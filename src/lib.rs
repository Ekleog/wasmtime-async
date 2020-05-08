//! # wasmtime-async
//!
//! This crate is an extension to the
//! [`wasmtime`](https://github.com/bytecodealliance/wasmtime/blob/master/README.md)
//! crate. It makes it possible to use wasmtime along with futures,
//! without having to consider every WebAssembly call as blocking. Note
//! however that it is designed only for cases where the time spent in
//! WebAssembly is indeed not enough to warrant running it in a worker
//! thread -- it is designed with, in mind, relatively lightweight
//! WebAssembly code that then calls into async callbacks provided from
//! the rust side.
//!
//! The WebAssembly code will be run on a specific stack and, when it
//! calls an async callback provided by rust, will be interrupted until
//! the future has returned. As such, so long as the time spent inside
//! WebAssembly is not enough to warrant in itself running the whole task
//! on a blocking executor, it should be possible to run WebAssembly code
//! that integrates seamlessly with async code.
//!
//! The drawback of this approach is that the async callbacks appear as
//! though they were blocking to WebAssembly. This is unfortunately
//! necessary to not require the WebAssembly code itself to be
//! async-ready.
//!
//! # Usage
//!
//! This crate provides two main elements:
//! - The [`Stack`] struct, that owns a stack on which WebAssembly code
//!   can run
//! - The [`FuncExt`] trait, that provides extension methods for
//!   [`wasmtime::Func`] for dealing with asynchronous callbacks provided
//!   by Rust to WebAssembly.
//!
//! ## [`Stack`]
//!
//! The [`Stack`] struct is easy to use: just use [`Stack::new`], and it
//! will create a stack on which WebAssembly code can run.
//!
//! Running code on a [`Stack`] takes a mutable reference to it so long as
//! the code is running, thus preventing multiple functions from using the
//! same stack without any runtime cost or unsafe usage.
//!
//! ## [`FuncExt`]
//!
//! The [`FuncExt`] provides most of the interesting methods in this crate.
//!
//! ### Wrapping async functions for use from WebAssembly
//!
//! First, use the methods to wrap async functions in Rust so that they
//! could be used transparently from WebAssembly:
//!
//! - [`FuncExt::new_async`], corresponding to [`wasmtime::Func::new`]
//! - [`FuncExt::wrap_async`], corresponding to [`wasmtime::Func::wrap`]
//!   with callbacks that do not take a [`wasmtime::Caller`] as first
//!   argument
//! - [`FuncExt::wrap_async0`] to [`FuncExt::wrap_async15`], corresponding
//!   to [`wasmtime::Func::wrap`] with callbacks that do take a
//!   [`wasmtime::Caller`] as first argument
//!
//! It would be better to have a single [`FuncExt::wrap_async`] function,
//! but unfortunately, due to both orphan rules and [a probable limitation
//! of rustc](https://github.com/rust-lang/rust/issues/71852), it is not
//! possible to do so at the moment, hence the multiple methods that
//! handle each part of [`Func::wrap`].
//!
//! ### Calling WebAssembly that uses async functions
//!
//! When calling into WebAssembly code that potentially uses async
//! functions, you **must** use an async-ready calling function, or a
//! panic will arise!
//!
//! The functions are these:
//!
//! - [`FuncExt::call_async`], corresponding to [`wasmtime::Func::call`]
//! - [`FuncExt::get_async`], which returns an [`AsyncGetter`] object. The
//!   [`AsyncGetter`] object is just here to circumvent limitations in the
//!   Rust type system, and in particular associated existential types. On
//!   [`AsyncGetter`], you can call the [`AsyncGetter::get0`] to
//!   [`AsyncGetter::get15`] functions just like you would have called
//!   them on [`wasmtime::Func`].

// TODO: use #![doc(include)] once it's stable

use std::cell::Cell;
use std::future::Future;
use std::marker::PhantomData;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{self, Poll};
use std::thread;

use wasmtime::{Caller, Func, FuncType, Store, Trap, Val, WasmRet, WasmTy};

/// A stack on which to run WebAssembly code
#[repr(transparent)]
pub struct Stack {
    pub(crate) s: context::stack::ProtectedFixedSizeStack,
}

impl Stack {
    /// Create a stack that can allow at least the given `size`
    pub fn new(size: usize) -> anyhow::Result<Stack> {
        let s = context::stack::ProtectedFixedSizeStack::new(size)?;
        Ok(Stack { s })
    }
}

/// A “prelude” for users of the `wasmtime-async` crate.
pub mod prelude {
    pub use super::FuncExt;
}

thread_local! {
    static TRANSFER: Cell<Option<context::Transfer>> = Cell::new(None);
}

macro_rules! def_wrap {
    ($name:ident $(, $args:ident)*) => {
        /// Wrap asynchronous functions that take a [`Caller`] as
        /// their first argument.
        ///
        /// See also [`wasmtime::Func::wrap`] for more details.
        ///
        /// Running WebAssembly code that could call into a function
        /// defined like this *must* be done with one of the
        /// async-ready ways of calling it, or it will panic.
        fn $name<F, $($args,)* R>(store: &Store, func: F) -> Func
        where
            F: 'static + for<'a> Fn(Caller<'a> $(, $args)*) -> Box<dyn 'a + Future<Output = R>>,
            $($args: WasmTy,)*
            R: WasmRet;
    };
}

/// The extension trait to [`wasmtime::Func`], that holds most of the
/// interest of this crate.
#[rustfmt::skip::macros(def_wrap)]
pub trait FuncExt {
    /// Wrap an asynchronous function like [`wasmtime::Func::new`]
    /// would have done.
    ///
    /// See also [`wasmtime::Func::new`] for more details.
    ///
    /// Running WebAssembly code that could call into a function
    /// defined like this *must* be done with one of the async-ready
    /// ways of calling it, or it will panic.
    // TODO: when it's possible, return impl Trait
    fn new_async<F>(store: &Store, ty: FuncType, func: F) -> Func
    where
        F: 'static
            + for<'a> Fn(
                Caller<'a>,
                &'a [Val],
                &'a mut [Val],
            ) -> Box<dyn 'a + Future<Output = Result<(), Trap>>>;

    /// Wrap an asynchronous function that does not take a [`Caller`]
    /// as its first argument.
    ///
    /// See also [`wasmtime::Func::wrap`] for more details.
    ///
    /// Running WebAssembly code that could call into a function
    /// defined like this *must* be done with one of the async-ready
    /// ways of calling it, or it will panic.
    fn wrap_async<Params, Results, F>(store: &Store, func: F) -> Func
    where
        F: IntoFuncAsync<Params, Results>;

    def_wrap!(wrap_async0);
    def_wrap!(wrap_async1, A1);
    def_wrap!(wrap_async2, A1, A2);
    def_wrap!(wrap_async3, A1, A2, A3);
    def_wrap!(wrap_async4, A1, A2, A3, A4);
    def_wrap!(wrap_async5, A1, A2, A3, A4, A5);
    def_wrap!(wrap_async6, A1, A2, A3, A4, A5, A6);
    def_wrap!(wrap_async7, A1, A2, A3, A4, A5, A6, A7);
    def_wrap!(wrap_async8, A1, A2, A3, A4, A5, A6, A7, A8);
    def_wrap!(wrap_async9, A1, A2, A3, A4, A5, A6, A7, A8, A9);
    def_wrap!(wrap_async10, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10);
    def_wrap!(wrap_async11, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11);
    def_wrap!(wrap_async12, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12);
    def_wrap!(wrap_async13, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13);
    def_wrap!(wrap_async14, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14);
    def_wrap!(wrap_async15, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15);

    /// Call this function in an async-ready way. This makes it
    /// possible to run functions that have been built by the helper
    /// methods provided by this crate.
    ///
    /// See also [`wasmtime::Func::call`] for more details.
    // TODO: When it's possible, return:
    // impl 'a + Future<Output = anyhow::Result<Box<[Val]>>>
    fn call_async<'a>(
        &self,
        stack: &'a mut Stack,
        params: &'a [Val],
    ) -> WasmFuture<'a, anyhow::Result<Box<[Val]>>>;

    /// Helper to retrieve WebAssembly functions in a way that could
    /// be called directly from Rust, without having to marshal
    /// arguments and return values.
    ///
    /// This will usually be immediately followed by one of the
    /// methods on [`AsyncGetter`].
    ///
    /// This is a helper method designed to work around current Rust
    /// typesystem limitations, ie. lack of associated existential
    /// types.
    fn get_async<'a>(&'a self) -> AsyncGetter<'a>;
}

macro_rules! make_wrap {
    ($name:ident $(, $args:ident)*) => {
        fn $name<F, $($args,)* R>(store: &Store, func: F) -> Func
        where
            F: 'static + for<'a> Fn(Caller<'a> $(, $args)*) -> Box<dyn 'a + Future<Output = R>>,
            $($args: WasmTy,)*
            R: WasmRet,
        {
            #[allow(non_snake_case)]
            let func = move |caller: Caller<'_>, $($args: $args),*| -> R {
                // See comments on `new_async` for the safety of context transfers
                let mut transfer = TRANSFER.with(|t| t.replace(None).unwrap());
                // The below unsafe could be avoided with
                // Box::into_pin when it gets stabilized. We will
                // be able to remove the box altogether once [1]
                // will get fixed
                // [1] https://github.com/rust-lang/rust/issues/70263
                let mut fut = unsafe { Pin::new_unchecked(func(caller, $($args),*)) };
                loop {
                    let ctx = unsafe { &mut *(transfer.data as *mut task::Context) };
                    match fut.as_mut().poll(ctx) {
                        Poll::Pending => {
                            transfer = unsafe { transfer.context.resume(0) };
                        }
                        Poll::Ready(r) => {
                            TRANSFER.with(|t| debug_assert!(t.replace(Some(transfer)).is_none()));
                            return r;
                        }
                    }
                }
            };
            Func::wrap(store, func)
        }
    };
}

#[rustfmt::skip::macros(make_wrap)]
impl FuncExt for Func {
    fn new_async<F>(store: &Store, ty: FuncType, func: F) -> Func
    where
        F: 'static
            + for<'a> Fn(
                Caller<'a>,
                &'a [Val],
                &'a mut [Val],
            ) -> Box<dyn 'a + Future<Output = Result<(), Trap>>>,
    {
        let func =
            move |caller: Caller<'_>, params: &[Val], returns: &mut [Val]| -> Result<(), Trap> {
                // The below unwrap can only panic if the function is
                // called outside any `call` or function returned by
                // `get*`, which should not possibly happen.
                let mut transfer = TRANSFER.with(|t| t.replace(None).unwrap());
                // This below unsafe could be avoided with Box::into_pin
                // when it gets stabilized. We will be able to remove the
                // box altogether once [1] will get fixed
                // [1] https://github.com/rust-lang/rust/issues/70263
                let mut fut = unsafe { Pin::new_unchecked(func(caller, params, returns)) };
                loop {
                    // This is safe thanks to being run only from `call`
                    // or `get*`, which we know will make sure to pass the
                    // context in the data
                    let ctx = unsafe { &mut *(transfer.data as *mut task::Context) };
                    match fut.as_mut().poll(ctx) {
                        Poll::Pending => {
                            transfer = unsafe { transfer.context.resume(0) };
                        }
                        Poll::Ready(r) => {
                            TRANSFER.with(|t| debug_assert!(t.replace(Some(transfer)).is_none()));
                            return r;
                        }
                    }
                }
            };
        Func::new(store, ty, func)
    }

    fn wrap_async<Params, Results, F>(store: &Store, func: F) -> Func
    where
        F: IntoFuncAsync<Params, Results>,
    {
        func.into_func_async(store)
    }

    make_wrap!(wrap_async0);
    make_wrap!(wrap_async1, A1);
    make_wrap!(wrap_async2, A1, A2);
    make_wrap!(wrap_async3, A1, A2, A3);
    make_wrap!(wrap_async4, A1, A2, A3, A4);
    make_wrap!(wrap_async5, A1, A2, A3, A4, A5);
    make_wrap!(wrap_async6, A1, A2, A3, A4, A5, A6);
    make_wrap!(wrap_async7, A1, A2, A3, A4, A5, A6, A7);
    make_wrap!(wrap_async8, A1, A2, A3, A4, A5, A6, A7, A8);
    make_wrap!(wrap_async9, A1, A2, A3, A4, A5, A6, A7, A8, A9);
    make_wrap!(wrap_async10, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10);
    make_wrap!(wrap_async11, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11);
    make_wrap!(wrap_async12, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12);
    make_wrap!(wrap_async13, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13);
    make_wrap!(wrap_async14, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14);
    make_wrap!(wrap_async15, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15);

    fn call_async<'a>(
        &self,
        stack: &'a mut Stack,
        params: &'a [Val],
    ) -> WasmFuture<'a, anyhow::Result<Box<[Val]>>> {
        extern "C" fn context_fn(mut transfer: context::Transfer) -> ! {
            let res: thread::Result<anyhow::Result<Box<[Val]>>> = std::panic::catch_unwind(|| {
                // This is safe thanks to the `resume` just below this
                // function's definition
                let (f, params) = unsafe { &*(transfer.data as *const (Func, &[Val])) }.clone();
                transfer = unsafe { transfer.context.resume(0) };
                TRANSFER.with(|t| debug_assert!(t.replace(Some(transfer)).is_none()));
                let res = f.call(params);
                res
            });
            // TODO: make sure this unwrap can't panic
            let transfer = TRANSFER.with(|t| t.replace(None).unwrap());
            unsafe { transfer.context.resume(&res as *const _ as usize) };
            // We're not allowed to panic from here anyway, so there's
            // little better than unreachable_unchecked even with
            // defensive programming in mind
            unsafe { std::hint::unreachable_unchecked() }
        }
        // We know `stack.s` is owned by ourselves, thanks to us
        // taking an `&'a mut Stack` for as long as the stack is used
        let ctx = unsafe { context::Context::new(&stack.s, context_fn) };
        let arg: (Func, &[Val]) = (self.clone(), params);
        let transfer = unsafe { ctx.resume(&arg as *const _ as usize) };
        debug_assert!(transfer.data == 0);
        WasmFuture {
            ctx: Some(transfer.context),
            phantom: PhantomData,
        }
    }

    fn get_async<'a>(&'a self) -> AsyncGetter<'a> {
        AsyncGetter { f: self }
    }
}

/// Helper struct for retrieving native functions out of WebAssembly
/// functions that call async callbacks.
pub struct AsyncGetter<'f> {
    f: &'f Func,
}

macro_rules! implement_getter {
    ($name:ident $(, $args:ident)*) => {
        /// Retrieve a Rust-native function that calls this function
        /// in an async-ready way. This makes it possible to run
        /// functions that have been built by the helper methods
        /// provided by this crate.
        ///
        /// See also [`wasmtime::Func::call`] for more details.
        pub fn $name<$($args,)* R>(
            &self
        ) -> anyhow::Result<Box<dyn 'static + for<'s> Fn(&'s mut Stack, $($args),*) -> WasmFuture<'s, Result<R, Trap>>>>
        where
            // 'static bounds are free as all T: WasmTy are 'static anyway
            $($args: 'static + WasmTy,)*
            R: 'static + WasmTy,
        {
            // See the comments in `call_async` for why the unsafe
            // blocks should be safe
            #[allow(non_snake_case)]
            extern "C" fn context_fn<F, $($args,)* R>(mut transfer: context::Transfer) -> !
            where
                F: Fn($($args,)*) -> Result<R, Trap>,
                $($args: WasmTy,)*
                R: WasmTy,
            {
                let res: thread::Result<Result<R, Trap>> = std::panic::catch_unwind(|| {
                    let (f, $($args),*) = unsafe { &*(transfer.data as *const (Rc<F>, $($args),*)) }.clone();
                    transfer = unsafe { transfer.context.resume(0) };
                    TRANSFER.with(|t| debug_assert!(t.replace(Some(transfer)).is_none()));
                    let res = f($($args),*);
                    res
                });
                // TODO: make sure this unwrap can't unwind
                let transfer = TRANSFER.with(|t| t.replace(None).unwrap());
                unsafe { transfer.context.resume(&res as *const _ as usize); }
                unsafe { std::hint::unreachable_unchecked() }
            }
            fn typed_context_fn<F, $($args,)* R>(_: &Rc<F>) -> extern "C" fn(context::Transfer) -> !
            where
                F: Fn($($args,)*) -> Result<R, Trap>,
                $($args: WasmTy,)*
                R: WasmTy,
            {
                context_fn::<F, $($args,)* R>
            }
            // We have to use `Rc` so that the returned future can also keep `f` alive
            let f = Rc::new(self.f.$name::<$($args,)* R>()?);
            #[allow(non_snake_case)]
            Ok(Box::new(move |stack: &mut Stack, $($args: $args,)*| -> WasmFuture<'_, Result<R, Trap>> {
                let ctx = unsafe { context::Context::new(&stack.s, typed_context_fn(&f)) };
                let arg: (_, $($args),*) = (f.clone(), $($args),*);
                let transfer = unsafe { ctx.resume(&arg as *const _ as usize) };
                debug_assert!(transfer.data == 0);
                WasmFuture {
                    ctx: Some(transfer.context),
                    phantom: PhantomData,
                }
            }))
        }
    };
}

impl<'f> AsyncGetter<'f> {
    implement_getter!(get0);
    implement_getter!(get1, A1);
    implement_getter!(get2, A1, A2);
    implement_getter!(get3, A1, A2, A3);
    implement_getter!(get4, A1, A2, A3, A4);
    implement_getter!(get5, A1, A2, A3, A4, A5);
    implement_getter!(get6, A1, A2, A3, A4, A5, A6);
    implement_getter!(get7, A1, A2, A3, A4, A5, A6, A7);
    implement_getter!(get8, A1, A2, A3, A4, A5, A6, A7, A8);
    implement_getter!(get9, A1, A2, A3, A4, A5, A6, A7, A8, A9);
    implement_getter!(get10, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10);
    implement_getter!(get11, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11);
    implement_getter!(get12, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12);
    implement_getter!(get13, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13);
    implement_getter!(get14, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14);
    implement_getter!(get15, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15);
}

/// Internal trait implemented for all arguments that can be passed to
/// [`FuncExt::wrap_async`].
///
/// This trait should not be implemented by external users, it's only
/// intended as an implementation detail of this crate.
pub trait IntoFuncAsync<Params, Results> {
    #[doc(hidden)]
    fn into_func_async(self, store: &Store) -> Func;
}

macro_rules! impl_into_func {
    ($($args: ident),*) => {
        impl<F, $($args,)* R, RetFut> IntoFuncAsync<($($args,)*), R> for F
        where
            F: 'static + Fn($($args),*) -> RetFut,
            $($args: WasmTy,)*
            RetFut: Future<Output = R>,
            R: WasmRet,
        {
            fn into_func_async(self, store: &Store) -> Func {
                #[allow(non_snake_case)]
                let func = move |$($args: $args,)*| -> R {
                    // See comments on `new_async` for the safety of context transfer
                    let mut transfer = TRANSFER.with(|t| t.replace(None).unwrap());
                    let fut = self($($args),*);
                    pin_utils::pin_mut!(fut);
                    loop {
                        let ctx = unsafe { &mut *(transfer.data as *mut task::Context) };
                        match fut.as_mut().poll(ctx) {
                            Poll::Pending => {
                                transfer = unsafe { transfer.context.resume(0) };
                            }
                            Poll::Ready(r) => {
                                TRANSFER.with(|t| debug_assert!(t.replace(Some(transfer)).is_none()));
                                return r;
                            }
                        }
                    }
                };
                Func::wrap(store, func)
            }
        }
    };
}

impl_into_func!();
impl_into_func!(A1);
impl_into_func!(A1, A2);
impl_into_func!(A1, A2, A3);
impl_into_func!(A1, A2, A3, A4);
impl_into_func!(A1, A2, A3, A4, A5);
impl_into_func!(A1, A2, A3, A4, A5, A6);
impl_into_func!(A1, A2, A3, A4, A5, A6, A7);
impl_into_func!(A1, A2, A3, A4, A5, A6, A7, A8);
impl_into_func!(A1, A2, A3, A4, A5, A6, A7, A8, A9);
impl_into_func!(A1, A2, A3, A4, A5, A6, A7, A8, A9, A10);
impl_into_func!(A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11);
impl_into_func!(A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12);
impl_into_func!(A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13);
impl_into_func!(A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14);
impl_into_func!(A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15);

/// Future that runs WebAssembly code to completion, when the
/// WebAssembly potentially includes async callback calls.
///
/// This struct should not be depended upon for anything other than it
/// being `impl Future`. It will be removed once associated
/// existential traits will exist, to be replaced by direct `impl
/// Future` returns.
pub struct WasmFuture<'a, Ret> {
    ctx: Option<context::Context>,
    // The first phantom keeps alive the stack and parameters that ought to be.
    // The second phantom states that Ret is being generated by WasmFuture.
    phantom: PhantomData<(&'a mut (), fn() -> Ret)>,
}

impl<'a, Ret> Future for WasmFuture<'a, Ret> {
    type Output = Ret;

    fn poll(self: Pin<&mut Self>, ctx: &mut task::Context) -> Poll<Self::Output> {
        let this = self.get_mut();
        let transfer = unsafe {
            this.ctx
                .take()
                .unwrap()
                .resume(ctx as *mut task::Context as usize)
        };
        if transfer.data == 0 {
            this.ctx = Some(transfer.context);
            // We know that every `resume(0)` that could happen here
            // (ie. apart from the one acknowledging the parameters)
            // was necessarily done in answer to a `Poll::Pending`,
            // thus meaning that the waker is already registered
            Poll::Pending
        } else {
            let res = unsafe { std::ptr::read(transfer.data as *const thread::Result<Ret>) };
            match res {
                Ok(r) => Poll::Ready(r),
                Err(e) => std::panic::resume_unwind(e),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::time::Duration;

    use futures::executor;
    use wasmtime::ValType;

    #[test]
    fn new_async_then_call() {
        let store = Store::default();
        let double_type = FuncType::new(Box::new([ValType::I32]), Box::new([ValType::I32]));
        let double = Func::new_async(&store, double_type, move |_, params, results| {
            Box::new(async move {
                let mut value = params[0].unwrap_i32();
                value *= 2;
                results[0] = value.into();
                futures_timer::Delay::new(Duration::from_millis(1)).await;
                Ok(())
            })
        });
        let mut stack = Stack::new(16 * 4096).unwrap();
        let params = &[Val::from(5i32)];
        assert_eq!(
            executor::block_on(double.call_async(&mut stack, params)).unwrap()[0].unwrap_i32(),
            10i32
        );
    }

    #[test]
    fn wrap_async_then_get() {
        let store = Store::default();
        let double = Func::wrap_async(&store, |x: i32| async move {
            let res = 2 * x;
            futures_timer::Delay::new(Duration::from_millis(1)).await;
            res
        });
        let mut stack = Stack::new(16 * 4096).unwrap();
        let f = double.get_async().get1::<i32, i32>().unwrap();
        assert_eq!(executor::block_on(f(&mut stack, 21)).unwrap(), 42);
    }

    #[test]
    fn wrap_async_with_caller_then_get() {
        let store = Store::default();
        let add = Func::wrap_async2(&store, |caller: Caller, x: i32, y: i64| {
            Box::new(async move {
                let res = x as i64 + y;
                futures_timer::Delay::new(Duration::from_millis(1)).await;
                assert!(caller.get_export("foo").is_none());
                res
            })
        });
        let mut stack = Stack::new(16 * 4096).unwrap();
        let f = add.get_async().get2::<i32, i64, i64>().unwrap();
        assert_eq!(executor::block_on(f(&mut stack, 1, 2)).unwrap(), 3);
    }
}
