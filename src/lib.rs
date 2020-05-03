use std::cell::Cell;
use std::future::Future;
use std::marker::PhantomData;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{self, Poll};
use std::thread;

use wasmtime::{Caller, Func, FuncType, Store, Trap, Val, WasmRet, WasmTy};

#[repr(transparent)]
pub struct Stack {
    pub(crate) s: context::stack::ProtectedFixedSizeStack,
}

impl Stack {
    pub fn new(size: usize) -> anyhow::Result<Stack> {
        let s = context::stack::ProtectedFixedSizeStack::new(size)?;
        Ok(Stack { s })
    }
}

thread_local! {
    static TRANSFER: Cell<Option<context::Transfer>> = Cell::new(None);
}

pub trait FuncExt {
    // TODO: when it's possible, return impl Trait
    fn new_async<F>(store: &Store, ty: FuncType, func: F) -> Func
    where
        F: 'static
            + for<'a> Fn(
                Caller<'a>,
                &'a [Val],
                &'a mut [Val],
            ) -> Box<dyn 'a + Future<Output = Result<(), Trap>>>;

    fn wrap_async<Params, Results, F>(store: &Store, func: F) -> Func
    where
        F: IntoFuncAsync<Params, Results>;

    // TODO: orphan rules force having two methods :(
    fn wrap_async_with_caller<Params, Results, F>(store: &Store, func: F) -> Func
    where
        F: IntoFuncAsyncWithCaller<Params, Results>;

    // TODO: When it's possible, return:
    // impl 'a + Future<Output = anyhow::Result<Box<[Val]>>>
    fn call_async<'a>(
        &self,
        stack: &'a mut Stack,
        params: &'a [Val],
    ) -> WasmFuture<'a, anyhow::Result<Box<[Val]>>>;

    fn get_async<'a>(&'a self) -> AsyncGetter<'a>;
}

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

    fn wrap_async_with_caller<Params, Results, F>(store: &Store, func: F) -> Func
    where
        F: IntoFuncAsyncWithCaller<Params, Results>,
    {
        func.into_func_async_with_caller(store)
    }

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

pub struct AsyncGetter<'f> {
    f: &'f Func,
}

macro_rules! implement_getter {
    ($name:ident $(, $args:ident)*) => {
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

pub trait IntoFuncAsync<Params, Results> {
    #[doc(hidden)]
    fn into_func_async(self, store: &Store) -> Func;
}

pub trait IntoFuncAsyncWithCaller<Params, Results> {
    #[doc(hidden)]
    fn into_func_async_with_caller(self, store: &Store) -> Func;
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

        impl<F, $($args,)* R> IntoFuncAsyncWithCaller<(Caller<'_>, $($args),*), R> for F
        where
            F: 'static + for<'a> Fn(
                Caller<'a> $(, $args)*
            ) -> Box<dyn 'a + Future<Output = R>>,
            $($args: WasmTy,)*
            R: WasmRet,
        {
            fn into_func_async_with_caller(self, store: &Store) -> Func {
                #[allow(non_snake_case)]
                let func = move |caller: Caller<'_>, $($args: $args),*| -> R {
                    // See comments on `new_async` for the safety of context transfers
                    let mut transfer = TRANSFER.with(|t| t.replace(None).unwrap());
                    // The below unsafe could be avoided with
                    // Box::into_pin when it gets stabilized. We will
                    // be able to remove the box altogether once [1]
                    // will get fixed
                    // [1] https://github.com/rust-lang/rust/issues/70263
                    let mut fut = unsafe { Pin::new_unchecked(self(caller, $($args),*)) };
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
        // TODO: this should not be required
        fn check_type<F, A1, A2, R>(f: F) -> F
        where
            F: 'static + for<'a> Fn(Caller<'a>, A1, A2) -> Box<dyn 'a + Future<Output = R>>,
            A1: WasmTy,
            A2: WasmTy,
            R: WasmRet,
        {
            f
        }
        let add = Func::wrap_async_with_caller(
            &store,
            check_type(|caller: Caller, x: i32, y: i64| {
                Box::new(async move {
                    let res = x as i64 + y;
                    futures_timer::Delay::new(Duration::from_millis(1)).await;
                    assert!(caller.get_export("foo").is_none());
                    res
                })
            }),
        );
        let mut stack = Stack::new(16 * 4096).unwrap();
        let f = add.get_async().get2::<i32, i64, i64>().unwrap();
        assert_eq!(executor::block_on(f(&mut stack, 1, 2)).unwrap(), 3);
    }
}
