use std::cell::Cell;
use std::future::Future;
use std::marker::PhantomData;
use std::pin::Pin;
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

type FinalResult<T> = thread::Result<anyhow::Result<T>>;

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

    // TODO: orphan rules force a different method :(
    fn wrap_async_with_caller<Params, Results, F>(store: &Store, func: F) -> Func
    where
        F: IntoFuncAsyncWithCaller<Params, Results>;

    // TODO: When it's possible, return:
    // impl 'a + Future<Output = anyhow::Result<Box<[Val]>>>
    fn call_async<'a>(&self, stack: &'a mut Stack, params: &'a [Val]) -> WasmFuture<'a>;
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

    fn call_async<'a>(&self, stack: &'a mut Stack, params: &'a [Val]) -> WasmFuture<'a> {
        extern "C" fn context_fn(mut transfer: context::Transfer) -> ! {
            let res = std::panic::catch_unwind(|| {
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
            unsafe {
                transfer
                    .context
                    .resume(&res as *const FinalResult<Box<[Val]>> as usize)
            };
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

    // TODO: get0 to get15 (-> macro)
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

pub struct WasmFuture<'a> {
    ctx: Option<context::Context>,
    phantom: PhantomData<&'a mut ()>, // Keeps alive the stack and parameters that ought to be
}

impl<'a> Future for WasmFuture<'a> {
    type Output = anyhow::Result<Box<[Val]>>;

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
            let res = unsafe { std::ptr::read(transfer.data as *const FinalResult<Box<[Val]>>) };
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

    // TODO: test into_func with and without Caller
}
