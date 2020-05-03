use crate::*;

use std::cell::Cell;
use std::future::Future;
use std::pin::Pin;
use std::task::{self, Poll};
use std::thread;

thread_local! {
    static TRANSFER: Cell<Option<context::Transfer>> = Cell::new(None);
}

type FinalResult<T> = thread::Result<anyhow::Result<T>>;

#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Func {
    f: wasmtime::Func,
}

impl Func {
    pub(crate) fn from_wasm(f: wasmtime::Func) -> Func {
        Func { f }
    }

    pub(crate) fn into_wasm(self) -> wasmtime::Func {
        self.f
    }

    pub(crate) fn from_wasm_ref(f: &wasmtime::Func) -> &Func {
        // This is OK thanks to repr(transparent)
        unsafe { std::mem::transmute(f) }
    }

    pub fn new<F>(store: &wasmtime::Store, ty: wasmtime::FuncType, func: F) -> Func
    where
        F: 'static
            + Fn(
                wasmtime::Caller<'_>,
                &[wasmtime::Val],
                &mut [wasmtime::Val],
            ) -> Result<(), wasmtime::Trap>,
    {
        Func::from_wasm(wasmtime::Func::new(store, ty, func))
    }

    pub fn new_async<F>(store: &wasmtime::Store, ty: wasmtime::FuncType, func: F) -> Func
    where
        F: 'static
            + for<'a> Fn(
                Caller<'a>,
                &'a [Val],
                &'a mut [Val],
            ) -> Box<dyn 'a + Future<Output = Result<(), wasmtime::Trap>>>,
    {
        let func = move |caller: wasmtime::Caller<'_>,
                         params: &[wasmtime::Val],
                         returns: &mut [wasmtime::Val]|
              -> Result<(), wasmtime::Trap> {
            // The below unwrap can only panic if the function is
            // called outside any `call` or function returned by
            // `get*`, which should not possibly happen.
            let mut transfer = TRANSFER.with(|t| t.replace(None).unwrap());
            let caller = Caller::from_wasm(caller);
            let params = Val::from_wasm_slice(params);
            let returns = Val::from_wasm_slice_mut(returns);
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
        let f = wasmtime::Func::new(store, ty, func);
        Func { f }
    }

    pub fn wrap<Params, Results, F>(store: &wasmtime::Store, func: F) -> Func
    where
        F: IntoFunc<Params, Results>,
    {
        func.into_func(store)
    }

    pub fn ty(&self) -> wasmtime::FuncType {
        self.f.ty()
    }

    pub fn param_arity(&self) -> usize {
        self.f.param_arity()
    }

    pub fn result_arity(&self) -> usize {
        self.f.result_arity()
    }

    pub fn call<'a>(
        &self,
        stack: &'a mut Stack,
        params: &'a [Val],
    ) -> impl 'a + Future<Output = anyhow::Result<Box<[Val]>>> {
        extern "C" fn context_fn(mut transfer: context::Transfer) -> ! {
            let res = std::panic::catch_unwind(|| {
                // This is safe thanks to the `resume` just below this
                // function's definition
                let (f, params) =
                    unsafe { &*(transfer.data as *const (wasmtime::Func, &[wasmtime::Val])) }
                        .clone();
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
                    .resume(&res as *const FinalResult<Box<[wasmtime::Val]>> as usize)
            };
            // We're not allowed to panic from here anyway, so there's
            // little better than unreachable_unchecked even with
            // defensive programming in mind
            unsafe { std::hint::unreachable_unchecked() }
        }
        let ctx = unsafe { context::Context::new(&stack.s, context_fn) };
        let arg: (wasmtime::Func, &[wasmtime::Val]) =
            (self.f.clone(), Val::into_wasm_slice(params));
        let transfer = unsafe { ctx.resume(&arg as *const _ as usize) };
        debug_assert!(transfer.data == 0);
        ContextFut {
            ctx: Some(transfer.context),
        }
    }

    // TODO: get0 to get15 (-> macro)
}

pub trait IntoFunc<Params, Results> {
    #[doc(hidden)]
    fn into_func(self, store: &wasmtime::Store) -> Func;
}

macro_rules! impl_into_func {
    ($($args: ident),*) => {
        impl<F, $($args,)* R, RetFut> IntoFunc<($($args,)*), R> for F
        where
            F: 'static + Fn($($args),*) -> RetFut,
            $($args: wasmtime::WasmTy,)*
            RetFut: Future<Output = R>,
            R: wasmtime::WasmRet,
        {
            fn into_func(self, store: &wasmtime::Store) -> Func {
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
                Func::from_wasm(wasmtime::Func::wrap(store, func))
            }
        }

        impl<F, $($args,)* R> IntoFunc<(Caller<'_>, $($args),*), R> for F
        where
            F: 'static + for<'a> Fn(
                Caller<'a> $(, $args)*
            ) -> Box<dyn 'a + Future<Output = R>>,
            $($args: wasmtime::WasmTy,)*
            R: wasmtime::WasmRet,
        {
            fn into_func(self, store: &wasmtime::Store) -> Func {
                #[allow(non_snake_case)]
                let func = move |caller: wasmtime::Caller<'_>, $($args: $args),*| -> R {
                    // See comments on `new_async` for the safety of context transfers
                    let mut transfer = TRANSFER.with(|t| t.replace(None).unwrap());
                    // The below unsafe could be avoided with
                    // Box::into_pin when it gets stabilized. We will
                    // be able to remove the box altogether once [1]
                    // will get fixed
                    // [1] https://github.com/rust-lang/rust/issues/70263
                    let mut fut = unsafe { Pin::new_unchecked(self(Caller::from_wasm(caller), $($args),*)) };
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
                Func::from_wasm(wasmtime::Func::wrap(store, func))
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

// TODO: implement IntoFunc for as many variants as
// https://docs.rs/wasmtime/0.16.0/wasmtime/trait.IntoFunc.html

struct ContextFut {
    ctx: Option<context::Context>,
}

impl Future for ContextFut {
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
            let res = unsafe {
                std::ptr::read(transfer.data as *const FinalResult<Box<[wasmtime::Val]>>)
            };
            match res {
                Ok(r) => Poll::Ready(r.map(Val::from_wasm_boxed_slice)),
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

    #[test]
    fn new_async_then_call() {
        let store = wasmtime::Store::default();
        let double_type = wasmtime::FuncType::new(
            Box::new([wasmtime::ValType::I32]),
            Box::new([wasmtime::ValType::I32]),
        );
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
            executor::block_on(double.call(&mut stack, params)).unwrap()[0].unwrap_i32(),
            10i32
        );
    }

    // TODO: test into_func with and without Caller
}
