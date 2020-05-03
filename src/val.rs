use crate::*;

#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Val {
    v: wasmtime::Val,
}

macro_rules! delegate {
    ($(($name:ident, $type:ty),)*) => {
        $(
            pub fn $name(&self) -> $type {
                self.v.$name()
            }
        )*
    };
}

impl Val {
    pub(crate) fn from_wasm(v: wasmtime::Val) -> Val {
        Val { v }
    }

    pub(crate) fn into_wasm(self) -> wasmtime::Val {
        self.v
    }

    pub(crate) fn from_wasm_slice(s: &[wasmtime::Val]) -> &[Val] {
        // This is OK thanks to repr(transparent)
        unsafe { std::mem::transmute(s) }
    }

    pub(crate) fn from_wasm_slice_mut(s: &mut [wasmtime::Val]) -> &mut [Val] {
        // This is OK thanks to repr(transparent)
        unsafe { std::mem::transmute(s) }
    }

    pub(crate) fn into_wasm_slice(s: &[Val]) -> &[wasmtime::Val] {
        // This is OK thanks to repr(transparent)
        unsafe { std::mem::transmute(s) }
    }

    pub(crate) fn from_wasm_boxed_slice(b: Box<[wasmtime::Val]>) -> Box<[Val]> {
        // This is OK thanks to repr(transparent)
        unsafe { std::mem::transmute(b) }
    }

    pub fn null() -> Val {
        Val::from_wasm(wasmtime::Val::null())
    }

    delegate! {
        (ty, wasmtime::ValType),
        (i32, Option<i32>),
        (unwrap_i32, i32),
        (i64, Option<i64>),
        (unwrap_i64, i64),
        (f32, Option<f32>),
        (unwrap_f32, f32),
        (anyref, Option<wasmtime::AnyRef>),
        (unwrap_anyref, wasmtime::AnyRef),
        (v128, Option<u128>),
        (unwrap_v128, u128),
    }

    pub fn funcref(&self) -> Option<&Func> {
        self.v.funcref().map(Func::from_wasm_ref)
    }

    pub fn unwrap_funcref(&self) -> &Func {
        Func::from_wasm_ref(self.v.unwrap_funcref())
    }
}

macro_rules! from_impl {
    ($type:ty) => {
        impl From<$type> for Val {
            fn from(v: $type) -> Val {
                Val::from_wasm(wasmtime::Val::from(v))
            }
        }
    };
}

from_impl!(wasmtime::AnyRef);
from_impl!(f32);
from_impl!(f64);
from_impl!(i32);
from_impl!(i64);

impl From<Func> for Val {
    fn from(v: Func) -> Val {
        Val::from_wasm(wasmtime::Val::from(v.into_wasm()))
    }
}
