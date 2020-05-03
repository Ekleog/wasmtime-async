use crate::*;

#[derive(Clone)]
#[repr(transparent)]
pub struct Export<'instance> {
    exp: wasmtime::Export<'instance>,
}

impl<'instance> Export<'instance> {
    pub(crate) fn from_wasm(exp: wasmtime::Export<'instance>) -> Export<'instance> {
        Export { exp }
    }

    pub fn name(&self) -> &'instance str {
        self.exp.name()
    }

    pub fn ty(&self) -> wasmtime::ExternType {
        self.exp.ty()
    }

    pub fn into_extern(self) -> Extern {
        Extern::from_wasm(self.exp.into_extern())
    }

    pub fn into_func(self) -> Option<Func> {
        self.exp.into_func().map(Func::from_wasm)
    }

    pub fn into_table(self) -> Option<Table> {
        self.exp.into_table().map(Table::from_wasm)
    }

    pub fn into_memory(self) -> Option<wasmtime::Memory> {
        self.exp.into_memory()
    }

    pub fn into_global(self) -> Option<Global> {
        self.exp.into_global().map(Global::from_wasm)
    }
}
