use crate::*;

#[derive(Clone)]
#[repr(transparent)]
pub struct Extern {
    ext: wasmtime::Extern,
}

impl Extern {
    pub(crate) fn from_wasm(ext: wasmtime::Extern) -> Extern {
        Extern { ext }
    }

    pub(crate) fn into_wasm_slice(s: &[Extern]) -> &[wasmtime::Extern] {
        // This is OK thanks to the repr(transparent)
        unsafe { std::mem::transmute(s) }
    }

    pub fn into_func(self) -> Option<Func> {
        self.ext.into_func().map(Func::from_wasm)
    }

    pub fn into_global(self) -> Option<Global> {
        self.ext.into_global().map(Global::from_wasm)
    }

    pub fn into_table(self) -> Option<Table> {
        self.ext.into_table().map(Table::from_wasm)
    }

    pub fn into_memory(self) -> Option<wasmtime::Memory> {
        self.ext.into_memory()
    }

    pub fn ty(&self) -> wasmtime::ExternType {
        self.ext.ty()
    }
}

impl From<Func> for Extern {
    fn from(f: Func) -> Extern {
        Extern::from_wasm(wasmtime::Extern::from(f.into_wasm()))
    }
}

impl From<Global> for Extern {
    fn from(g: Global) -> Extern {
        Extern::from_wasm(wasmtime::Extern::from(g.into_wasm()))
    }
}

impl From<wasmtime::Memory> for Extern {
    fn from(m: wasmtime::Memory) -> Extern {
        Extern::from_wasm(wasmtime::Extern::from(m))
    }
}

impl From<Table> for Extern {
    fn from(t: Table) -> Extern {
        Extern::from_wasm(wasmtime::Extern::from(t.into_wasm()))
    }
}
