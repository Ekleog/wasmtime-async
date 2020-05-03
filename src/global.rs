use crate::*;

#[derive(Clone)]
#[repr(transparent)]
pub struct Global {
    glob: wasmtime::Global,
}

impl Global {
    pub(crate) fn from_wasm(glob: wasmtime::Global) -> Global {
        Global { glob }
    }

    pub(crate) fn into_wasm(self) -> wasmtime::Global {
        self.glob
    }

    pub fn new(
        store: &wasmtime::Store,
        ty: wasmtime::GlobalType,
        val: Val,
    ) -> anyhow::Result<Global> {
        let glob = wasmtime::Global::new(store, ty, val.into_wasm())?;
        Ok(Global { glob })
    }

    pub fn ty(&self) -> wasmtime::GlobalType {
        self.glob.ty()
    }

    pub fn val_type(&self) -> wasmtime::ValType {
        self.glob.val_type()
    }

    pub fn mutability(&self) -> wasmtime::Mutability {
        self.glob.mutability()
    }

    pub fn get(&self) -> Val {
        Val::from_wasm(self.glob.get())
    }

    pub fn set(&self, val: Val) -> anyhow::Result<()> {
        self.glob.set(val.into_wasm())
    }
}
