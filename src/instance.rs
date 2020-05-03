use crate::*;

#[derive(Clone)]
#[repr(transparent)]
pub struct Instance {
    inst: wasmtime::Instance,
}

impl Instance {
    pub fn new(module: &wasmtime::Module, imports: &[Extern]) -> anyhow::Result<Instance> {
        let inst = wasmtime::Instance::new(module, Extern::into_wasm_slice(imports))?;
        Ok(Instance { inst })
    }

    // TODO: Does the store's InterruptHandle need hooking? Probably not, but needs checking
    pub fn store(&self) -> &wasmtime::Store {
        self.inst.store()
    }

    pub fn exports<'instance>(
        &'instance self,
    ) -> impl 'instance + ExactSizeIterator<Item = Export<'instance>> {
        self.inst.exports().map(Export::from_wasm)
    }

    pub fn get_export(&self, name: &str) -> Option<Extern> {
        self.inst.get_export(name).map(Extern::from_wasm)
    }

    pub fn get_func(&self, name: &str) -> Option<Func> {
        self.inst.get_func(name).map(Func::from_wasm)
    }

    pub fn get_table(&self, name: &str) -> Option<Table> {
        self.inst.get_table(name).map(Table::from_wasm)
    }

    pub fn get_memory(&self, name: &str) -> Option<wasmtime::Memory> {
        self.inst.get_memory(name)
    }

    pub fn get_global(&self, name: &str) -> Option<Global> {
        self.inst.get_global(name).map(Global::from_wasm)
    }
}
