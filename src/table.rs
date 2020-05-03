use crate::*;

#[derive(Clone)]
#[repr(transparent)]
pub struct Table {
    t: wasmtime::Table,
}

impl Table {
    pub(crate) fn from_wasm(t: wasmtime::Table) -> Table {
        Table { t }
    }

    pub(crate) fn into_wasm(self) -> wasmtime::Table {
        self.t
    }

    pub fn new(
        store: &wasmtime::Store,
        ty: wasmtime::TableType,
        init: Val,
    ) -> anyhow::Result<Table> {
        let t = wasmtime::Table::new(store, ty, init.into_wasm())?;
        Ok(Table { t })
    }

    pub fn ty(&self) -> wasmtime::TableType {
        self.t.ty()
    }

    pub fn get(&self, index: u32) -> Option<Val> {
        self.t.get(index).map(Val::from_wasm)
    }

    pub fn set(&self, index: u32, val: Val) -> anyhow::Result<()> {
        self.t.set(index, val.into_wasm())
    }

    pub fn size(&self) -> u32 {
        self.t.size()
    }

    pub fn grow(&self, delta: u32, init: Val) -> anyhow::Result<u32> {
        self.t.grow(delta, init.into_wasm())
    }

    pub fn copy(
        dst_table: &Table,
        dst_index: u32,
        src_table: &Table,
        src_index: u32,
        len: u32,
    ) -> anyhow::Result<()> {
        wasmtime::Table::copy(&dst_table.t, dst_index, &src_table.t, src_index, len)
    }
}
