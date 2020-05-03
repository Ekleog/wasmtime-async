use crate::*;

#[repr(transparent)]
pub struct Caller<'a> {
    caller: wasmtime::Caller<'a>,
}

impl<'a> Caller<'a> {
    pub(crate) fn from_wasm(caller: wasmtime::Caller<'a>) -> Caller<'a> {
        Caller { caller }
    }

    pub fn get_export(&self, name: &str) -> Option<Extern> {
        self.caller.get_export(name).map(Extern::from_wasm)
    }
}
