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
