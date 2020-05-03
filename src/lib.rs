// Note to the reader: most of the interesting logic is in the `func` and `stack` modules.

mod caller;
mod export;
mod extern_;
mod func;
mod global;
mod instance;
mod stack;
mod table;
mod val;

pub use caller::Caller;
pub use export::Export;
pub use extern_::Extern;
pub use func::{Func, IntoFunc};
pub use global::Global;
pub use instance::Instance;
pub use stack::Stack;
pub use table::Table;
pub use val::Val;
