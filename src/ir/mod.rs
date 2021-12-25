pub mod core;
pub mod instructions;
pub mod structs;
pub mod types;
pub mod values;

mod idman;

pub use self::core::{Value, ValueKind, ValueRc};
pub use structs::{BasicBlock, BasicBlockRc, Function, FunctionRc, Program};
pub use types::{Type, TypeKind};
