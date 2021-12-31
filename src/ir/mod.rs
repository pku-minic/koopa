pub mod builder;
pub mod dfg;
pub mod entities;
pub mod layout;
pub mod types;
pub mod values;

mod idman;

pub mod builder_traits {
  pub use super::builder::{BasicBlockBuilder, GlobalInstBuilder, LocalInstBuilder, ValueBuilder};
}

pub use entities::{BasicBlock, Function, FunctionData, Program, Value, ValueKind};
pub use types::{Type, TypeKind};
pub use values::BinaryOp;
