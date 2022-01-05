//! The core part of Koopa IR.
//!
//! This module provides in-memory form IR related implementations,
//! containing:
//!
//! * Structs of Koopa IR programs ([`Program`]), functions ([`Function`],
//!   [`FunctionData`]), basic blocks ([`BasicBlock`], [`BasicBlockData`])
//!   and values ([`Value`], [`ValueData`]).
//! * Types of IR values ([`Type`]).
//! * IR builders and IR builder traits ([`builder`]).

pub mod builder;
pub mod dfg;
pub mod entities;
pub mod layout;
pub mod types;
pub mod values;

mod idman;

pub mod builder_traits {
  //! Re-exportations of IR builder traits.
  //!
  //! # Usage
  //!
  //! ```
  //! use koopa::ir::{FunctionData, Type};
  //! use koopa::ir::builder_traits::*;
  //!
  //! let mut func = FunctionData::new("@func", Vec::new(), Type::get_unit());
  //! // builder traits required
  //! let zero = func.dfg_mut().new_value().integer(0);
  //! ```

  pub use super::builder::{BasicBlockBuilder, GlobalInstBuilder, LocalInstBuilder, ValueBuilder};
}

pub use entities::{BasicBlock, Function, FunctionData, Program, Value, ValueKind};
pub use types::{Type, TypeKind};
pub use values::BinaryOp;
