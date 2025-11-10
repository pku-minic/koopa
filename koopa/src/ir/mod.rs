//! The core part of Koopa IR.
//!
//! This module provides in-memory form IR related implementations,
//! including:
//!
//! * Structs of Koopa IR programs ([`Program`]), functions ([`Function`],
//!   [`FunctionData`]), basic blocks ([`BasicBlock`],
//!   [`BasicBlockData`](entities::BasicBlockData)) and values ([`Value`],
//!   [`ValueData`](entities::ValueData)).
//! * Types of IR values ([`Type`]).
//! * IR builders and IR builder traits ([`builder`]).
//!
//! # Example
//!
//! Here is a Fibonacci function represented in Koopa IR:
//!
//! ```koopa
//! fun @fib(@n: i32): i32 {
//! %entry:
//!   %cond = le @n, 2
//!   br %cond, %then, %else
//!
//! %then:
//!   ret 1
//!
//! %else:
//!   %0 = sub @n, 1
//!   %x = call @fib(%0)
//!   %1 = sub @n, 2
//!   %y = call @fib(%1)
//!   %ans = add %x, %y
//!   ret %ans
//! }
//! ```
//!
//! You can build the corresponding Koopa IR program:
//!
//! ```
//! use koopa::ir::*;
//! use koopa::ir::builder_traits::*;
//!
//! // create program and function
//! let mut program = Program::new();
//! let fib = program.new_func(FunctionData::with_param_names(
//!   "@fib".into(),
//!   vec![(Some("@n".into()), Type::get_i32())],
//!   Type::get_i32(),
//! ));
//! let fib_data = program.func_mut(fib);
//! let n = fib_data.params()[0];
//!
//! // entry/then/else basic block
//! let entry = fib_data.dfg_mut().new_bb().basic_block(Some("%entry".into()));
//! let then = fib_data.dfg_mut().new_bb().basic_block(Some("%then".into()));
//! let else_bb = fib_data.dfg_mut().new_bb().basic_block(Some("%else".into()));
//! fib_data.layout_mut().bbs_mut().extend([entry, then, else_bb]);
//!
//! // instructions in entry basic block
//! let two = fib_data.dfg_mut().new_value().integer(2);
//! let cond = fib_data.dfg_mut().new_value().binary(BinaryOp::Le, n, two);
//! let br = fib_data.dfg_mut().new_value().branch(cond, then, else_bb);
//! fib_data.layout_mut().bb_mut(entry).insts_mut().extend([cond, br]);
//!
//! // instructions in `then` basic block
//! let one = fib_data.dfg_mut().new_value().integer(1);
//! let ret = fib_data.dfg_mut().new_value().ret(Some(one));
//! fib_data.layout_mut().bb_mut(then).insts_mut().push_key_back(ret);
//!
//! // instructions in `else` basic block
//! let sub1 = fib_data.dfg_mut().new_value().binary(BinaryOp::Sub, n, one);
//! let call1 = fib_data.dfg_mut().new_value().call(fib, vec![sub1]);
//! let sub2 = fib_data.dfg_mut().new_value().binary(BinaryOp::Sub, n, two);
//! let call2 = fib_data.dfg_mut().new_value().call(fib, vec![sub2]);
//! let ans = fib_data.dfg_mut().new_value().binary(BinaryOp::Add, call1, call2);
//! let ret = fib_data.dfg_mut().new_value().ret(Some(ans));
//! fib_data.layout_mut().bb_mut(else_bb).insts_mut().extend([sub1, call1, sub2, call2, ans, ret]);
//! ```

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
  //! let mut func = FunctionData::new("@func".into(), Vec::new(), Type::get_unit());
  //! // builder traits required
  //! let zero = func.dfg_mut().new_value().integer(0);
  //! ```

  pub use super::builder::{BasicBlockBuilder, GlobalInstBuilder, LocalInstBuilder, ValueBuilder};
}

pub use entities::{BasicBlock, Function, FunctionData, Program, Value, ValueKind};
pub use types::{Type, TypeKind};
pub use values::BinaryOp;
