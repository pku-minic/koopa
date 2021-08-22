use crate::ir::core::{ValueAdapter, ValueRc};
use crate::ir::types::Type;
use intrusive_collections::{intrusive_adapter, LinkedList, LinkedListLink};
use std::rc::{Rc, Weak};

/// Represents a program.
pub struct Program {
  vars: LinkedList<ValueAdapter>,
  funcs: LinkedList<FunctionAdapter>,
}

impl Program {
  //
}

/// Represents a function.
pub struct Function {
  link: LinkedListLink,
  ty: Type,
  name: String,
  params: Vec<ValueRc>,
  bbs: LinkedList<BasicBlockAdapter>,
}

intrusive_adapter! {
  FunctionAdapter = FunctionRc: Function { link: LinkedListLink }
}

/// Rc of `Function`.
///
/// Used when a type has ownership of `Function`.
pub type FunctionRc = Rc<Function>;

/// Ref of `Function`.
///
/// Used when a type only needs to refer to `Function`.
pub type FunctionRef = Weak<Function>;

impl Function {
  //
}

/// Represents a basic block.
pub struct BasicBlock {
  link: LinkedListLink,
  preds: Vec<BasicBlockRef>,
  insts: LinkedList<ValueAdapter>,
}

intrusive_adapter! {
  BasicBlockAdapter = BasicBlockRc: BasicBlock { link: LinkedListLink }
}

/// Rc of `BasicBlock`.
///
/// Used when a type has ownership of `BasicBlock`.
pub type BasicBlockRc = Rc<BasicBlock>;

/// Ref of `BasicBlock`.
///
/// Used when a type only needs to refer to `BasicBlock`.
pub type BasicBlockRef = Weak<BasicBlock>;

impl BasicBlock {
  //
}
