use crate::ir::core::{ValueAdapter, ValueRc};
use crate::ir::types::{Type, TypeKind};
use intrusive_collections::{intrusive_adapter, LinkedList, LinkedListLink};
use std::rc::{Rc, Weak};

/// Represents a program.
pub struct Program {
  vars: LinkedList<ValueAdapter>,
  funcs: LinkedList<FunctionAdapter>,
}

impl Program {
  /// Creates a new IR program.
  pub fn new() -> Self {
    Program {
      vars: LinkedList::default(),
      funcs: LinkedList::default(),
    }
  }

  /// Gets the global variables.
  pub fn vars(&self) -> &LinkedList<ValueAdapter> {
    &self.vars
  }

  /// Gets the function definitions.
  pub fn funcs(&self) -> &LinkedList<FunctionAdapter> {
    &self.funcs
  }
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
  pub FunctionAdapter = FunctionRc: Function { link: LinkedListLink }
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
  /// Creates a new function.
  pub fn new(name: String, params: Vec<ValueRc>, ret_ty: Type) -> FunctionRc {
    let ty = Type::get_function(
      ret_ty,
      params
        .iter()
        .map(|p| {
          let ty = p.ty().clone();
          debug_assert!(
            !matches!(ty.kind(), TypeKind::Unit),
            "parameter type must not be `unit`!"
          );
          ty
        })
        .collect(),
    );
    Rc::new(Function {
      link: LinkedListLink::new(),
      ty: ty,
      name: name,
      params: params,
      bbs: LinkedList::new(BasicBlockAdapter::new()),
    })
  }

  /// Gets the type of the current function.
  pub fn ty(&self) -> &Type {
    &self.ty
  }

  /// Gets the function name.
  pub fn name(&self) -> &str {
    &self.name
  }

  /// Gets the parameter list.
  pub fn params(&self) -> &[ValueRc] {
    &self.params
  }

  /// Gets the basic block list.
  pub fn bbs(&self) -> &LinkedList<BasicBlockAdapter> {
    &self.bbs
  }
}

/// Represents a basic block.
pub struct BasicBlock {
  link: LinkedListLink,
  preds: Vec<BasicBlockRef>,
  insts: LinkedList<ValueAdapter>,
}

intrusive_adapter! {
  pub BasicBlockAdapter = BasicBlockRc: BasicBlock { link: LinkedListLink }
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
  /// Creates a new basic block.
  pub fn new() -> BasicBlockRc {
    Rc::new(BasicBlock {
      link: LinkedListLink::new(),
      preds: vec![],
      insts: LinkedList::new(ValueAdapter::new()),
    })
  }

  /// Gets the predecessor list.
  pub fn preds(&self) -> &[BasicBlockRef] {
    &self.preds
  }

  /// Gets the successors list.
  pub fn succs(&self) -> &[BasicBlockRef] {
    todo!()
  }

  /// Gets the instruction list.
  pub fn insts(&self) -> &LinkedList<ValueAdapter> {
    &self.insts
  }
}
