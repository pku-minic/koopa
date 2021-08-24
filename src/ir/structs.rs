use crate::ir::core::{ValueAdapter, ValueKind, ValueRc};
use crate::ir::types::{Type, TypeKind};
use intrusive_collections::{intrusive_adapter, LinkedList, LinkedListLink};
use std::cell::{Ref, RefCell, RefMut};
use std::rc::{Rc, Weak};
use std::slice;

/// Represents a program.
pub struct Program {
  vars: LinkedList<ValueAdapter>,
  funcs: LinkedList<FunctionAdapter>,
}

impl Program {
  /// Creates a new IR program.
  pub fn new() -> Self {
    Self {
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

  /// Adds the specific global variable to the current program.
  pub fn add_var(&mut self, value: ValueRc) {
    debug_assert!(
      matches!(value.kind(), ValueKind::GlobalAlloc(..)),
      "`value` must be a global allocation!"
    );
    self.vars.push_back(value);
  }

  /// Adds the specific function to the current program.
  pub fn add_func(&mut self, func: FunctionRc) {
    self.funcs.push_back(func);
  }
}

/// Represents a function.
pub struct Function {
  link: LinkedListLink,
  ty: Type,
  name: String,
  params: Vec<ValueRc>,
  inner: RefCell<FunctionInner>,
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
      ret_ty,
    );
    Rc::new(Self {
      link: LinkedListLink::new(),
      ty,
      name,
      params,
      inner: RefCell::new(FunctionInner {
        bbs: LinkedList::default(),
      }),
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

  /// Immutably borrows the current function.
  ///
  /// Panics if the function is currently mutably borrowed.
  pub fn borrow(&self) -> Ref<FunctionInner> {
    self.inner.borrow()
  }

  /// Mutably borrows the current function.
  ///
  /// Panics if the function is currently borrowed.
  pub fn borrow_mut(&self) -> RefMut<FunctionInner> {
    self.inner.borrow_mut()
  }
}

pub struct FunctionInner {
  bbs: LinkedList<BasicBlockAdapter>,
}

impl FunctionInner {
  /// Gets the basic block list.
  pub fn bbs(&self) -> &LinkedList<BasicBlockAdapter> {
    &self.bbs
  }

  /// Gets the mutable basic block list.
  pub fn bbs_mut(&mut self) -> &mut LinkedList<BasicBlockAdapter> {
    &mut self.bbs
  }

  /// Adds the specific basic block to the current function.
  pub fn add_bb(&mut self, bb: BasicBlockRc) {
    self.bbs.push_back(bb);
  }
}

/// Represents a basic block.
pub struct BasicBlock {
  link: LinkedListLink,
  name: Option<String>,
  inner: RefCell<BasicBlockInner>,
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
  pub fn new(name: Option<String>) -> BasicBlockRc {
    Rc::new(Self {
      link: LinkedListLink::new(),
      name,
      inner: RefCell::new(BasicBlockInner {
        preds: vec![],
        insts: LinkedList::default(),
      }),
    })
  }

  /// Gets the name.
  pub fn name(&self) -> &Option<String> {
    &self.name
  }

  /// Immutably borrows the current basic block.
  ///
  /// Panics if the basic block is currently mutably borrowed.
  pub fn borrow(&self) -> Ref<BasicBlockInner> {
    self.inner.borrow()
  }

  /// Mutably borrows the current basic block.
  ///
  /// Panics if the basic block is currently borrowed.
  pub fn borrow_mut(&self) -> RefMut<BasicBlockInner> {
    self.inner.borrow_mut()
  }
}

pub struct BasicBlockInner {
  preds: Vec<BasicBlockRef>,
  insts: LinkedList<ValueAdapter>,
}

impl BasicBlockInner {
  /// Gets the predecessor list.
  pub fn preds(&self) -> &[BasicBlockRef] {
    &self.preds
  }

  /// Gets the mutable predecessor list.
  pub fn preds_mut(&mut self) -> &Vec<BasicBlockRef> {
    &mut self.preds
  }

  /// Gets the successors list.
  pub fn succs(&self) -> &[BasicBlockRef] {
    if let Some(inst) = self.insts.back().get() {
      match inst.kind() {
        ValueKind::Branch(branch) => branch.targets(),
        ValueKind::Jump(jump) => slice::from_ref(jump.target()),
        _ => &[],
      }
    } else {
      &[]
    }
  }

  /// Gets the instruction list.
  pub fn insts(&self) -> &LinkedList<ValueAdapter> {
    &self.insts
  }

  /// Gets the mutable instruction list.
  pub fn insts_mut(&mut self) -> &mut LinkedList<ValueAdapter> {
    &mut self.insts
  }

  /// Adds the specific instruction to the current basic block.
  pub fn add_inst(&mut self, inst: ValueRc) {
    self.insts.push_back(inst)
  }
}
