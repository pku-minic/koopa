use crate::ir::core::ValueAdapter;
use crate::ir::{Type, TypeKind, Value, ValueKind, ValueRc};
use crate::utils::NewWithRef;
use intrusive_collections::linked_list::{Cursor, CursorMut};
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

  /// Gets the mutable global variables.
  pub fn vars_mut(&mut self) -> &mut LinkedList<ValueAdapter> {
    &mut self.vars
  }

  /// Gets the function definitions.
  pub fn funcs(&self) -> &LinkedList<FunctionAdapter> {
    &self.funcs
  }

  /// Gets the mutable function definitions.
  pub fn funcs_mut(&mut self) -> &mut LinkedList<FunctionAdapter> {
    &mut self.funcs
  }

  /// Adds the specific global variable to the current program.
  pub fn add_var(&mut self, value: ValueRc) {
    assert!(
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

impl Default for Program {
  fn default() -> Self {
    Self::new()
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
  /// Creates a new function definition.
  pub fn new(name: String, params: Vec<ValueRc>, ret_ty: Type) -> FunctionRc {
    assert!(
      name.len() > 1 && (name.starts_with('%') || name.starts_with('@')),
      "invalid function name"
    );
    let ty = Type::get_function(
      params
        .iter()
        .map(|p| {
          let ty = p.ty().clone();
          assert!(!ty.is_unit(), "parameter type must not be `unit`!");
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

  /// Creates a new function declaration.
  pub fn new_decl(name: String, ty: Type) -> FunctionRc {
    assert!(
      name.len() > 1 && (name.starts_with('%') || name.starts_with('@')),
      "invalid function name"
    );
    match ty.kind() {
      TypeKind::Function(params, _) => {
        assert!(
          params.iter().all(|p| !p.is_unit()),
          "parameter type must not be `unit`!"
        )
      }
      _ => panic!("expected a function type!"),
    };
    Rc::new(Self {
      link: LinkedListLink::new(),
      ty,
      name,
      params: Vec::new(),
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

  /// Immutably borrows the inner of the current function.
  ///
  /// # Panics
  ///
  /// Panics if the inner function is currently mutably borrowed.
  pub fn inner(&self) -> Ref<FunctionInner> {
    self.inner.borrow()
  }

  /// Mutably borrows the inner of the current function.
  ///
  /// # Panics
  ///
  /// Panics if the inner function is currently borrowed.
  pub fn inner_mut(&self) -> RefMut<FunctionInner> {
    self.inner.borrow_mut()
  }
}

pub struct FunctionInner {
  bbs: LinkedList<BasicBlockAdapter>,
}

impl FunctionInner {
  /// Gets the basic block list.
  ///
  /// If `bbs` is empty, the current function will be a declaration.
  /// Otherwise, the first basic block in the list will be the entry.
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
    assert!(
      name.as_ref().map_or(true, |n| n.len() > 1
        && (n.starts_with('%') || n.starts_with('@'))),
      "invalid basic block name"
    );
    Rc::new_with_ref(|bb| Self {
      link: LinkedListLink::new(),
      name,
      inner: RefCell::new(BasicBlockInner {
        bb,
        preds: PredList(Vec::new()),
        insts: LinkedList::default(),
      }),
    })
  }

  /// Gets the name.
  pub fn name(&self) -> &Option<String> {
    &self.name
  }

  /// Immutably borrows the inner of the current basic block.
  ///
  /// # Panics
  ///
  /// Panics if the inner basic block is currently mutably borrowed.
  pub fn inner(&self) -> Ref<BasicBlockInner> {
    self.inner.borrow()
  }

  /// Mutably borrows the inner of the current basic block.
  ///
  /// # Panics
  ///
  /// Panics if the inner basic block is currently borrowed.
  pub fn inner_mut(&self) -> RefMut<BasicBlockInner> {
    self.inner.borrow_mut()
  }
}

pub struct BasicBlockInner {
  bb: BasicBlockRef,
  preds: PredList,
  insts: LinkedList<ValueAdapter>,
}

impl BasicBlockInner {
  /// Gets the predecessor list.
  pub fn preds(&self) -> &[BasicBlockRef] {
    &self.preds.0
  }

  /// Gets the mutable predecessor list.
  pub(crate) fn preds_mut(&mut self) -> &mut PredList {
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

  /// Creates a [`ValueCursorMut`] from a instruction (value).
  ///
  /// # Panics
  ///
  /// Panics when `inst` is not in the current basic block.
  pub fn cursor_mut_from_inst(&mut self, inst: &Value) -> ValueCursorMut<'_> {
    assert!(
      inst
        .inner()
        .bb()
        .as_ref()
        .map_or(false, |bb| self.bb.ptr_eq(bb)),
      "`inst` is not in the current basic block"
    );
    ValueCursorMut {
      cursor: unsafe { self.insts.cursor_mut_from_ptr(inst) },
      bb: self.bb.clone(),
      preds: &mut self.preds,
    }
  }

  /// Returns a [`ValueCursorMut`] pointing to the first instruction of the
  /// list. If the the list is empty then a null cursor is returned.
  pub fn front_mut(&mut self) -> ValueCursorMut<'_> {
    ValueCursorMut {
      cursor: self.insts.front_mut(),
      bb: self.bb.clone(),
      preds: &mut self.preds,
    }
  }

  /// Returns a [`ValueCursorMut`] pointing to the last instruction of the
  /// list. If the the list is empty then a null cursor is returned.
  pub fn back_mut(&mut self) -> ValueCursorMut<'_> {
    ValueCursorMut {
      cursor: self.insts.back_mut(),
      bb: self.bb.clone(),
      preds: &mut self.preds,
    }
  }

  /// Adds the specific instruction to the end of the current basic block.
  ///
  /// # Panics
  ///
  /// Panics when `inst` is not an instruction, or the instruction
  /// is already in another basic block.
  pub fn add_inst(&mut self, inst: ValueRc) {
    self.back_mut().insert_after(inst);
  }
}

impl Drop for BasicBlockInner {
  fn drop(&mut self) {
    // handle all phi functions manually to prevent circular references
    for inst in &self.insts {
      if matches!(inst.kind(), ValueKind::Phi(_)) {
        inst.inner_mut().replace_all_uses_with(None);
      }
    }
  }
}

/// Predecessor list.
pub(crate) struct PredList(Vec<BasicBlockRef>);

impl PredList {
  /// Adds the specific basic block to the predecessor list.
  pub(crate) fn add_pred(&mut self, bb: BasicBlockRef) {
    // update predecessor list
    self.0.push(bb);
  }

  /// Removes the specific basic block from the predecessor list.
  pub(crate) fn remove_pred(&mut self, bb: &BasicBlockRef) {
    if let Some(i) = self.0.iter().position(|b| b.ptr_eq(bb)) {
      self.0.swap_remove(i);
    }
  }
}

/// Mutable cursor of an instruction (value) list.
pub struct ValueCursorMut<'a> {
  cursor: CursorMut<'a, ValueAdapter>,
  bb: BasicBlockRef,
  preds: &'a mut PredList,
}

macro_rules! impl_methods {
  () => {};
  (pub fn $name:ident($($t:tt)*) $(-> $ret:ty)?; $($rest:tt)*) => {
    impl_methods! { @impl pub fn $name($($t)*) $(-> $ret)?; }
    impl_methods! { $($rest)* }
  };
  (@impl pub fn $name:ident(&self $(,$arg:ident: $ty:ty)*) $(-> $ret:ty)?;) => {
    #[doc = concat!(
      "See [`intrusive_collections::linked_list::CursorMut::", stringify!($name), "`]."
    )]
    #[inline(always)]
    pub fn $name(&self $(,$arg: $ty)*) $(-> $ret)? {
      self.cursor.$name($($arg,)*)
    }
  };
  (@impl pub fn $name:ident(&mut self $(,$arg:ident: $ty:ty)*) $(-> $ret:ty)?;) => {
    #[doc = concat!(
      "See [`intrusive_collections::linked_list::CursorMut::", stringify!($name), "`]."
    )]
    #[inline(always)]
    pub fn $name(&mut self $(,$arg: $ty)*) $(-> $ret)? {
      self.cursor.$name($($arg,)*)
    }
  };
}

impl<'a> ValueCursorMut<'a> {
  impl_methods! {
    pub fn is_null(&self) -> bool;
    pub fn get(&self) -> Option<&Value>;
    pub fn as_cursor(&self) -> Cursor<'_, ValueAdapter>;
    pub fn move_next(&mut self);
    pub fn move_prev(&mut self);
    pub fn peek_next(&self) -> Cursor<'_, ValueAdapter>;
    pub fn peek_prev(&self) -> Cursor<'_, ValueAdapter>;
  }

  /// Removes the current instruction from the instruction list.
  ///
  /// The removed [`ValueRc`] is returned, and the cursor is moved to point to
  /// the next instruction.
  ///
  /// If the cursor is currently pointing to the null object, no instruction
  /// is removed and [`None`] is returned.
  pub fn remove(&mut self) -> Option<ValueRc> {
    self.cursor.remove().map(|inst| {
      let mut inst_inner = inst.inner_mut();
      // break circular references if the instruction is a phi function
      if matches!(inst.kind(), ValueKind::Phi(_)) {
        inst_inner.replace_all_uses_with(None);
      }
      // remove from the current basic block
      inst_inner.set_bb(None);
      inst.remove_pred(&self.bb, self.preds);
      drop(inst_inner);
      inst
    })
  }

  /// Removes the current instruction from the instruction list and inserts
  /// another instruction in its place.
  ///
  /// The removed [`ValueRc`] is returned, and the cursor is modified to point
  /// to the newly added instruction.
  ///
  /// If the cursor is currently pointing to the null object, an error is
  /// returned containing the given `inst` parameter.
  ///
  /// # Panics
  ///
  /// Panics if `inst` is not an instruction, or it's already linked to a
  /// different instruction list.
  pub fn replace_with(&mut self, inst: ValueRc) -> Result<ValueRc, ValueRc> {
    assert!(inst.is_inst(), "`inst` is not an instruction");
    self.cursor.replace_with(inst.clone()).map(|old| {
      // update `old`
      let mut old_inner = old.inner_mut();
      old_inner.set_bb(None);
      old.remove_pred(&self.bb, self.preds);
      drop(old_inner);
      // update `inst`
      let mut inst_inner = inst.inner_mut();
      inst_inner.set_bb(Some(self.bb.clone()));
      inst.add_pred(self.bb.clone(), self.preds);
      old
    })
  }

  /// Inserts a new instruction into the instruction list after the current
  /// one.
  ///
  /// If the cursor is pointing at the null object, the new instruction is
  /// inserted at the front of the instruction list.
  ///
  /// # Panics
  ///
  /// Panics if `inst` is not an instruction, or it's already linked to a
  /// different instruction list.
  pub fn insert_after(&mut self, inst: ValueRc) {
    self.insert_update_inst(&inst);
    self.cursor.insert_after(inst);
  }

  /// Inserts a new instruction into the instruction list before the current
  /// one.
  ///
  /// If the cursor is pointing at the null object, the new instruction is
  /// inserted at the end of the instruction list.
  ///
  /// # Panics
  ///
  /// Panics if `inst` is not an instruction, or it's already linked to a
  /// different instruction list.
  pub fn insert_before(&mut self, inst: ValueRc) {
    self.insert_update_inst(&inst);
    self.cursor.insert_before(inst);
  }

  /// Checks and updates the specific instruction before insertion.
  fn insert_update_inst(&mut self, inst: &Value) {
    assert!(inst.is_inst(), "`inst` is not an instruction");
    inst.inner_mut().set_bb(Some(self.bb.clone()));
    inst.add_pred(self.bb.clone(), self.preds);
  }
}
