use crate::ir::instructions::*;
use crate::ir::structs::BasicBlockRef;
use crate::ir::types::Type;
use crate::ir::utils::{intrusive_adapter, WeakPointerOps};
use crate::ir::values::*;
use intrusive_collections::{LinkedList, LinkedListLink};
use std::cell::RefCell;
use std::rc::{Rc, Weak};

/// Value in Koopa IR.
///
/// A value can be used by other users.
pub struct Value {
  link: LinkedListLink,
  uses: LinkedList<UseAdapter>,
  ty: Type,
  bb: Option<BasicBlockRef>,
  kind: ValueKind,
}

intrusive_adapter!(pub(crate) ValueAdapter = ValueRc: Value { link: LinkedListLink });

/// Rc of `Value`.
///
/// Used when a type has ownership of `Value`.
pub type ValueRc = Rc<RefCell<Value>>;

/// Reference of `Value`.
///
/// Used when a type only needs to refer to `Value`.
pub type ValueRef = Weak<RefCell<Value>>;

impl Value {
  pub(crate) fn new(ty: Type, kind: ValueKind) -> ValueRc {
    Rc::new(RefCell::new(Value {
      link: LinkedListLink::new(),
      uses: LinkedList::new(UseAdapter::new()),
      ty: ty,
      bb: None,
      kind: kind,
    }))
  }

  pub(crate) fn new_with_init<F>(ty: Type, kind: ValueKind, init: F) -> ValueRc
  where
    F: FnOnce(ValueRef, &mut ValueKind),
  {
    let value = Rc::new(RefCell::new(Value {
      link: LinkedListLink::new(),
      uses: LinkedList::new(UseAdapter::new()),
      ty: ty,
      bb: None,
      kind: kind,
    }));
    let user = Rc::downgrade(&value);
    init(user, &mut value.borrow_mut().kind);
    value
  }

  /// Gets use list of the current `Value`.
  pub fn uses(&self) -> &LinkedList<UseAdapter> {
    &self.uses
  }

  /// Adds use to the current `Value`.
  pub fn add_use(&mut self, u: Weak<Use>) {
    self.uses.push_back(u);
  }

  /// Removes the specific use `u` from the current `Value`.
  ///
  /// Undefined if `u` is not in the use list.
  pub fn remove_use(&mut self, u: Weak<Use>) {
    self.uses.cursor_mut_from_ptr(u.as_ptr()).remove();
  }

  /// Replaces all uses of the current `Value` to another `Value`.
  pub fn replace_all_uses_with(&mut self, value: ValueRc) {
    debug_assert!(!std::ptr::eq(value.as_ptr(), self), "`value` ");
    while let Some(u) = self.uses.front_mut().get() {
      u.set_value(value);
    }
  }

  /// Gets the type of the current `Value`.
  pub fn ty(&self) -> &Type {
    &self.ty
  }

  /// Sets the type of the current `Value`.
  pub fn set_ty(&mut self, ty: Type) {
    self.ty = ty;
  }

  /// Gets the parent basic block of the current `Value`.
  pub fn bb(&self) -> &Option<BasicBlockRef> {
    &self.bb
  }

  /// Sets the parent basic block of the current `Value`.
  pub fn set_bb(&mut self, bb: Option<BasicBlockRef>) {
    self.bb = bb;
  }

  /// Gets the kind of the current `Value`.
  pub fn kind(&self) -> &ValueKind {
    &self.kind
  }

  /// Gets the mutable kind of the current `Value`.
  pub fn kind_mut(&mut self) -> &mut ValueKind {
    &mut self.kind
  }

  /// Checks if the current `Value` is a user.
  pub fn is_user(&self) -> bool {
    !matches!(
      self.kind,
      ValueKind::Integer(..) | ValueKind::ZeroInit(..) | ValueKind::Undef(..) | todo!()
    )
  }
}

/// All supported values.
pub enum ValueKind {
  Integer(Integer),
  ZeroInit(ZeroInit),
  Undef(Undef),
  Aggregate(Aggregate),
  Alloc(Alloc),
}

/// Unwrap a `ValueKind` without any checks.
macro_rules! unwrap_kind {
  ($kind:ident, $tag:ident) => {
    match $kind {
      ValueKind::$tag(v) => v,
      _ => unreachable!(),
    }
  };
}
pub(crate) use unwrap_kind;

/// Bidirectional reference between `Value`s and `Instruction`s.
pub struct Use {
  link: LinkedListLink,
  value: ValueRc,
  user: ValueRef,
}

intrusive_adapter! {
  UseAdapter = Weak<Use> [WeakPointerOps]: Use { link: LinkedListLink }
}

impl Use {
  /// Creates a new `Rc` of `Use`.
  pub fn new(value: ValueRc, user: ValueRef) -> Rc<Self> {
    debug_assert!(
      user.upgrade().unwrap().borrow().is_user(),
      "`user` is not a `User`!"
    );
    let u = Rc::new(Use {
      link: LinkedListLink::new(),
      value: value,
      user: user,
    });
    value.borrow_mut().add_use(Rc::downgrade(&u));
    u
  }

  /// Clones the current `Use` as a `Rc` of `Use`.
  pub fn clone(&self) -> Rc<Self> {
    let u = Rc::new(Use {
      link: LinkedListLink::new(),
      value: self.value,
      user: self.user,
    });
    self.value.borrow_mut().add_use(Rc::downgrade(&u));
    u
  }

  /// Gets the value that the current use holds.
  pub fn value(&self) -> &ValueRc {
    &self.value
  }

  /// Gets the user that the current use holds.
  pub fn user(&self) -> &ValueRef {
    &self.user
  }

  /// Sets the value that the current use holds.
  pub fn set_value(&mut self, value: ValueRc) {
    self.value.borrow_mut().remove_use(Weak::from_raw(self));
    self.value = value;
    self.value.borrow_mut().add_use(Weak::from_raw(self));
  }
}

impl Drop for Use {
  fn drop(&mut self) {
    self.value.borrow_mut().remove_use(Weak::from_raw(self));
  }
}
