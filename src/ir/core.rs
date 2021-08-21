use crate::ir::instructions::*;
use crate::ir::structs::BasicBlockRef;
use crate::ir::types::Type;
use crate::ir::values::*;
use intrusive_collections::{intrusive_adapter, LinkedList, LinkedListLink, UnsafeRef};
use std::cell::{Cell, Ref, RefCell, RefMut};
use std::mem::MaybeUninit;
use std::rc::{Rc, Weak};

/// Value in Koopa IR.
///
/// A value can be used by other users.
pub struct Value {
  link: LinkedListLink,
  inner: RefCell<ValueInner>,
}

intrusive_adapter!(pub(crate) ValueAdapter = ValueRc: Value { link: LinkedListLink });

/// Rc of `Value`.
///
/// Used when a type has ownership of `Value`.
pub type ValueRc = Rc<Value>;

/// Reference of `Value`.
///
/// Used when a type only needs to refer to `Value`.
pub type ValueRef = Weak<Value>;

impl Value {
  pub(crate) fn new(ty: Type, kind: ValueKind) -> ValueRc {
    Rc::new(Value {
      link: LinkedListLink::new(),
      inner: RefCell::new(ValueInner {
        uses: LinkedList::new(UseAdapter::new()),
        ty: ty,
        bb: None,
        kind: kind,
      }),
    })
  }

  pub(crate) fn new_with_init<F>(ty: Type, init: F) -> ValueRc
  where
    F: FnOnce(ValueRef) -> ValueKind,
  {
    let value = Rc::new(Value {
      link: LinkedListLink::new(),
      inner: RefCell::new(ValueInner {
        uses: LinkedList::new(UseAdapter::new()),
        ty: ty,
        bb: None,
        kind: unsafe { MaybeUninit::uninit().assume_init() },
      }),
    });
    let user = Rc::downgrade(&value);
    value.borrow_mut().kind = init(user);
    value
  }

  pub fn borrow(&self) -> Ref<'_, ValueInner> {
    self.inner.borrow()
  }

  pub fn borrow_mut(&self) -> RefMut<'_, ValueInner> {
    self.inner.borrow_mut()
  }
}

pub struct ValueInner {
  uses: LinkedList<UseAdapter>,
  ty: Type,
  bb: Option<BasicBlockRef>,
  kind: ValueKind,
}

impl ValueInner {
  /// Gets use list of the current `Value`.
  pub fn uses(&self) -> &LinkedList<UseAdapter> {
    &self.uses
  }

  /// Adds use to the current `Value`.
  fn add_use(&mut self, u: UseRef) {
    self.uses.push_back(u);
  }

  /// Removes the specific use `u` from the current `Value`.
  ///
  /// Undefined if `u` is not in the use list.
  fn remove_use(&mut self, u: &Use) {
    unsafe {
      self.uses.cursor_mut_from_ptr(u).remove();
    }
  }

  /// Replaces all uses of the current `Value` to another `Value`.
  pub fn replace_all_uses_with(&mut self, value: ValueRc) {
    debug_assert!(
      !std::ptr::eq(&value.borrow().uses, &self.uses),
      "`value` can not be the same as `self`!"
    );
    while let Some(u) = self.uses.front().clone_pointer() {
      u.as_ref().set_value(value.clone());
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
    todo!();
    // !matches!(
    //   self.kind,
    //   ValueKind::Integer(..)
    //     | ValueKind::ZeroInit(..)
    //     | ValueKind::Undef(..)
    //     | ValueKind::Alloc(..)
    // )
  }

  /// Checks if the current `Value` is an instruction.
  pub fn is_inst(&self) -> bool {
    todo!()
  }
}

/// All supported values.
pub enum ValueKind {
  Integer(Integer),
  ZeroInit(ZeroInit),
  Undef(Undef),
  Aggregate(Aggregate),
  Alloc(Alloc),
  GlobalAlloc(GlobalAlloc),
  Load(Load),
  Store(Store),
  GetPtr(GetPtr),
  Binary(Binary),
  Unary(Unary),
}

/// Bidirectional reference between `Value`s and `Instruction`s.
pub struct Use {
  link: LinkedListLink,
  value: Cell<Option<ValueRc>>,
  user: ValueRef,
}

intrusive_adapter!(pub UseAdapter = UseRef: Use { link: LinkedListLink });

/// Box of `Use`.
///
/// Used when a type has ownership of `Use`.
pub type UseBox = Box<Use>;

/// Reference of `Use`.
///
/// Used when a type only needs to refer to `Use`.
pub type UseRef = UnsafeRef<Use>;

impl Use {
  /// Creates a new `Rc` of `Use`.
  pub fn new(value: ValueRc, user: ValueRef) -> UseBox {
    debug_assert!(
      user.upgrade().unwrap().borrow().is_user(),
      "`user` is not a `User`!"
    );
    let use_ptr = Box::into_raw(Box::new(Use {
      link: LinkedListLink::new(),
      value: Cell::new(Some(value.clone())),
      user: user,
    }));
    unsafe {
      value.borrow_mut().add_use(UnsafeRef::from_raw(use_ptr));
      Box::from_raw(use_ptr)
    }
  }

  /// Gets the clone of value that the current use holds.
  pub fn value(&self) -> ValueRc {
    let v = self.value.take();
    self.value.set(v.clone());
    v.unwrap()
  }

  /// Gets the user that the current use holds.
  pub fn user(&self) -> &ValueRef {
    &self.user
  }

  /// Sets the value that the current use holds.
  pub fn set_value(&self, value: ValueRc) {
    let old_val = self.value.replace(Some(value.clone())).unwrap();
    old_val.borrow_mut().remove_use(self);
    value
      .borrow_mut()
      .add_use(unsafe { UnsafeRef::from_raw(self) });
  }
}

impl Drop for Use {
  fn drop(&mut self) {
    let s = &*self;
    let value = s.value.take().unwrap();
    value.borrow_mut().remove_use(s);
  }
}
