use crate::ir::types::Type;
use crate::ir::utils::{intrusive_adapter, WeakPointerOps};
use crate::ir::{NodeRc, NodeRef};
use intrusive_collections::{LinkedList, LinkedListLink};
use std::rc::{Rc, Weak};

/// Value in Koopa IR.
///
/// A value can be used by other users.
pub trait Value {
  /// Gets use list of the current `Value`.
  fn uses(&self) -> &LinkedList<ValueDataAdapter>;

  /// Adds use to the current `Value`.
  fn add_use(&mut self, u: Weak<Use>);

  /// Removes the specific use `u` from the current `Value`.
  ///
  /// Undefined if `u` is not in the use list.
  fn remove_use(&mut self, u: Weak<Use>);

  /// Replaces all uses of the current `Value` to another `Value`.
  fn replace_all_uses_with(&mut self, value: NodeRc);
}

/// User in Koopa IR.
///
/// A user can use other values.
pub trait User: Value {
  /// Gets the operands of the current value.
  fn operands(&self) -> &[Rc<Use>];
}

/// Data of `Value`s.
pub struct ValueData {
  uses: LinkedList<ValueDataAdapter>, // TODO: intrusive linked list
  ty: Type,
}

intrusive_adapter! {
  pub ValueDataAdapter = Weak<Use> [WeakPointerOps]:
      Use { link: LinkedListLink }
}

impl ValueData {
  pub fn new(ty: Type) -> Self {
    ValueData {
      uses: LinkedList::new(ValueDataAdapter::new()),
      ty: ty,
    }
  }
}

impl Value for ValueData {
  fn uses(&self) -> &LinkedList<ValueDataAdapter> {
    &self.uses
  }

  fn add_use(&mut self, u: Weak<Use>) {
    self.uses.push_back(u);
  }

  fn remove_use(&mut self, u: Weak<Use>) {
    self.uses.cursor_mut_from_ptr(u.as_ptr()).remove();
  }

  fn replace_all_uses_with(&mut self, value: NodeRc) {
    while let Some(u) = self.uses.front_mut().get() {
      u.set_value(value);
    }
  }
}

/// Bidirectional reference between `Value`s and `Instruction`s.
pub struct Use {
  link: LinkedListLink,
  value: NodeRc,
  user: NodeRef,
}

impl Use {
  /// Creates a new `Rc` of `Use`.
  pub fn new(value: NodeRc, user: NodeRef) -> Rc<Self> {
    let u = Rc::new(Use {
      link: LinkedListLink::new(),
      value: value,
      user: user,
    });
    value.add_use(Rc::downgrade(&u));
    u
  }

  /// Clones the current `Use` as a `Rc` of `Use`.
  pub fn clone(&self) -> Rc<Self> {
    let u = Rc::new(Use {
      link: LinkedListLink::new(),
      value: self.value,
      user: self.user,
    });
    self.value.add_use(Rc::downgrade(&u));
    u
  }

  /// Gets the value that the current use holds.
  pub fn value(&self) -> &NodeRc {
    &self.value
  }

  /// Gets the user that the current use holds.
  pub fn user(&self) -> &NodeRef {
    &self.user
  }

  /// Sets the value that the current use holds.
  pub fn set_value(&mut self, value: NodeRc) {
    self.value.remove_use(Weak::from_raw(self));
    self.value = value;
    self.value.add_use(Weak::from_raw(self));
  }
}

impl Drop for Use {
  fn drop(&mut self) {
    self.value.remove_use(Weak::from_raw(self));
  }
}

/// Implements `Value` trait for the specific type.
#[macro_export]
macro_rules! impl_value {
  ($name:ident, $data:tt) => {
    impl $crate::ir::core::Value for $name {
      #[inline]
      fn uses(&self) -> &intrusive_collections::LinkedList<$crate::ir::core::ValueDataAdapter> {
        self.$data.uses()
      }
      #[inline]
      fn add_use(&mut self, u: std::rc::Weak<$crate::ir::core::Use>) {
        self.$data.add_use(u);
      }
      #[inline]
      fn remove_use(&mut self, u: std::rc::Weak<$crate::ir::core::Use>) {
        self.$data.remove_use(u);
      }
      #[inline]
      fn replace_all_uses_with(&mut self, value: $crate::ir::NodeRc) {
        self.$data.replace_all_uses_with(value);
      }
    }
  };
}

/// Implements `User` trait for the specific type.
#[macro_export]
macro_rules! impl_user {
  ($name:ident, $operands:tt) => {
    impl $crate::ir::core::User for $name {
      #[inline]
      fn operands(&self) -> &[Rc<Use>] {
        &self.$operands
      }
    }
  };
}
