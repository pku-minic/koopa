pub mod core;
pub mod instructions;
pub mod structs;
pub mod types;
pub mod values;

mod utils;

use self::core::{Use, Value, ValueDataAdapter};
use self::values::*;
use intrusive_collections::LinkedList;
use std::rc::{Rc, Weak};

/// Node of Koopa IR.
pub enum Node {
  Integer(Integer),
  ZeroInit(ZeroInit),
  Undef(Undef),
  Aggregate(Aggregate),
}

/// Rc of `Node`.
///
/// Used when a type has ownership of `Node`.
pub type NodeRc = Rc<Node>;

/// Reference of `Node`.
///
/// Used when a type only needs to refer to `Node`.
pub type NodeRef = Weak<Node>;

impl Value for Node {
  fn uses(&self) -> &LinkedList<ValueDataAdapter> {
    todo!()
  }

  fn add_use(&mut self, u: Weak<Use>) {
    todo!()
  }

  fn remove_use(&mut self, u: Weak<Use>) {
    todo!()
  }

  fn replace_all_uses_with(&mut self, value: NodeRc) {
    todo!()
  }
}

impl Node {
  pub fn is_user(&self) -> bool {
    match self {
      Node::Aggregate(_) | todo!() => true,
      _ => false,
    }
  }
}
