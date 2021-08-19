use crate::ir::core::{Use, Value, ValueData};
use crate::ir::types::Type;
use crate::ir::{Node, NodeRc};
use crate::{impl_user, impl_value};
use std::cell::RefCell;
use std::rc::Rc;

/// Integer constant.
pub struct Integer {
  data: ValueData,
  value: i32,
}

impl_value!(Integer, data);

impl Integer {
  // TODO: pool
  pub fn new(value: i32) -> NodeRc {
    Rc::new(RefCell::new(Node::Integer(Integer {
      data: ValueData::new(Type::get_i32()),
      value: value,
    })))
  }

  pub fn value(&self) -> i32 {
    self.value
  }
}

/// Zero initializer.
pub struct ZeroInit {
  data: ValueData,
}

impl_value!(ZeroInit, data);

impl ZeroInit {
  // TODO: pool
  pub fn new(ty: Type) -> NodeRc {
    Rc::new(RefCell::new(Node::ZeroInit(ZeroInit {
      data: ValueData::new(ty),
    })))
  }
}

/// Undefined value.
pub struct Undef {
  data: ValueData,
}

impl_value!(Undef, data);

impl Undef {
  // TODO: pool
  pub fn new(ty: Type) -> NodeRc {
    Rc::new(RefCell::new(Node::Undef(Undef {
      data: ValueData::new(ty),
    })))
  }
}

/// Aggregate value.
///
/// This 'value' is actually an `User`.
pub struct Aggregate {
  data: ValueData,
  elems: Vec<Rc<Use>>,
}

impl_value!(Aggregate, data);
impl_user!(Aggregate, elems);

impl Aggregate {
  pub fn new(elems: Vec<NodeRc>) -> NodeRc {
    // element list should not be empty
    debug_assert!(!elems.is_empty(), "`elem` is empty!");
    // check if all elements have the same type
    debug_assert!(
      elems
        .windows(2)
        .all(|e| e[0].borrow().ty() == e[1].borrow().ty()),
      "type mismatch in `elem`!"
    );
    // create node
    let node = Rc::new(RefCell::new(Node::Aggregate(Aggregate {
      data: ValueData::new(*elems[0].borrow().ty()),
      elems: vec![],
    })));
    // initialize element list
    let user = Rc::downgrade(&node);
    let elems = elems.into_iter().map(|e| Use::new(e, user)).collect();
    match &mut *node.borrow_mut() {
      Node::Aggregate(agg) => agg.elems = elems,
      _ => unreachable!(),
    };
    node
  }
}
