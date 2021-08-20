use crate::ir::core::{unwrap_kind, Use, Value, ValueKind, ValueRc};
use crate::ir::types::Type;
use std::rc::Rc;

/// Integer constant.
pub struct Integer {
  value: i32,
}

impl Integer {
  todo!("pool");
  pub fn new(value: i32) -> ValueRc {
    Value::new(
      Type::get_i32(),
      ValueKind::Integer(Integer { value: value }),
    )
  }

  /// Gets the integer value.
  pub fn value(&self) -> i32 {
    self.value
  }
}

/// Zero initializer.
pub struct ZeroInit;

impl ZeroInit {
  todo!("pool");
  pub fn new(ty: Type) -> ValueRc {
    Value::new(ty, ValueKind::ZeroInit(ZeroInit))
  }
}

/// Undefined value.
pub struct Undef;

impl Undef {
  todo!("pool");
  pub fn new(ty: Type) -> ValueRc {
    Value::new(ty, ValueKind::Undef(Undef))
  }
}

/// Aggregate value.
///
/// This 'value' is actually an user.
pub struct Aggregate {
  elems: Vec<Rc<Use>>,
}

impl Aggregate {
  pub fn new(elems: Vec<ValueRc>) -> ValueRc {
    // element list should not be empty
    debug_assert!(!elems.is_empty(), "`elem` is empty!");
    // check if all elements have the same type
    debug_assert!(
      elems
        .windows(2)
        .all(|e| e[0].borrow().ty() == e[1].borrow().ty()),
      "type mismatch in `elem`!"
    );
    // create value
    Value::new_with_init(
      *elems[0].borrow().ty(),
      ValueKind::Aggregate(Aggregate { elems: vec![] }),
      |user, kind| {
        unwrap_kind!(kind, Aggregate).elems = elems.into_iter().map(|e| Use::new(e, user)).collect()
      },
    )
  }
}
