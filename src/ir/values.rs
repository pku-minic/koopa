use crate::ir::core::{Use, UseRc, Value, ValueKind, ValueRc};
use crate::ir::types::Type;

/// Integer constant.
pub struct Integer {
  value: i32,
}

impl Integer {
  // TODO: pool
  /// Creates an integer constant with value `value`.
  ///
  /// The type of the created integer constant will be `i32`.
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
  // TODO: pool
  /// Creates a zero initializer.
  ///
  /// The type of the created zero initializer will be `ty`.
  pub fn new(ty: Type) -> ValueRc {
    Value::new(ty, ValueKind::ZeroInit(ZeroInit))
  }
}

/// Undefined value.
pub struct Undef;

impl Undef {
  // TODO: pool
  /// Creates a undefined value.
  ///
  /// The type of the created undefined value will be `ty`.
  pub fn new(ty: Type) -> ValueRc {
    Value::new(ty, ValueKind::Undef(Undef))
  }
}

/// Aggregate value.
///
/// This 'value' is actually an user.
pub struct Aggregate {
  elems: Vec<UseRc>,
}

impl Aggregate {
  /// Creates an aggregate with elements `elems`.
  ///
  /// The type of the created aggregate will be `(elems[0].ty)[elems.len]`.
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
    let ty = Type::get_array(elems[0].borrow().ty().clone(), elems.len());
    Value::new_with_init(ty, |user| {
      ValueKind::Aggregate(Aggregate {
        elems: elems
          .into_iter()
          .map(|e| Use::new(e, user.clone()))
          .collect(),
      })
    })
  }

  /// Gets the elements in aggregate.
  pub fn elems(&self) -> &[UseRc] {
    &self.elems
  }
}
