use crate::ir::core::{Use, UseBox, Value, ValueKind, ValueRc};
use crate::ir::types::{Type, TypeKind};
use std::cell::RefCell;
use std::collections::HashMap;

/// Integer constant.
pub struct Integer {
  value: i32,
}

impl Integer {
  thread_local! {
    /// Pool of all created integer constants.
    static POOL: RefCell<HashMap<i32, ValueRc>> = RefCell::new(HashMap::new());
  }

  /// Creates an integer constant with value `value`.
  ///
  /// The type of the created integer constant will be `i32`.
  pub fn new(value: i32) -> ValueRc {
    Self::POOL.with(|pool| {
      let mut pool = pool.borrow_mut();
      pool.get(&value).cloned().unwrap_or_else(|| {
        let v = Value::new(Type::get_i32(), ValueKind::Integer(Integer { value }));
        pool.insert(value, v.clone());
        v
      })
    })
  }

  /// Gets the integer value.
  pub fn value(&self) -> i32 {
    self.value
  }
}

/// Zero initializer.
pub struct ZeroInit;

impl ZeroInit {
  thread_local! {
    /// Pool of all created zero initializers.
    static POOL: RefCell<HashMap<Type, ValueRc>> = RefCell::new(HashMap::new());
  }

  /// Creates a zero initializer.
  ///
  /// The type of the created zero initializer will be `ty`.
  pub fn new(ty: Type) -> ValueRc {
    debug_assert!(
      !matches!(ty.kind(), TypeKind::Unit),
      "`ty` can not be unit!"
    );
    Self::POOL.with(|pool| {
      let mut pool = pool.borrow_mut();
      pool.get(&ty).cloned().unwrap_or_else(|| {
        let v = Value::new(ty.clone(), ValueKind::ZeroInit(ZeroInit));
        pool.insert(ty, v.clone());
        v
      })
    })
  }
}

/// Undefined value.
pub struct Undef;

impl Undef {
  thread_local! {
    /// Pool of all created undefined values.
    static POOL: RefCell<HashMap<Type, ValueRc>> = RefCell::new(HashMap::new());
  }

  /// Creates a undefined value.
  ///
  /// The type of the created undefined value will be `ty`.
  pub fn new(ty: Type) -> ValueRc {
    debug_assert!(
      !matches!(ty.kind(), TypeKind::Unit),
      "`ty` can not be unit!"
    );
    Self::POOL.with(|pool| {
      let mut pool = pool.borrow_mut();
      pool.get(&ty).cloned().unwrap_or_else(|| {
        let v = Value::new(ty.clone(), ValueKind::Undef(Undef));
        pool.insert(ty, v.clone());
        v
      })
    })
  }
}

/// Aggregate value.
///
/// This 'value' is actually an user.
pub struct Aggregate {
  elems: Vec<UseBox>,
}

impl Aggregate {
  /// Creates an aggregate with elements `elems`.
  ///
  /// The type of the created aggregate will be `(elems[0].ty)[elems.len]`.
  pub fn new(elems: Vec<ValueRc>) -> ValueRc {
    // element list should not be empty
    debug_assert!(!elems.is_empty(), "`elems` must not be empty!");
    // check if all elements have the same type
    debug_assert!(
      elems.windows(2).all(|e| e[0].ty() == e[1].ty()),
      "type mismatch in `elems`!"
    );
    // check base type
    let base = elems[0].ty().clone();
    debug_assert!(
      !matches!(base.kind(), TypeKind::Unit),
      "base type must not be `unit`!"
    );
    // create value
    let ty = Type::get_array(base, elems.len());
    Value::new_with_init(ty, |user| {
      ValueKind::Aggregate(Aggregate {
        elems: elems
          .into_iter()
          .map(|e| Use::new(Some(e), user.clone()))
          .collect(),
      })
    })
  }

  /// Gets the elements in aggregate.
  pub fn elems(&self) -> &[UseBox] {
    &self.elems
  }
}

/// Function argument reference.
pub struct ArgRef {
  index: usize,
}

impl ArgRef {
  /// Creates a argument reference with index `index`.
  ///
  /// The type of the created argument reference will be `ty`.
  pub fn new(ty: Type, index: usize) -> ValueRc {
    debug_assert!(
      !matches!(ty.kind(), TypeKind::Unit),
      "`ty` can not be unit!"
    );
    Value::new(ty, ValueKind::ArgRef(ArgRef { index }))
  }

  /// Gets the index.
  pub fn index(&self) -> usize {
    self.index
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use std::rc::Rc;

  #[test]
  fn const_eq() {
    assert!(Rc::ptr_eq(&Integer::new(10), &Integer::new(10)));
    assert!(!Rc::ptr_eq(&Integer::new(10), &Integer::new(5)));
    assert!(Rc::ptr_eq(
      &ZeroInit::new(Type::get_i32()),
      &ZeroInit::new(Type::get_i32())
    ));
    assert!(Rc::ptr_eq(
      &ZeroInit::new(Type::get_array(Type::get_i32(), 10)),
      &ZeroInit::new(Type::get_array(Type::get_i32(), 10))
    ));
    assert!(!Rc::ptr_eq(
      &ZeroInit::new(Type::get_i32()),
      &ZeroInit::new(Type::get_array(Type::get_i32(), 10))
    ));
  }

  #[test]
  fn aggregate_use_value() {
    let array = Aggregate::new((0..10).map(|i| Integer::new(i)).collect());
    assert_eq!(array.ty(), &Type::get_array(Type::get_i32(), 10));
    match array.borrow().kind() {
      ValueKind::Aggregate(agg) => {
        for (i, elem) in agg.elems().iter().enumerate() {
          let value = elem.value().unwrap();
          assert!(Rc::ptr_eq(&value, &Integer::new(i as i32)));
          assert_eq!(elem.user().as_ptr(), Rc::as_ptr(&array));
          let v = value.borrow();
          let u = v.uses().front().get();
          assert!(u.is_some());
          assert!(std::ptr::eq(u.unwrap(), elem.as_ref()));
        }
      }
      _ => unreachable!(),
    }
    drop(array);
    for value in (0..10).map(|i| Integer::new(i)) {
      assert!(value.borrow().uses().is_empty());
    }
  }
}
