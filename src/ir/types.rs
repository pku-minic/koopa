//! Types of Koopa IR values.
//!
//! Each Koopa IR value and function should have a type. A type can be
//! a 32-bit integer type, a unit type, an array type, a pointer type,
//! or a function type.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;
use std::{cmp, fmt, hash, mem};

/// Kind of type.
#[derive(Hash, Clone, PartialEq, Eq)]
pub enum TypeKind {
  /// 32-bit integer.
  Int32,
  /// Unit (void).
  Unit,
  /// Array (with base type and length).
  Array(Type, usize),
  /// Pointer (with base type).
  Pointer(Type),
  /// Function (with parameter types and return type).
  Function(Vec<Type>, Type),
}

impl fmt::Display for TypeKind {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      TypeKind::Int32 => write!(f, "i32"),
      TypeKind::Unit => write!(f, "unit"),
      TypeKind::Array(t, len) => write!(f, "[{}, {}]", t, len),
      TypeKind::Pointer(t) => write!(f, "*{}", t),
      TypeKind::Function(params, ret) => {
        write!(f, "(")?;
        let mut first = true;
        for param in params {
          if !first {
            write!(f, ", ")?;
          }
          write!(f, "{}", param)?;
          first = false;
        }
        if !ret.is_unit() {
          write!(f, "): {}", ret)
        } else {
          write!(f, ")")
        }
      }
    }
  }
}

/// Types of Koopa IR values.
#[derive(Clone, Eq)]
pub struct Type(Rc<TypeKind>);

impl Type {
  thread_local! {
    /// Pool of all created types.
    static POOL: RefCell<HashMap<TypeKind, Type>> = RefCell::new(HashMap::new());

    /// Size of pointers.
    static PTR_SIZE: Cell<usize> = Cell::new(mem::size_of::<*const ()>());
  }

  /// Returns a type by the given [`TypeKind`].
  pub fn get(type_data: TypeKind) -> Type {
    Self::POOL.with(|pool| {
      let mut pool = pool.borrow_mut();
      pool.get(&type_data).cloned().unwrap_or_else(|| {
        let v = Self(Rc::new(type_data.clone()));
        pool.insert(type_data, v.clone());
        v
      })
    })
  }

  /// Returns an `i32` type.
  pub fn get_i32() -> Type {
    Type::get(TypeKind::Int32)
  }

  /// Returns an `unit` type.
  pub fn get_unit() -> Type {
    Type::get(TypeKind::Unit)
  }

  /// Returns an array type.
  pub fn get_array(base: Type, len: usize) -> Type {
    assert!(len != 0, "`len` can not be zero!");
    Type::get(TypeKind::Array(base, len))
  }

  /// Returns an pointer type.
  pub fn get_pointer(base: Type) -> Type {
    Type::get(TypeKind::Pointer(base))
  }

  /// Returns an function type.
  pub fn get_function(params: Vec<Type>, ret: Type) -> Type {
    Type::get(TypeKind::Function(params, ret))
  }

  /// Sets the size of pointers.
  pub fn set_ptr_size(size: usize) {
    Self::PTR_SIZE.with(|ptr_size| ptr_size.set(size));
  }

  /// Returns a reference to the kind of the current type.
  pub fn kind(&self) -> &TypeKind {
    &self.0
  }

  /// Checks if the current type is an integer type.
  pub fn is_i32(&self) -> bool {
    matches!(self.0.as_ref(), TypeKind::Int32)
  }

  /// Checks if the current type is a unit type.
  pub fn is_unit(&self) -> bool {
    matches!(self.0.as_ref(), TypeKind::Unit)
  }

  /// Returns the size of the current type in bytes.
  pub fn size(&self) -> usize {
    match self.kind() {
      TypeKind::Int32 => 4,
      TypeKind::Unit => 0,
      TypeKind::Array(ty, len) => ty.size() * len,
      TypeKind::Pointer(..) | TypeKind::Function(..) => Self::PTR_SIZE.with(|s| s.get()),
    }
  }
}

impl cmp::PartialEq for Type {
  fn eq(&self, other: &Self) -> bool {
    Rc::ptr_eq(&self.0, &other.0)
  }
}

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.0)
  }
}

impl fmt::Debug for Type {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.0)
  }
}

impl hash::Hash for Type {
  fn hash<H: hash::Hasher>(&self, state: &mut H) {
    self.0.hash(state);
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn print_type() {
    assert_eq!(format!("{}", Type::get_i32()), "i32");
    assert_eq!(format!("{}", Type::get_unit()), "unit");
    assert_eq!(
      format!("{}", Type::get_array(Type::get_i32(), 10)),
      "[i32, 10]"
    );
    assert_eq!(
      format!(
        "{}",
        Type::get_array(Type::get_array(Type::get_i32(), 2), 3)
      ),
      "[[i32, 2], 3]"
    );
    assert_eq!(
      format!("{}", Type::get_pointer(Type::get_pointer(Type::get_i32()))),
      "**i32"
    );
    assert_eq!(
      format!("{}", Type::get_function(Vec::new(), Type::get_unit())),
      "()"
    );
    assert_eq!(
      format!(
        "{}",
        Type::get_function(vec![Type::get_i32()], Type::get_unit())
      ),
      "(i32)"
    );
    assert_eq!(
      format!(
        "{}",
        Type::get_function(vec![Type::get_i32(), Type::get_i32()], Type::get_i32())
      ),
      "(i32, i32): i32"
    );
  }

  #[test]
  fn type_eq() {
    assert_eq!(Type::get_i32(), Type::get_i32());
    assert_eq!(
      Type::get_array(Type::get_i32(), 6),
      Type::get_array(Type::get_i32(), 6)
    );
    assert_ne!(
      Type::get_array(Type::get_i32(), 6),
      Type::get_array(Type::get_i32(), 7)
    );
  }

  #[test]
  fn type_size() {
    assert_eq!(Type::get_i32().size(), 4);
    assert_eq!(Type::get_unit().size(), 0);
    assert_eq!(Type::get_array(Type::get_i32(), 5).size(), 4 * 5);
    assert_eq!(
      Type::get_array(Type::get_array(Type::get_i32(), 6), 5).size(),
      4 * 6 * 5
    );
    assert_eq!(
      Type::get_pointer(Type::get_array(Type::get_i32(), 5)).size(),
      mem::size_of::<usize>()
    );
    assert_eq!(
      Type::get_array(Type::get_pointer(Type::get_i32()), 5).size(),
      mem::size_of::<usize>() * 5
    );
    assert_eq!(
      Type::get_function(vec![Type::get_i32(), Type::get_i32()], Type::get_unit()).size(),
      mem::size_of::<usize>()
    );
    Type::set_ptr_size(4);
    assert_eq!(
      Type::get_array(Type::get_pointer(Type::get_i32()), 5).size(),
      4 * 5
    );
  }
}
