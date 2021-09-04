use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::{cmp, fmt, hash};

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
        if !matches!(ret.0.as_ref(), TypeKind::Unit) {
          write!(f, "): {}", ret)
        } else {
          write!(f, ")")
        }
      }
    }
  }
}

/// Types in Koopa.
#[derive(Clone, Eq)]
pub struct Type(Rc<TypeKind>);

impl Type {
  thread_local! {
    /// Pool of all created types.
    static POOL: RefCell<HashMap<TypeKind, Type>> = RefCell::new(HashMap::new());
  }

  /// Gets a specific type.
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

  /// Gets an `i32` type.
  pub fn get_i32() -> Type {
    Type::get(TypeKind::Int32)
  }

  /// Gets an `unit` type.
  pub fn get_unit() -> Type {
    Type::get(TypeKind::Unit)
  }

  /// Gets an array type.
  pub fn get_array(base: Type, len: usize) -> Type {
    debug_assert!(len != 0, "`len` can not be zero!");
    Type::get(TypeKind::Array(base, len))
  }

  /// Gets an pointer type.
  pub fn get_pointer(base: Type) -> Type {
    Type::get(TypeKind::Pointer(base))
  }

  /// Gets an function type.
  pub fn get_function(params: Vec<Type>, ret: Type) -> Type {
    Type::get(TypeKind::Function(params, ret))
  }

  /// Gets the kind of the current `Type`.
  pub fn kind(&self) -> &TypeKind {
    &self.0
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
    self.0.hash(state)
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
}
