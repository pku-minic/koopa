use lazy_static::lazy_static;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Mutex;
use std::{cmp, fmt};

/// Kind of type.
#[derive(Hash, Clone, PartialEq, Eq)]
pub enum TypeKind {
  /// 32-bit integer.
  Int32,
  /// Array (with base type and shape).
  Array(Type, usize),
  /// Pointer (with base type).
  Pointer(Type),
  /// Function (with optional return type and parameter types).
  Function(Option<Type>, Vec<Type>),
}

impl fmt::Display for TypeKind {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      TypeKind::Int32 => write!(f, "i32"),
      TypeKind::Array(t, len) => write!(f, "{}[{}]", t, len),
      TypeKind::Pointer(t) => write!(f, "{}*", t),
      TypeKind::Function(ret, args) => {
        if let Some(ret) = ret {
          write!(f, "{}", ret);
        }
        write!(f, "(");
        args.iter().fold(true, |first, t| {
          if !first {
            write!(f, ", ");
          }
          write!(f, "{}", t);
          false
        });
        write!(f, ")")
      }
    }
  }
}

/// Types in Koopa.
#[derive(Hash, Clone, Eq)]
pub struct Type(Rc<TypeKind>);

lazy_static! {
  /// Pool of all created types.
  static ref TYPES: Mutex<HashMap<TypeKind, Type>> = Mutex::new(HashMap::new());
}

impl Type {
  /// Gets a specific type.
  pub fn get_type(type_data: TypeKind) -> Type {
    TYPES
      .lock()
      .unwrap()
      .get(&type_data)
      .cloned()
      .unwrap_or_else(|| {
        let k = Type(Rc::new(type_data));
        TYPES.lock().unwrap().insert(type_data, k);
        k
      })
  }

  /// Gets an `i32` type.
  pub fn get_i32() -> Type {
    Type::get_type(TypeKind::Int32)
  }

  /// Gets an array type.
  pub fn get_array(base: Type, len: usize) -> Type {
    Type::get_type(TypeKind::Array(base, len))
  }

  /// Gets an pointer type.
  pub fn get_pointer(base: Type) -> Type {
    Type::get_type(TypeKind::Pointer(base))
  }

  /// Gets an function type.
  pub fn get_function(ret: Option<Type>, args: Vec<Type>) -> Type {
    Type::get_type(TypeKind::Function(ret, args))
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

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn print_type() {
    assert_eq!(format!("{}", Type::get_i32()), "i32");
    assert_eq!(
      format!("{}", Type::get_array(Type::get_i32(), 10)),
      "i32[10]"
    );
    assert_eq!(
      format!("{}", Type::get_pointer(Type::get_pointer(Type::get_i32()))),
      "i32**"
    );
    assert_eq!(format!("{}", Type::get_function(None, vec![])), "()");
    assert_eq!(
      format!("{}", Type::get_function(None, vec![Type::get_i32()])),
      "(i32)"
    );
    assert_eq!(
      format!(
        "{}",
        Type::get_function(
          Some(Type::get_i32()),
          vec![Type::get_i32(), Type::get_i32()]
        )
      ),
      "i32(i32, i32)"
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
