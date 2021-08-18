use crate::ir::core::{impl_value, Value, ValueData};
use crate::ir::types::Type;

/// Integer constant.
pub struct IntegerConstant {
  data: ValueData,
  value: i32,
}

impl_value!(IntegerConstant, data);

impl IntegerConstant {
  pub fn new(value: i32) -> Self {
    IntegerConstant {
      data: ValueData::new(Type::get_i32()),
      value: value,
    }
  }
}

/// Zero initializer.
pub struct ZeroInitializer {
  data: ValueData,
}

impl_value!(ZeroInitializer, data);

impl ZeroInitializer {
  pub fn new(ty: Type) -> Self {
    ZeroInitializer {
      data: ValueData::new(ty),
    }
  }
}

/// Undefined value.
pub struct Undefined {
  data: ValueData,
}

impl_value!(Undefined, data);

impl Undefined {
  pub fn new(ty: Type) -> Self {
    Undefined {
      data: ValueData::new(ty),
    }
  }
}
