use crate::ir::idman::{next_bb_id, next_func_id, next_value_id};
use crate::ir::idman::{BasicBlockId, FunctionId, ValueId};
use crate::ir::types::Type;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::{Rc, Weak};

/// A Koopa IR program.
///
/// Programs can hold global values and functions.
#[derive(Default)]
pub struct Program {
  values: Rc<RefCell<HashMap<Value, ValueData>>>,
  funcs: HashMap<Function, FunctionData>,
}

impl Program {
  /// Creates a new program.
  pub fn new() -> Self {
    Self::default()
  }
}

/// Weak pointer for the `RefCell` of global value map.
///
/// For `DataFlowGraph`s in function.
pub(crate) type GlobalValueMapCell = Weak<RefCell<HashMap<Value, ValueData>>>;

/// A handle of Koopa IR function.
///
/// You can fetch `FunctionData` from `Program` by using this handle.
pub struct Function(FunctionId);

/// Data of Koopa IR function.
///
/// Functions can hold basic blocks.
pub struct FunctionData {
  ty: Type,
  name: String,
  params: Vec<Value>,
  // TODO: dfg and layout
}

impl FunctionData {
  /// Creates a new function definition.
  pub fn new(name: String, params: Vec<Value>, ty: Type) -> Self {
    // TODO: assertions
    Self { ty, name, params }
  }

  /// Creates a new function declaration.
  pub fn new_decl(name: String, ty: Type) -> Self {
    // TODO: assertions
    Self {
      ty,
      name,
      params: Vec::new(),
    }
  }

  /// Returns a reference to the function's type.
  pub fn ty(&self) -> &Type {
    &self.ty
  }

  /// Returns a reference to the function's name.
  pub fn name(&self) -> &String {
    &self.name
  }

  /// Returns a reference to the function parameters.
  pub fn params(&self) -> &Vec<Value> {
    &self.params
  }
}

/// A handle of Koopa IR basic block.
///
/// You can fetch `BasicBlockData` from `DataFlowGraph` in `FunctionData`
/// by using this handle.
pub struct BasicBlock(BasicBlockId);

/// Data of Koopa IR basic block.
///
/// `BasicBlockData` only holds parameters about this basic block, and
/// which values (branch/jump instructions) the current basic block is
/// used by. Other information, such as the data and order of instructions
/// in this basic block, can be found in `FunctionData` (in the data flow
/// graph or the layout).
pub struct BasicBlockData {
  ty: Type,
  name: Option<String>,
  params: Vec<Value>,
  pub(crate) used_by: Vec<Value>,
}

impl BasicBlockData {
  /// Creates a new `BasicBlockData` with the given name.
  pub fn new(name: Option<String>) -> Self {
    Self {
      ty: Type::get_basic_block(Vec::new()),
      name,
      params: Vec::new(),
      used_by: Vec::new(),
    }
  }

  /// Creates a new `BasicBlockData` with the given name, parameters and type.
  pub fn with_params(name: Option<String>, params: Vec<Value>, ty: Type) -> Self {
    Self {
      ty,
      name,
      params,
      used_by: Vec::new(),
    }
  }

  /// Returns a reference to the basic block's type.
  pub fn ty(&self) -> &Type {
    &self.ty
  }

  /// Returns a reference to the basic block's name.
  pub fn name(&self) -> &Option<String> {
    &self.name
  }

  /// Returns a reference to the basic block parameters.
  pub fn params(&self) -> &Vec<Value> {
    &self.params
  }

  /// Returns a reference to the values that the current basic block
  /// is used by.
  pub fn used_by(&self) -> &Vec<Value> {
    &self.used_by
  }
}

impl Default for BasicBlockData {
  /// Creates a `BasicBlockData` without name and parameters.
  fn default() -> Self {
    Self {
      ty: Type::get_basic_block(Vec::default()),
      name: None,
      params: Vec::default(),
      used_by: Vec::default(),
    }
  }
}

/// A handle of Koopa IR value.
///
/// You can fetch `ValueData` from `DataFlowGraph` in `FunctionData`
/// by using this handle.
pub struct Value(ValueId);

/// Data of Koopa IR value.
///
/// `ValueData` can hold the type and the kind of the value, and which
/// values the current value is used by.
pub struct ValueData {
  ty: Type,
  name: Option<String>,
  kind: ValueKind,
  pub(crate) used_by: Vec<Value>,
}

impl ValueData {
  /// Creates a new `ValueData` with the given type and kind.
  pub(crate) fn new(ty: Type, kind: ValueKind) -> Self {
    Self {
      ty,
      name: None,
      kind,
      used_by: Vec::new(),
    }
  }

  /// Returns a reference to the value's type.
  pub fn ty(&self) -> &Type {
    &self.ty
  }

  /// Returns a reference to the value's name.
  pub fn name(&self) -> &Option<String> {
    &self.name
  }

  /// Sets the name of this value.
  pub fn set_name(&mut self, name: Option<String>) {
    self.name = name;
  }

  /// Returns a reference to the value's kind.
  pub fn kind(&self) -> &ValueKind {
    &self.kind
  }

  /// Returns a reference to the values that the current value is used by.
  pub fn used_by(&self) -> &Vec<Value> {
    &self.used_by
  }
}

/// Kind of Koopa IR value.
pub enum ValueKind {
  //
}
