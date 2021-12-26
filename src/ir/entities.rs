use crate::ir::idman::{next_bb_id, next_func_id, next_value_id};
use crate::ir::idman::{BasicBlockId, FunctionId, ValueId};
use crate::ir::types::{Type, TypeKind};
use crate::ir::values;
use std::cell::{Ref, RefCell};
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

  /// Creates a new global value in the current program.
  pub fn new_value(&mut self) -> Value {
    // TODO: add parameter `GlobalAlloc`
    todo!()
  }

  /// Removes the specific global value by its handle.
  ///
  /// Returns the value data if the value was previously in the program.
  pub fn remove_value(&mut self, value: &Value) -> Option<ValueData> {
    todo!()
  }

  /// Immutably borrows the global value map.
  pub fn borrow_values(&self) -> Ref<HashMap<Value, ValueData>> {
    self.values.as_ref().borrow()
  }

  /// Creates a new function in the current program.
  pub fn new_func(&mut self, data: FunctionData) -> Function {
    let func = Function(next_func_id());
    self.funcs.insert(func, data);
    func
  }

  /// Removes the specific function by its handle.
  ///
  /// Returns the function data if the function was previously in the program.
  pub fn remove_func(&mut self, func: &Function) -> Option<FunctionData> {
    self.funcs.remove(func)
  }

  /// Returns a reference to the function map.
  pub fn funcs(&self) -> &HashMap<Function, FunctionData> {
    &self.funcs
  }

  /// Returns a mutable reference to the function map.
  pub fn funcs_mut(&mut self) -> &mut HashMap<Function, FunctionData> {
    &mut self.funcs
  }
}

/// Weak pointer for the `RefCell` of global value map.
///
/// For `DataFlowGraph`s in function.
pub(crate) type GlobalValueMapCell = Weak<RefCell<HashMap<Value, ValueData>>>;

/// A handle of Koopa IR function.
///
/// You can fetch `FunctionData` from `Program` by using this handle.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
  ///
  /// # Panics
  ///
  /// Panics if `ty` is not a valid basic block type.
  pub fn with_params(name: Option<String>, params: Vec<Value>, ty: Type) -> Self {
    assert!(
      matches!(ty.kind(), TypeKind::BasicBlock(p) if p.len() == params.len()),
      "`ty` is not a valid basic block type"
    );
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
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
  Integer(values::Integer),
  ZeroInit(values::ZeroInit),
  Undef(values::Undef),
  Aggregate(values::Aggregate),
  FuncArgRef(values::FuncArgRef),
  BlockArgRef(values::BlockArgRef),
  Alloc(values::Alloc),
  GlobalAlloc(values::GlobalAlloc),
  Load(values::Load),
  Store(values::Store),
  GetPtr(values::GetPtr),
  GetElemPtr(values::GetElemPtr),
  Binary(values::Binary),
  Branch(values::Branch),
  Jump(values::Jump),
  Call(values::Call),
  Return(values::Return),
}
