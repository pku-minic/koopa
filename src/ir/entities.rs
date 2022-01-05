//! Koopa IR entities, including programs ([`Program`]), functions
//! ([`Function`], [`FunctionData`]), basic blocks ([`BasicBlock`],
//! [`BasicBlockData`]) and values ([`Value`], [`ValueData`]).

use crate::ir::builder::GlobalBuilder;
use crate::ir::dfg::DataFlowGraph;
use crate::ir::idman::{is_global_id, next_func_id, next_global_value_id};
use crate::ir::idman::{BasicBlockId, FunctionId, ValueId};
use crate::ir::layout::Layout;
use crate::ir::types::Type;
use crate::ir::values;
use std::cell::{Ref, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};

/// A Koopa IR program.
///
/// Programs can hold global values and functions.
#[derive(Default)]
pub struct Program {
  pub(in crate::ir) values: Rc<RefCell<HashMap<Value, ValueData>>>,
  pub(in crate::ir) inst_layout: Vec<Value>,
  funcs: HashMap<Function, FunctionData>,
  func_tys: Rc<RefCell<HashMap<Function, Type>>>,
  func_layout: Vec<Function>,
}

/// Returns a mutable reference to the global value data by the given
/// value handle.
macro_rules! data_mut {
  ($self:ident, $value:expr) => {
    $self
      .values
      .borrow_mut()
      .get_mut(&$value)
      .expect("value does not exist")
  };
}

impl Program {
  /// Creates a new program.
  pub fn new() -> Self {
    Self::default()
  }

  /// Creates a new global value in the current program.
  /// Returns a [`GlobalBuilder`] for building the new global value.
  pub fn new_value(&mut self) -> GlobalBuilder {
    GlobalBuilder { program: self }
  }

  /// Creates a new global value by its value data. Returns the handle of
  /// the created value. This method will be called by [`GlobalBuilder`].
  ///
  /// # Panics
  ///
  /// Panics if the given value data uses unexisted values.
  pub(in crate::ir) fn new_value_data(&mut self, data: ValueData) -> Value {
    let value = Value(next_global_value_id());
    for v in data.kind().value_uses() {
      data_mut!(self, v).used_by.insert(value);
    }
    self.values.borrow_mut().insert(value, data);
    value
  }

  /// Removes the given global value by its handle. Returns the
  /// corresponding value data.
  ///
  /// # Panics
  ///
  /// Panics if the given value does not exist, or the removed value is
  /// currently used by other values.
  pub fn remove_value(&mut self, value: Value) -> ValueData {
    let data = self
      .values
      .borrow_mut()
      .remove(&value)
      .expect("`value` does not exist");
    if data.kind().is_global_alloc() {
      self
        .inst_layout
        .remove(self.inst_layout.iter().position(|v| *v == value).unwrap());
    }
    assert!(data.used_by.is_empty(), "`value` is used by other values");
    for v in data.kind().value_uses() {
      data_mut!(self, v).used_by.remove(&value);
    }
    data
  }

  /// Sets the name of the given global value.
  ///
  /// # Panics
  ///
  /// Panics if the given value does not exist,
  /// or the given name (if exists) not starts with `%` or `@`.
  pub fn set_value_name(&mut self, value: Value, name: Option<String>) {
    self
      .values
      .borrow_mut()
      .get_mut(&value)
      .expect("`value` does not exist")
      .set_name(name);
  }

  /// Immutably borrows the global value map.
  pub fn borrow_values(&self) -> Ref<HashMap<Value, ValueData>> {
    self.values.borrow()
  }

  /// Returns a reference to the layout of all global values.
  pub fn inst_layout(&self) -> &[Value] {
    &self.inst_layout
  }

  /// Immutably borrows the global value data by the given value handle.
  ///
  /// # Panics
  ///
  /// Panics if the given value does not exist.
  pub fn borrow_value(&self, value: Value) -> Ref<ValueData> {
    Ref::map(self.values.borrow(), |m| {
      m.get(&value).expect("`value` does not exist")
    })
  }

  /// Creates a new function in the current program.
  pub fn new_func(&mut self, mut data: FunctionData) -> Function {
    let func = Function(next_func_id());
    data.dfg.globals = Rc::downgrade(&self.values);
    data.dfg.func_tys = Rc::downgrade(&self.func_tys);
    self.func_tys.borrow_mut().insert(func, data.ty.clone());
    self.funcs.insert(func, data);
    self.func_layout.push(func);
    func
  }

  /// Removes the given function by its handle.
  ///
  /// Returns the function data if the function was previously in the program.
  pub fn remove_func(&mut self, func: Function) -> Option<FunctionData> {
    self.func_tys.borrow_mut().remove(&func);
    self
      .func_layout
      .remove(self.func_layout.iter().position(|f| *f == func).unwrap());
    self.funcs.remove(&func)
  }

  /// Returns a reference to the function map.
  pub fn funcs(&self) -> &HashMap<Function, FunctionData> {
    &self.funcs
  }

  /// Returns a mutable reference to the function map.
  pub fn funcs_mut(&mut self) -> &mut HashMap<Function, FunctionData> {
    &mut self.funcs
  }

  /// Returns a reference to the layout of all functions.
  pub fn func_layout(&self) -> &[Function] {
    &self.func_layout
  }

  /// Returns a reference to the function data by
  /// the given function handle.
  ///
  /// # Panics
  ///
  /// Panics if the given function does not exist.
  pub fn func(&self, func: Function) -> &FunctionData {
    self.funcs.get(&func).expect("`func` does not exist")
  }

  /// Returns a mutable reference to the function data by
  /// the given function handle.
  ///
  /// # Panics
  ///
  /// Panics if the given function does not exist.
  pub fn func_mut(&mut self, func: Function) -> &mut FunctionData {
    self.funcs.get_mut(&func).expect("`func` does not exist")
  }
}

/// Weak pointer for the `RefCell` of global value map.
///
/// For [`DataFlowGraph`]s in function.
pub(in crate::ir) type GlobalValueMapCell = Weak<RefCell<HashMap<Value, ValueData>>>;

/// Weak pointer for the `RefCell` of function type map.
///
/// For [`DataFlowGraph`]s in function.
pub(in crate::ir) type FuncTypeMapCell = Weak<RefCell<HashMap<Function, Type>>>;

/// A handle of Koopa IR function.
///
/// You can fetch [`FunctionData`] from [`Program`] by using this handle.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Function(FunctionId);

/// Data of Koopa IR function.
///
/// Functions can hold basic blocks.
pub struct FunctionData {
  ty: Type,
  name: String,
  params: Vec<Value>,
  dfg: DataFlowGraph,
  layout: Layout,
}

impl FunctionData {
  /// Creates a new function definition.
  ///
  /// # Panics
  ///
  /// Panics if the given name not starts with `%` or `@`, or the given
  /// type can not construct a valid function type.
  pub fn new(name: String, params_ty: Vec<Type>, ret_ty: Type) -> Self {
    use crate::ir::values::FuncArgRef;
    Self::check_sanity(&name, params_ty.iter());
    // create function argument references
    let mut dfg = DataFlowGraph::new();
    let params = params_ty
      .iter()
      .enumerate()
      .map(|(i, ty)| dfg.new_value_data(FuncArgRef::new_data(i, ty.clone())))
      .collect();
    Self {
      ty: Type::get_function(params_ty, ret_ty),
      name,
      params,
      dfg,
      layout: Layout::new(),
    }
  }

  /// Creates a new function definition with parameter names.
  ///
  /// # Panics
  ///
  /// Panics if the given name not starts with `%` or `@`, or the given
  /// type can not construct a valid function type.
  pub fn with_param_names(name: String, params: Vec<(Option<String>, Type)>, ret_ty: Type) -> Self {
    use crate::ir::values::FuncArgRef;
    Self::check_sanity(&name, params.iter().map(|(_, ty)| ty));
    // create function argument references
    let mut dfg = DataFlowGraph::new();
    let (params, params_ty) = params
      .into_iter()
      .enumerate()
      .map(|(i, (n, ty))| {
        let v = dfg.new_value_data(FuncArgRef::new_data(i, ty.clone()));
        dfg.set_value_name(v, n);
        (v, ty)
      })
      .unzip();
    Self {
      ty: Type::get_function(params_ty, ret_ty),
      name,
      params,
      dfg,
      layout: Layout::new(),
    }
  }

  /// Creates a new function declaration.
  ///
  /// # Panics
  ///
  /// Panics if the given name not starts with `%` or `@`, or the given
  /// type can not construct a valid function type.
  pub fn new_decl(name: String, params_ty: Vec<Type>, ret_ty: Type) -> Self {
    Self::check_sanity(&name, params_ty.iter());
    Self {
      ty: Type::get_function(params_ty, ret_ty),
      name,
      params: Vec::new(),
      dfg: DataFlowGraph::new(),
      layout: Layout::new(),
    }
  }

  /// Checks if the given name and type is valid.
  ///
  /// # Panics
  ///
  /// Panics if the given name and type is invalid.
  fn check_sanity<'a, T>(name: &str, mut params: T)
  where
    T: Iterator<Item = &'a Type>,
  {
    assert!(
      name.len() > 1 && (name.starts_with('%') || name.starts_with('@')),
      "invalid function name"
    );
    assert!(
      params.all(|p| !p.is_unit()),
      "parameter type must not be `unit`!"
    );
  }

  /// Returns a reference to the function's type.
  pub fn ty(&self) -> &Type {
    &self.ty
  }

  /// Returns a reference to the function's name.
  pub fn name(&self) -> &str {
    &self.name
  }

  /// Sets the function's name.
  pub fn set_name(&mut self, name: String) {
    self.name = name;
  }

  /// Returns a reference to the function parameters.
  pub fn params(&self) -> &[Value] {
    &self.params
  }

  /// Returns a reference to the data flow graph.
  pub fn dfg(&self) -> &DataFlowGraph {
    &self.dfg
  }

  /// Returns a mutable reference to the data flow graph.
  pub fn dfg_mut(&mut self) -> &mut DataFlowGraph {
    &mut self.dfg
  }

  /// Returns a reference to the layout.
  pub fn layout(&self) -> &Layout {
    &self.layout
  }

  /// Returns a mutable reference to the layout.
  pub fn layout_mut(&mut self) -> &mut Layout {
    &mut self.layout
  }
}

/// A handle of Koopa IR basic block.
///
/// You can fetch [`BasicBlockData`] from [`DataFlowGraph`] in
/// [`FunctionData`] by using this handle.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BasicBlock(pub(in crate::ir) BasicBlockId);

/// Data of Koopa IR basic block.
///
/// `BasicBlockData` only holds parameters about this basic block, and
/// which values (branch/jump instructions) the current basic block is
/// used by. Other information, such as the data and order of instructions
/// in this basic block, can be found in [`FunctionData`] (in the data flow
/// graph or the layout).
pub struct BasicBlockData {
  name: Option<String>,
  params: Vec<Value>,
  pub(in crate::ir) used_by: HashSet<Value>,
}

impl BasicBlockData {
  pub(in crate::ir) fn new(name: Option<String>) -> Self {
    Self {
      name,
      params: Vec::new(),
      used_by: HashSet::new(),
    }
  }

  pub(in crate::ir) fn with_params(name: Option<String>, params: Vec<Value>) -> Self {
    Self {
      name,
      params,
      used_by: HashSet::new(),
    }
  }

  /// Returns a reference to the basic block's name.
  pub fn name(&self) -> &Option<String> {
    &self.name
  }

  /// Sets the basic block's name.
  pub fn set_name(&mut self, name: Option<String>) {
    self.name = name;
  }

  /// Returns a reference to the basic block parameters.
  pub fn params(&self) -> &[Value] {
    &self.params
  }

  /// Returns a mutable reference to the basic block parameters.
  pub fn params_mut(&mut self) -> &mut Vec<Value> {
    &mut self.params
  }

  /// Returns a reference to the values that the current basic block
  /// is used by.
  pub fn used_by(&self) -> &HashSet<Value> {
    &self.used_by
  }
}

/// A handle of Koopa IR value.
///
/// You can fetch [`ValueData`] from [`DataFlowGraph`] in [`FunctionData`]
/// by using this handle.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Value(pub(in crate::ir) ValueId);

impl Value {
  /// Returns `true` if the current value handle is a global value handle.
  pub fn is_global(self) -> bool {
    is_global_id(self.0)
  }
}

/// Data of Koopa IR value.
///
/// `ValueData` can hold the type and the kind of the value, and which
/// values the current value is used by.
#[derive(Debug)]
pub struct ValueData {
  ty: Type,
  name: Option<String>,
  kind: ValueKind,
  pub(in crate::ir) used_by: HashSet<Value>,
}

impl ValueData {
  /// Creates a new `ValueData` with the given type and kind.
  pub(in crate::ir) fn new(ty: Type, kind: ValueKind) -> Self {
    Self {
      ty,
      name: None,
      kind,
      used_by: HashSet::new(),
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
  ///
  /// # Panics
  ///
  /// Panics if the given name (if exists) not starts with `%` or `@`.
  pub(in crate::ir) fn set_name(&mut self, name: Option<String>) {
    assert!(
      name.as_ref().map_or(true, |n| n.len() > 1
        && (n.starts_with('%') || n.starts_with('@'))),
      "invalid value name"
    );
    self.name = name;
  }

  /// Returns a reference to the value's kind.
  pub fn kind(&self) -> &ValueKind {
    &self.kind
  }

  /// Returns a mutable reference to the value's kind.
  pub fn kind_mut(&mut self) -> &mut ValueKind {
    &mut self.kind
  }

  /// Returns a reference to the values that the current value is used by.
  pub fn used_by(&self) -> &HashSet<Value> {
    &self.used_by
  }
}

impl Clone for ValueData {
  /// Clones the current value data, except the `used_by` set.
  fn clone(&self) -> Self {
    Self {
      ty: self.ty.clone(),
      name: self.name.clone(),
      kind: self.kind.clone(),
      used_by: HashSet::new(),
    }
  }
}

/// Kind of Koopa IR value.
#[derive(Clone, Debug)]
pub enum ValueKind {
  /// Integer constant.
  Integer(values::Integer),
  /// Zero initializer.
  ZeroInit(values::ZeroInit),
  /// Undefined value.
  Undef(values::Undef),
  /// Aggregate constant.
  Aggregate(values::Aggregate),
  /// Function argument reference.
  FuncArgRef(values::FuncArgRef),
  /// Basic block argument reference.
  BlockArgRef(values::BlockArgRef),
  /// Local memory allocation.
  Alloc(values::Alloc),
  /// Global memory allocation.
  GlobalAlloc(values::GlobalAlloc),
  /// Memory load.
  Load(values::Load),
  /// Memory store.
  Store(values::Store),
  /// Pointer calculation.
  GetPtr(values::GetPtr),
  /// Element pointer calculation.
  GetElemPtr(values::GetElemPtr),
  /// Binary operation.
  Binary(values::Binary),
  /// Conditional branch.
  Branch(values::Branch),
  /// Unconditional jump.
  Jump(values::Jump),
  /// Function call.
  Call(values::Call),
  /// Function return.
  Return(values::Return),
}

impl ValueKind {
  /// Returns an iterator of all values that used by the `ValueKind`.
  pub fn value_uses(&self) -> ValueUses {
    ValueUses {
      kind: self,
      index: 0,
    }
  }

  /// Returns an iterator of all basic blocks that used by the `ValueKind`.
  pub fn bb_uses(&self) -> BasicBlockUses {
    BasicBlockUses {
      kind: self,
      index: 0,
    }
  }

  /// Returns `true` if the `ValueKind` represents a constant value.
  pub fn is_const(&self) -> bool {
    matches!(
      self,
      ValueKind::Integer(..)
        | ValueKind::ZeroInit(..)
        | ValueKind::Undef(..)
        | ValueKind::Aggregate(..)
    )
  }

  /// Returns `true` if the `ValueKind` represents a global allocation.
  pub fn is_global_alloc(&self) -> bool {
    matches!(self, ValueKind::GlobalAlloc(..))
  }

  /// Returns `true` if the `ValueKind` represents a local instruction.
  pub fn is_local_inst(&self) -> bool {
    matches!(
      self,
      ValueKind::Alloc(..)
        | ValueKind::Load(..)
        | ValueKind::Store(..)
        | ValueKind::GetPtr(..)
        | ValueKind::GetElemPtr(..)
        | ValueKind::Binary(..)
        | ValueKind::Branch(..)
        | ValueKind::Jump(..)
        | ValueKind::Call(..)
        | ValueKind::Return(..)
    )
  }
}

/// An iterator over all values that used by a [`ValueKind`].
pub struct ValueUses<'a> {
  kind: &'a ValueKind,
  index: usize,
}

impl<'a> Iterator for ValueUses<'a> {
  type Item = Value;

  fn next(&mut self) -> Option<Self::Item> {
    let cur = self.index;
    self.index += 1;
    macro_rules! vec_use {
      ($vec:expr) => {
        if cur < $vec.len() {
          Some($vec[cur])
        } else {
          None
        }
      };
    }
    macro_rules! field_use {
      ($($field:expr),+) => {
        field_use!(@expand 0 $(,$field)+)
      };
      (@expand $index:expr) => {
        None
      };
      (@expand $index:expr, $head:expr $(,$tail:expr)*) => {
        if cur == $index {
          Some($head)
        } else {
          field_use!(@expand $index + 1 $(,$tail)*)
        }
      };
    }
    match self.kind {
      ValueKind::Aggregate(v) => vec_use!(v.elems()),
      ValueKind::GlobalAlloc(v) => field_use!(v.init()),
      ValueKind::Load(v) => field_use!(v.src()),
      ValueKind::Store(v) => field_use!(v.value(), v.dest()),
      ValueKind::GetPtr(v) => field_use!(v.src(), v.index()),
      ValueKind::GetElemPtr(v) => field_use!(v.src(), v.index()),
      ValueKind::Binary(v) => field_use!(v.lhs(), v.rhs()),
      ValueKind::Branch(v) => {
        let tlen = v.true_args().len();
        if cur == 0 {
          Some(v.cond())
        } else if cur >= 1 && cur <= tlen {
          Some(v.true_args()[cur - 1])
        } else if cur > tlen && cur <= tlen + v.false_args().len() {
          Some(v.false_args()[cur - tlen - 1])
        } else {
          None
        }
      }
      ValueKind::Jump(v) => vec_use!(v.args()),
      ValueKind::Call(v) => vec_use!(v.args()),
      ValueKind::Return(v) => match cur {
        0 => v.value(),
        _ => None,
      },
      _ => None,
    }
  }
}

/// An iterator over all basic blocks that used by a [`ValueKind`].
pub struct BasicBlockUses<'a> {
  kind: &'a ValueKind,
  index: usize,
}

impl<'a> Iterator for BasicBlockUses<'a> {
  type Item = BasicBlock;

  fn next(&mut self) -> Option<Self::Item> {
    let cur = self.index;
    self.index += 1;
    match self.kind {
      ValueKind::Branch(br) => match cur {
        0 => Some(br.true_bb()),
        1 => Some(br.false_bb()),
        _ => None,
      },
      ValueKind::Jump(jump) => match cur {
        0 => Some(jump.target()),
        _ => None,
      },
      _ => None,
    }
  }
}
