use crate::ir::entities::{BasicBlock, Function, Value, ValueData, ValueKind};
use crate::ir::types::Type;
use std::fmt;

/// Integer constant.
pub struct Integer {
  value: i32,
}

impl Integer {
  pub(crate) fn new_data(value: i32) -> ValueData {
    ValueData::new(Type::get_i32(), ValueKind::Integer(Self { value }))
  }

  /// Returns the integer value.
  pub fn value(&self) -> i32 {
    self.value
  }
}

/// Zero initializer.
pub struct ZeroInit;

impl ZeroInit {
  pub(crate) fn new_data(ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::ZeroInit(Self))
  }
}

/// Undefined value.
pub struct Undef;

impl Undef {
  pub(crate) fn new_data(ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::Undef(Self))
  }
}

/// Aggregate constant.
pub struct Aggregate {
  elems: Vec<Value>,
}

impl Aggregate {
  pub(crate) fn new_data(elems: Vec<Value>, ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::Aggregate(Self { elems }))
  }

  /// Returns a reference to the aggregate elements.
  pub fn elems(&self) -> &[Value] {
    &self.elems
  }
}

/// Function argument reference.
pub struct FuncArgRef {
  index: usize,
}

impl FuncArgRef {
  pub(crate) fn new_data(index: usize, ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::FuncArgRef(Self { index }))
  }

  /// Returns the argument index.
  pub fn index(&self) -> usize {
    self.index
  }
}

/// Basic block argument reference.
pub struct BlockArgRef {
  index: usize,
}

impl BlockArgRef {
  pub(crate) fn new_data(index: usize, ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::BlockArgRef(Self { index }))
  }

  /// Returns the argument index.
  pub fn index(&self) -> usize {
    self.index
  }
}

/// Local memory allocation.
pub struct Alloc;

impl Alloc {
  pub(crate) fn new_data(ty: Type) -> ValueData {
    assert!(!ty.is_unit(), "`ty` can not be unit");
    ValueData::new(ty, ValueKind::Alloc(Self))
  }
}

/// Global memory allocation.
pub struct GlobalAlloc {
  init: Value,
}

impl GlobalAlloc {
  pub(crate) fn new_data(init: Value, ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::GlobalAlloc(Self { init }))
  }

  /// Returns a reference to the initializer.
  pub fn init(&self) -> Value {
    self.init
  }
}

/// Memory load.
pub struct Load {
  src: Value,
}

impl Load {
  pub(crate) fn new_data(src: Value, ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::Load(Self { src }))
  }

  /// Returns a reference to the source memory location.
  pub fn src(&self) -> Value {
    self.src
  }
}

/// Memory store.
pub struct Store {
  value: Value,
  dest: Value,
}

impl Store {
  pub(crate) fn new_data(value: Value, dest: Value) -> ValueData {
    ValueData::new(Type::get_unit(), ValueKind::Store(Self { value, dest }))
  }

  /// Returns a reference to the value of the memory store.
  pub fn value(&self) -> Value {
    self.value
  }

  /// Returns a reference to the destination of the memory store.
  pub fn dest(&self) -> Value {
    self.dest
  }
}

/// Pointer calculation.
pub struct GetPtr {
  src: Value,
  index: Value,
}

impl GetPtr {
  pub(crate) fn new_data(src: Value, index: Value, ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::GetPtr(Self { src, index }))
  }

  /// Returns a reference to the source memory location.
  pub fn src(&self) -> Value {
    self.src
  }

  /// Returns a reference to the index of pointer calculation.
  pub fn index(&self) -> Value {
    self.index
  }
}

/// Element pointer calculation.
pub struct GetElemPtr {
  src: Value,
  index: Value,
}

impl GetElemPtr {
  pub(crate) fn new_data(src: Value, index: Value, ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::GetElemPtr(Self { src, index }))
  }

  /// Returns a reference to the source memory location.
  pub fn src(&self) -> Value {
    self.src
  }

  /// Returns a reference to the index of element pointer calculation.
  pub fn index(&self) -> Value {
    self.index
  }
}

/// Binary operation.
pub struct Binary {
  op: BinaryOp,
  lhs: Value,
  rhs: Value,
}

impl Binary {
  pub(crate) fn new_data(op: BinaryOp, lhs: Value, rhs: Value, ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::Binary(Self { op, lhs, rhs }))
  }

  /// Returns a reference to the binary operator.
  pub fn op(&self) -> BinaryOp {
    self.op
  }

  /// Returns a reference to the left-hand side use.
  pub fn lhs(&self) -> Value {
    self.lhs
  }

  /// Returns a reference to the right-hand side use.
  pub fn rhs(&self) -> Value {
    self.rhs
  }
}

/// Supported binary operators.
#[rustfmt::skip]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
  // comparison
  NotEq, Eq, Gt, Lt, Ge, Le,
  // arithmetic
  Add, Sub, Mul, Div, Mod,
  // bitwise operations
  And, Or, Xor,
  // shifting
  Shl, Shr, Sar,
}

impl fmt::Display for BinaryOp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      BinaryOp::NotEq => f.write_str("ne"),
      BinaryOp::Eq => f.write_str("eq"),
      BinaryOp::Gt => f.write_str("gt"),
      BinaryOp::Lt => f.write_str("lt"),
      BinaryOp::Ge => f.write_str("ge"),
      BinaryOp::Le => f.write_str("le"),
      BinaryOp::Add => f.write_str("add"),
      BinaryOp::Sub => f.write_str("sub"),
      BinaryOp::Mul => f.write_str("mul"),
      BinaryOp::Div => f.write_str("div"),
      BinaryOp::Mod => f.write_str("mod"),
      BinaryOp::And => f.write_str("and"),
      BinaryOp::Or => f.write_str("or"),
      BinaryOp::Xor => f.write_str("xor"),
      BinaryOp::Shl => f.write_str("shl"),
      BinaryOp::Shr => f.write_str("shr"),
      BinaryOp::Sar => f.write_str("sar"),
    }
  }
}

/// Conditional branch.
pub struct Branch {
  cond: Value,
  true_bb: BasicBlock,
  false_bb: BasicBlock,
  true_args: Vec<Value>,
  false_args: Vec<Value>,
}

impl Branch {
  pub(crate) fn new_data(cond: Value, true_bb: BasicBlock, false_bb: BasicBlock) -> ValueData {
    ValueData::new(
      Type::get_unit(),
      ValueKind::Branch(Self {
        cond,
        true_bb,
        false_bb,
        true_args: Vec::new(),
        false_args: Vec::new(),
      }),
    )
  }

  pub(crate) fn with_args(
    cond: Value,
    true_bb: BasicBlock,
    false_bb: BasicBlock,
    true_args: Vec<Value>,
    false_args: Vec<Value>,
  ) -> ValueData {
    ValueData::new(
      Type::get_unit(),
      ValueKind::Branch(Self {
        cond,
        true_bb,
        false_bb,
        true_args,
        false_args,
      }),
    )
  }

  /// Returns a reference to the branch condition.
  pub fn cond(&self) -> Value {
    self.cond
  }

  /// Returns a reference to the true target basic block.
  pub fn true_bb(&self) -> BasicBlock {
    self.true_bb
  }

  /// Returns a reference to the false target basic block.
  pub fn false_bb(&self) -> BasicBlock {
    self.false_bb
  }

  /// Returns a reference to the arguments passed to
  /// the true target basic block.
  pub fn true_args(&self) -> &[Value] {
    &self.true_args
  }

  /// Returns a reference to the arguments passed to
  /// the false target basic block.
  pub fn false_args(&self) -> &[Value] {
    &self.false_args
  }
}

/// Unconditional jump.
pub struct Jump {
  target: BasicBlock,
  args: Vec<Value>,
}

impl Jump {
  pub(crate) fn new_data(target: BasicBlock) -> ValueData {
    ValueData::new(
      Type::get_unit(),
      ValueKind::Jump(Self {
        target,
        args: Vec::new(),
      }),
    )
  }

  pub(crate) fn with_args(target: BasicBlock, args: Vec<Value>) -> ValueData {
    ValueData::new(Type::get_unit(), ValueKind::Jump(Self { target, args }))
  }

  /// Returns a reference to the target basic block.
  pub fn target(&self) -> BasicBlock {
    self.target
  }

  /// Returns a reference to the arguments passed to the target basic block.
  pub fn args(&self) -> &[Value] {
    &self.args
  }
}

/// Function call.
pub struct Call {
  callee: Function,
  args: Vec<Value>,
}

impl Call {
  pub(crate) fn new_data(callee: Function, args: Vec<Value>, ty: Type) -> ValueData {
    ValueData::new(ty, ValueKind::Call(Self { callee, args }))
  }

  /// Returns a reference to the callee.
  pub fn callee(&self) -> Function {
    self.callee
  }

  /// Returns a reference to the argument list.
  pub fn args(&self) -> &[Value] {
    &self.args
  }
}

/// Function return.
pub struct Return {
  value: Option<Value>,
}

impl Return {
  pub(crate) fn new_data(value: Option<Value>) -> ValueData {
    ValueData::new(Type::get_unit(), ValueKind::Return(Self { value }))
  }

  /// Returns a reference to the return value.
  pub fn value(&self) -> Option<Value> {
    self.value
  }
}
