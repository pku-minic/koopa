use std::os::raw::{c_char, c_void};

/// A raw slice that can store any kind of items.
#[repr(C)]
pub struct RawSlice {
  /// Buffer of slice items.
  pub buffer: *const c_void,
  /// Length of slice.
  pub len: u32,
  /// Kind of slice items.
  pub kind: RawSliceItemKind,
}

/// Kind of slice item.
#[repr(u32)]
pub enum RawSliceItemKind {
  /// Unknown.
  Unknown = 0,
  /// Type.
  Type,
  /// Function.
  Function,
  /// Basic block.
  BasicBlock,
  /// Value.
  Value,
}

/// A raw Koopa type.
pub type RawType = *const RawTypeKind;

/// Kind of raw Koopa type.
#[repr(C)]
pub enum RawTypeKind {
  /// 32-bit integer.
  Int32,
  /// Unit (void).
  Unit,
  /// Array (with base type and length).
  Array(RawType, usize),
  /// Pointer (with base type).
  Pointer(RawType),
  /// Function (with parameter types and return type).
  Function(RawSlice, RawType),
}

/// A raw Koopa program.
#[repr(C)]
pub struct RawProgram {
  /// Global values (global allocations only).
  pub values: RawSlice,
  /// Function definitions.
  pub funcs: RawSlice,
}

/// A raw Koopa function.
pub type RawFunction = *const RawFunctionData;

/// Data of raw Koopa function.
#[repr(C)]
pub struct RawFunctionData {
  /// Type of function.
  pub ty: RawType,
  /// Name of function.
  pub name: *const c_char,
  /// Parameters.
  pub params: RawSlice,
  /// Basic blocks, empty if is a function declaration.
  pub bbs: RawSlice,
}

/// A raw Koopa basic block.
pub type RawBasicBlock = *const RawBasicBlockData;

/// Data of raw Koopa basic block.
#[repr(C)]
pub struct RawBasicBlockData {
  /// Name of basic block, null if no name.
  pub name: *const c_char,
  /// Parameters.
  pub params: RawSlice,
  /// Values that this basic block is used by.
  pub used_by: RawSlice,
  /// Instructions in this basic block.
  pub insts: RawSlice,
}

/// A raw Koopa value.
pub type RawValue = *const RawValueData;

/// Data of raw Koopa value.
#[repr(C)]
pub struct RawValueData {
  /// Type of value.
  pub ty: RawType,
  /// Name of value, null if no name.
  pub name: *const c_char,
  /// Values that this value is used by.
  pub used_by: RawSlice,
  /// Kind of value.
  pub kind: RawValueKind,
}

/// Kind of raw Koopa value.
#[repr(C)]
pub enum RawValueKind {
  /// Integer constant.
  Integer(RawInteger),
  /// Zero initializer.
  ZeroInit,
  /// Undefined value.
  Undef,
  /// Aggregate constant.
  Aggregate(RawAggregate),
  /// Function argument reference.
  FuncArgRef(RawFuncArgRef),
  /// Basic block argument reference.
  BlockArgRef(RawBlockArgRef),
  /// Local memory allocation.
  Alloc,
  /// Global memory allocation.
  GlobalAlloc(RawGlobalAlloc),
  /// Memory load.
  Load(RawLoad),
  /// Memory store.
  Store(RawStore),
  /// Pointer calculation.
  GetPtr(RawGetPtr),
  /// Element pointer calculation.
  GetElemPtr(RawGetElemPtr),
  /// Binary operation.
  Binary(RawBinary),
  /// Conditional branch.
  Branch(RawBranch),
  /// Unconditional jump.
  Jump(RawJump),
  /// Function call.
  Call(RawCall),
  /// Function return.
  Return(RawReturn),
}

/// Raw integer constant.
#[repr(C)]
pub struct RawInteger {
  /// Value of integer.
  pub value: i32,
}

/// Raw aggregate constant.
#[repr(C)]
pub struct RawAggregate {
  /// Elements.
  pub elems: RawSlice,
}

/// Raw function argument reference.
#[repr(C)]
pub struct RawFuncArgRef {
  /// Index.
  pub index: usize,
}

/// Raw basic block argument reference.
#[repr(C)]
pub struct RawBlockArgRef {
  /// Index.
  pub index: usize,
}

/// Raw global memory allocation.
#[repr(C)]
pub struct RawGlobalAlloc {
  /// Initializer.
  pub init: RawValue,
}

/// Raw memory load.
#[repr(C)]
pub struct RawLoad {
  /// Source.
  pub src: RawValue,
}

/// Raw memory store.
#[repr(C)]
pub struct RawStore {
  /// Value.
  pub value: RawValue,
  /// Destination.
  pub dest: RawValue,
}

/// Raw pointer calculation.
#[repr(C)]
pub struct RawGetPtr {
  /// Source.
  pub src: RawValue,
  /// Index.
  pub index: RawValue,
}

/// Raw element pointer calculation.
#[repr(C)]
pub struct RawGetElemPtr {
  /// Source.
  pub src: RawValue,
  /// Index.
  pub index: RawValue,
}

/// Raw binary operation.
#[repr(C)]
pub struct RawBinary {
  /// Operator.
  pub op: RawBinaryOp,
  /// Left-hand side value.
  pub lhs: RawValue,
  /// Right-hand side value.
  pub rhs: RawValue,
}

/// Raw binary operator.
#[repr(u32)]
pub enum RawBinaryOp {
  /// Not equal to.
  NotEq,
  /// Equal to.
  Eq,
  /// Greater than.
  Gt,
  /// Less than.
  Lt,
  /// Greater than or equal to.
  Ge,
  /// Less than or equal to.
  Le,
  /// Addition.
  Add,
  /// Subtraction.
  Sub,
  /// Multiplication.
  Mul,
  /// Division.
  Div,
  /// Modulo.
  Mod,
  /// Bitwise AND.
  And,
  /// Bitwise OR.
  Or,
  /// Bitwise XOR.
  Xor,
  /// Shift left logical.
  Shl,
  /// Shift right logical.
  Shr,
  /// Shift right arithmetic.
  Sar,
}

/// Raw conditional branch.
#[repr(C)]
pub struct RawBranch {
  /// Condition.
  pub cond: RawValue,
  /// Target if condition is `true`.
  pub true_bb: RawBasicBlock,
  /// Target if condition is `false`.
  pub false_bb: RawBasicBlock,
  /// Arguments of `true` target..
  pub true_args: RawSlice,
  /// Arguments of `false` target..
  pub false_args: RawSlice,
}

/// Raw unconditional jump.
#[repr(C)]
pub struct RawJump {
  /// Target.
  pub target: RawBasicBlock,
  /// Arguments of target..
  pub args: RawSlice,
}

/// Raw function call.
#[repr(C)]
pub struct RawCall {
  /// Callee.
  pub callee: RawFunction,
  /// Arguments.
  pub args: RawSlice,
}

/// Raw function return.
#[repr(C)]
pub struct RawReturn {
  /// Return value, null if no return value.
  pub value: RawValue,
}
