use std::cell::Cell;

/// Type of `Value` identifier.
///
/// The IDs of `Value`s are unique, but two different IDs may correspond to
/// the same `Value`. For example, two integer constants are the same but
/// have different IDs.
pub(crate) type ValueId = u32;

/// The value of `ValueId` should start from 1,
/// because we want to use `NonZeroU32` to enable some
/// memory layout optimization.
const VALUE_ID_STARTS_FROM: ValueId = 1;

/// Type of `BasicBlock` identifier.
///
/// The IDs of `BasicBlock`s are unique.
pub(crate) type BasicBlockId = u32;

/// The value of `BasicBlockId` should start from 1,
/// because we want to use `NonZeroU32` to enable some
/// memory layout optimization.
const BASIC_BLOCK_ID_STARTS_FROM: BasicBlockId = 1;

/// Type of `Function` identifier.
///
/// The IDs of `Function`s are unique.
pub(crate) type FunctionId = u32;

/// The value of `FunctionId` should start from 1,
/// because we want to use `NonZeroU32` to enable some
/// memory layout optimization.
const FUNCTION_ID_STARTS_FROM: FunctionId = 1;

thread_local! {
  /// The next value ID.
  static NEXT_VALUE_ID: Cell<ValueId> = Cell::new(VALUE_ID_STARTS_FROM);
  /// The next basic block ID.
  static NEXT_BASIC_BLOCK_ID: Cell<BasicBlockId> = Cell::new(BASIC_BLOCK_ID_STARTS_FROM);
  /// The next function ID.
  static NEXT_FUNCTION_ID: Cell<FunctionId> = Cell::new(FUNCTION_ID_STARTS_FROM);
}

/// Gets the next value ID.
pub(crate) fn next_value_id() -> ValueId {
  NEXT_VALUE_ID.with(|id| id.replace(id.get() + 1))
}

/// Gets the next basic block ID.
pub(crate) fn next_bb_id() -> BasicBlockId {
  NEXT_BASIC_BLOCK_ID.with(|id| id.replace(id.get() + 1))
}

/// Gets the next function ID.
pub(crate) fn next_func_id() -> FunctionId {
  NEXT_FUNCTION_ID.with(|id| id.replace(id.get() + 1))
}
