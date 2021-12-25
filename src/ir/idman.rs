use std::cell::Cell;
use std::num::NonZeroU32;

/// Type of `Value` identifier.
///
/// The IDs of `Value`s are unique, but two different IDs may correspond to
/// the same `Value`. For example, two integer constants are the same but
/// have different IDs.
pub(crate) type ValueId = NonZeroU32;

/// The value of `ValueId` should start from 1,
/// because we want to use `NonZeroU32` to enable some
/// memory layout optimization.
const VALUE_ID_STARTS_FROM: ValueId = unsafe { NonZeroU32::new_unchecked(1) };

/// Type of `BasicBlock` identifier.
///
/// The IDs of `BasicBlock`s are unique.
pub(crate) type BasicBlockId = NonZeroU32;

/// The value of `BasicBlockId` should start from 1,
/// because we want to use `NonZeroU32` to enable some
/// memory layout optimization.
const BB_ID_STARTS_FROM: BasicBlockId = unsafe { NonZeroU32::new_unchecked(1) };

/// Type of `Function` identifier.
///
/// The IDs of `Function`s are unique.
pub(crate) type FunctionId = NonZeroU32;

/// The value of `FunctionId` should start from 1,
/// because we want to use `NonZeroU32` to enable some
/// memory layout optimization.
const FUNC_ID_STARTS_FROM: FunctionId = unsafe { NonZeroU32::new_unchecked(1) };

thread_local! {
  /// The next value ID.
  static NEXT_VALUE_ID: Cell<ValueId> = Cell::new(VALUE_ID_STARTS_FROM);
  /// The next basic block ID.
  static NEXT_BB_ID: Cell<BasicBlockId> = Cell::new(BB_ID_STARTS_FROM);
  /// The next function ID.
  static NEXT_FUNC_ID: Cell<FunctionId> = Cell::new(FUNC_ID_STARTS_FROM);
}

/// Gets the next value ID.
pub(crate) fn next_value_id() -> ValueId {
  NEXT_VALUE_ID.with(|id| id.replace(unsafe { NonZeroU32::new_unchecked(id.get().get() + 1) }))
}

/// Gets the next basic block ID.
pub(crate) fn next_bb_id() -> BasicBlockId {
  NEXT_BB_ID.with(|id| id.replace(unsafe { NonZeroU32::new_unchecked(id.get().get() + 1) }))
}

/// Gets the next function ID.
pub(crate) fn next_func_id() -> FunctionId {
  NEXT_FUNC_ID.with(|id| id.replace(unsafe { NonZeroU32::new_unchecked(id.get().get() + 1) }))
}
