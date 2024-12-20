//! Value/basic block/function ID manager.

use std::num::NonZeroU32;
use std::sync::atomic::{AtomicU32, Ordering};

/// Type of `Value` identifier.
///
/// The IDs of `Value`s are unique, but two different IDs may correspond to
/// the same `Value`. For example, two integer constants are the same but
/// have different IDs.
pub(in crate::ir) type ValueId = NonZeroU32;

/// The value of `ValueId` (global value) should start from 1,
/// because we want to use `NonZeroU32` to enable some
/// memory layout optimization.
const GLOBAL_VALUE_ID_STARTS_FROM: ValueId = unsafe { NonZeroU32::new_unchecked(1) };

/// The value of `ValueId` (local value) should start from 0x40000000,
/// because we want to use `NonZeroU32` to enable some
/// memory layout optimization.
const LOCAL_VALUE_ID_STARTS_FROM: ValueId = unsafe { NonZeroU32::new_unchecked(0x40000000) };

/// Type of `BasicBlock` identifier.
///
/// The IDs of `BasicBlock`s are unique.
pub(in crate::ir) type BasicBlockId = NonZeroU32;

/// The value of `BasicBlockId` should start from 1,
/// because we want to use `NonZeroU32` to enable some
/// memory layout optimization.
const BB_ID_STARTS_FROM: BasicBlockId = unsafe { NonZeroU32::new_unchecked(1) };

/// Type of `Function` identifier.
///
/// The IDs of `Function`s are unique.
pub(in crate::ir) type FunctionId = NonZeroU32;

/// The value of `FunctionId` should start from 1,
/// because we want to use `NonZeroU32` to enable some
/// memory layout optimization.
const FUNC_ID_STARTS_FROM: FunctionId = unsafe { NonZeroU32::new_unchecked(1) };

/// Returns the next global value ID.
pub(in crate::ir) fn next_global_value_id() -> ValueId {
  static NEXT_GLOBAL_VALUE_ID: AtomicU32 = AtomicU32::new(GLOBAL_VALUE_ID_STARTS_FROM.get());
  let id = NEXT_GLOBAL_VALUE_ID.fetch_add(1, Ordering::Relaxed);
  unsafe { NonZeroU32::new_unchecked(id) }
}

/// Returns the next local value ID.
pub(in crate::ir) fn next_local_value_id() -> ValueId {
  static NEXT_LOCAL_VALUE_ID: AtomicU32 = AtomicU32::new(LOCAL_VALUE_ID_STARTS_FROM.get());
  let id = NEXT_LOCAL_VALUE_ID.fetch_add(1, Ordering::Relaxed);
  unsafe { NonZeroU32::new_unchecked(id) }
}

/// Returns `true` if the given value ID is a global value ID.
pub(in crate::ir) fn is_global_id(value: ValueId) -> bool {
  value >= GLOBAL_VALUE_ID_STARTS_FROM && value < LOCAL_VALUE_ID_STARTS_FROM
}

/// Returns the next basic block ID.
pub(in crate::ir) fn next_bb_id() -> BasicBlockId {
  static NEXT_BB_ID: AtomicU32 = AtomicU32::new(BB_ID_STARTS_FROM.get());
  let id = NEXT_BB_ID.fetch_add(1, Ordering::Relaxed);
  unsafe { NonZeroU32::new_unchecked(id) }
}

/// Returns the next function ID.
pub(in crate::ir) fn next_func_id() -> FunctionId {
  static NEXT_FUNC_ID: AtomicU32 = AtomicU32::new(FUNC_ID_STARTS_FROM.get());
  let id = NEXT_FUNC_ID.fetch_add(1, Ordering::Relaxed);
  unsafe { NonZeroU32::new_unchecked(id) }
}
