use crate::ir::core::{Value, ValueRc};
use crate::ir::structs::{BasicBlock, BasicBlockRc, Program};
use std::cell::Cell;
use std::collections::HashMap;

/// A manager for storing names and allocating unique
/// temporary names of values and basic blocks.
pub struct NameManager {
  value_names: HashMap<*const Value, String>,
  bb_names: HashMap<*const BasicBlock, String>,
}

impl NameManager {
  thread_local! {
    /// Next id for temporary names.
    static NEXT_ID: Cell<usize> = Cell::default();
  }

  /// Creates a new `NameManager`.
  pub fn new() -> Self {
    Self {
      value_names: HashMap::new(),
      bb_names: HashMap::new(),
    }
  }

  /// Resets the id counter.
  pub fn reset_id() {
    Self::NEXT_ID.with(|c| c.set(1));
  }

  /// Gets the name of the specific value.
  pub fn get_value_name(&mut self, value: &ValueRc) -> &str {
    self.value_names.entry(value.as_ref()).or_insert_with(|| {
      if let Some(name) = value.inner().name() {
        name.clone()
      } else {
        Self::next_name()
      }
    })
  }

  /// Gets the name of the specific basic block.
  pub fn get_bb_name<'a>(&'a mut self, bb: &'a BasicBlockRc) -> &str {
    if let Some(name) = bb.name() {
      name
    } else {
      self
        .bb_names
        .entry(bb.as_ref())
        .or_insert_with(Self::next_name)
    }
  }

  /// Generates the next temporary name
  fn next_name() -> String {
    let id = Self::NEXT_ID.with(|c| c.replace(c.get() + 1));
    format!("%{}", id)
  }
}

// /// Koopa IR generator.
// pub trait Generator {
//   /// The output type of all generator methods.
//   type Output;

//   fn generate_on(program: &Program) {
//     for var in program.vars() {
//       //
//     }
//     for func in program.funcs() {
//       //
//     }
//   }
// }
