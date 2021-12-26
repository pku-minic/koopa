use crate::ir::entities::{BasicBlock, BasicBlockData, GlobalValueMapCell, Value, ValueData};
use crate::ir::idman::{next_bb_id, next_value_id};
use std::collections::HashMap;

/// Data flow graph of a function.
///
/// `DataFlowGraph` holds all data of values ([`ValueData`]) and basic
/// blocks ([`BasicBlockData`]), and maintains their use-define and
/// define-use chain.
pub struct DataFlowGraph {
  pub(crate) globals: GlobalValueMapCell,
  values: HashMap<Value, ValueData>,
  bbs: HashMap<BasicBlock, BasicBlockData>,
}

/// Returns a mutable reference of the value data by the given value handle.
macro_rules! data_mut {
  ($self:ident, $value:expr) => {
    $self
      .globals
      .upgrade()
      .unwrap()
      .borrow_mut()
      .get_mut(&$value)
      .or_else(|| $self.values.get_mut(&$value))
      .expect("value does not exist")
  };
}

// TODO: handle value uses blocks
impl DataFlowGraph {
  /// Creates a new data flow graph.
  pub(crate) fn new() -> Self {
    Self {
      globals: GlobalValueMapCell::new(),
      values: HashMap::new(),
      bbs: HashMap::new(),
    }
  }

  /// Creates a new value in the current data flow graph.
  /// Returns the handle of the created value.
  ///
  /// # Panics
  ///
  /// Panics if the given value data uses unexisted values or basic blocks.
  pub fn new_value(&mut self, data: ValueData) -> Value {
    let value = Value(next_value_id());
    for v in data.kind().value_uses() {
      data_mut!(self, v).used_by.insert(value);
    }
    for bb in data.kind().bb_uses() {
      self.bb_mut(bb).used_by.insert(value);
    }
    self.values.insert(value, data);
    value
  }

  /// Replaces the given value with a new value data. Returns the old
  /// value data.
  ///
  /// # Panics
  ///
  /// Panics if the given value does not exist.
  pub fn replace_value_with(&mut self, value: Value, data: ValueData) -> ValueData {
    let old = self.values.remove(&value).expect("`value` does not exist");
    for v in old.kind().value_uses() {
      data_mut!(self, v).used_by.remove(&value);
    }
    for bb in old.kind().bb_uses() {
      self.bb_mut(bb).used_by.remove(&value);
    }
    for v in data.kind().value_uses() {
      data_mut!(self, v).used_by.insert(value);
    }
    for bb in data.kind().bb_uses() {
      self.bb_mut(bb).used_by.insert(value);
    }
    self.values.insert(value, data);
    old
  }

  /// Removes the given value. Returns the corresponding value data.
  ///
  /// # Panics
  ///
  /// Panics if the given value does not exist, or the removed value is
  /// currently used by other values.
  pub fn remove_value(&mut self, value: Value) -> ValueData {
    let data = self.values.remove(&value).expect("`value` does not exist");
    assert!(data.used_by.is_empty(), "`value` is used by other values");
    for v in data.kind().value_uses() {
      data_mut!(self, v).used_by.remove(&value);
    }
    for bb in data.kind().bb_uses() {
      self.bb_mut(bb).used_by.remove(&value);
    }
    data
  }

  /// Returns a reference to the value map.
  pub fn values(&self) -> &HashMap<Value, ValueData> {
    &self.values
  }

  /// Creates a new basic block in the current data flow graph.
  /// Returns the handle of the created basic block.
  pub fn new_bb(&mut self, data: BasicBlockData) -> BasicBlock {
    let bb = BasicBlock(next_bb_id());
    self.bbs.insert(bb, data);
    bb
  }

  /// Returns a mutable reference of the given basic block.
  ///
  /// # Panics
  ///
  /// Panics if the given basic block does not exist.
  pub fn bb_mut(&mut self, bb: BasicBlock) -> &mut BasicBlockData {
    self.bbs.get_mut(&bb).expect("`bb` does not exist")
  }

  /// Removes the given basic block. Returns the corresponding
  /// basic block data.
  ///
  /// # Panics
  ///
  /// Panics if the given basic block does not exist.
  pub fn remove_bb(&mut self, bb: BasicBlock) -> BasicBlockData {
    self.bbs.remove(&bb).expect("`bb` does not exist")
  }

  /// Returns a reference to the basic block map.
  pub fn bbs(&self) -> &HashMap<BasicBlock, BasicBlockData> {
    &self.bbs
  }
}
