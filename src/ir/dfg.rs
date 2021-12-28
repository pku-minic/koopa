use crate::ir::builder::{LocalBuilder, ReplaceBuilder};
use crate::ir::entities::{BasicBlock, BasicBlockData, Value, ValueData};
use crate::ir::entities::{FuncTypeMapCell, GlobalValueMapCell};
use crate::ir::idman::{next_bb_id, next_value_id};
use std::collections::HashMap;

/// Data flow graph of a function.
///
/// `DataFlowGraph` holds all data of values ([`ValueData`]) and basic
/// blocks ([`BasicBlockData`]), and maintains their use-define and
/// define-use chain.
pub struct DataFlowGraph {
  pub(crate) globals: GlobalValueMapCell,
  pub(crate) func_tys: FuncTypeMapCell,
  values: HashMap<Value, ValueData>,
  bbs: HashMap<BasicBlock, BasicBlockData>,
}

/// Returns a reference of the value data by the given value handle.
macro_rules! data {
  ($self:ident, $value:expr) => {
    $self
      .globals
      .upgrade()
      .unwrap()
      .borrow_mut()
      .get(&$value)
      .or_else(|| $self.values.get(&$value))
      .expect("value does not exist")
  };
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

impl DataFlowGraph {
  /// Creates a new data flow graph.
  pub(crate) fn new() -> Self {
    Self {
      globals: GlobalValueMapCell::new(),
      func_tys: FuncTypeMapCell::new(),
      values: HashMap::new(),
      bbs: HashMap::new(),
    }
  }

  /// Creates a new value in the current data flow graph.
  /// Returns a [`LocalBuilder`] for building the new local value.
  pub fn new_value(&mut self) -> LocalBuilder {
    LocalBuilder { dfg: self }
  }

  /// Creates a new local value by its value data. Returns the handle of
  /// the created value. This method will be called by [`LocalBuilder`].
  ///
  /// # Panics
  ///
  /// Panics if the given value data uses unexisted values or basic blocks.
  pub(crate) fn new_value_data(&mut self, data: ValueData) -> Value {
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

  /// Replaces the given value with a new value.
  /// Returns a [`ReplaceBuilder`] for building the new value.
  ///
  /// # Panics
  ///
  /// Panics if the given value does not exist.
  pub fn replace_value_with(&mut self, value: Value) -> ReplaceBuilder {
    ReplaceBuilder { dfg: self, value }
  }

  /// Replaces the given value with a new value data.
  /// This method will be called by [`ReplaceBuilder`].
  ///
  /// # Panics
  ///
  /// Panics if the given value does not exist.
  pub(crate) fn replace_value_with_data(&mut self, value: Value, data: ValueData) {
    let old = self.values.remove(&value).unwrap();
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

  /// Returns a mutable reference to the given local value.
  ///
  /// # Panics
  ///
  /// Panics if the given local value does not exist.
  pub fn value_mut(&mut self, value: Value) -> &mut ValueData {
    self.values.get_mut(&value).expect("`value` does not exist")
  }

  /// Returns a reference to the value map.
  pub fn values(&self) -> &HashMap<Value, ValueData> {
    &self.values
  }

  /// Checks if the two given values are equal.
  pub fn value_eq(&self, lhs: Value, rhs: Value) -> bool {
    self.data_eq(data!(self, lhs), data!(self, rhs))
  }

  /// Checks if the two given value data are equal.
  fn data_eq(&self, lhs: &ValueData, rhs: &ValueData) -> bool {
    use crate::ir::entities::ValueKind::*;
    macro_rules! return_if {
      ($e:expr) => {
        if $e {
          return false;
        }
      };
    }
    return_if!(lhs.ty() != rhs.ty());
    match (lhs.kind(), rhs.kind()) {
      (Integer(l), Integer(r)) => return_if!(l.value() != r.value()),
      (ZeroInit(_), ZeroInit(_)) => return true,
      (Undef(_), Undef(_)) => return true,
      (Aggregate(l), Aggregate(r)) => return_if!(l.elems().len() != r.elems().len()),
      (FuncArgRef(l), FuncArgRef(r)) => return_if!(l.index() != r.index()),
      (BlockArgRef(l), BlockArgRef(r)) => return_if!(l.index() != r.index()),
      (Alloc(_), Alloc(_)) => return true,
      (GlobalAlloc(_), GlobalAlloc(_)) => (),
      (Load(_), Load(_)) => (),
      (Store(_), Store(_)) => (),
      (GetPtr(_), GetPtr(_)) => (),
      (GetElemPtr(_), GetElemPtr(_)) => (),
      (Binary(l), Binary(r)) => return_if!(l.op() != r.op()),
      (Branch(l), Branch(r)) => {
        return_if!(
          l.true_bb() != r.true_bb()
            || l.false_bb() != r.false_bb()
            || l.true_args().len() != r.true_args().len()
            || l.false_args().len() != r.false_args().len()
        )
      }
      (Jump(l), Jump(r)) => {
        return_if!(l.target() != r.target() || l.args().len() != r.args().len())
      }
      (Call(l), Call(r)) => {
        return_if!(l.callee() != r.callee() || l.args().len() != r.args().len())
      }
      (Return(l), Return(r)) => return_if!(l.value().xor(r.value()).is_some()),
      _ => return false,
    }
    for (lu, ru) in lhs.kind().value_uses().zip(rhs.kind().value_uses()) {
      return_if!(!self.value_eq(lu, ru));
    }
    true
  }

  /// Creates a new basic block in the current data flow graph.
  /// Returns the handle of the created basic block.
  pub fn new_bb(&mut self, data: BasicBlockData) -> BasicBlock {
    let bb = BasicBlock(next_bb_id());
    self.bbs.insert(bb, data);
    bb
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

  /// Returns a mutable reference of the given basic block.
  ///
  /// # Panics
  ///
  /// Panics if the given basic block does not exist.
  pub fn bb_mut(&mut self, bb: BasicBlock) -> &mut BasicBlockData {
    self.bbs.get_mut(&bb).expect("`bb` does not exist")
  }

  /// Returns a reference to the basic block map.
  pub fn bbs(&self) -> &HashMap<BasicBlock, BasicBlockData> {
    &self.bbs
  }
}
