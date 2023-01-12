//! Layout ([`Layout`]), basic blocklist and instruction list
//! related implementations.

use crate::ir::entities::{BasicBlock, Value};
use key_node_list::{impl_node, KeyNodeList, Map};
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::{hash_map::Entry, HashMap};
use std::hash::Hash;
use std::rc::{Rc, Weak};

/// Layout of instructions and basic blocks in a function.
///
/// `Layout` maintains the order of instructions ([`Value`]) and basic
/// blocks ([`BasicBlock`]) in function.
pub struct Layout {
  bbs: BasicBlockList,
  inst_bb: Rc<RefCell<HashMap<Value, BasicBlock>>>,
}

impl Layout {
  /// Creates a new layout.
  pub fn new() -> Self {
    Self::default()
  }

  /// Returns a reference to the basic block list.
  pub fn bbs(&self) -> &BasicBlockList {
    &self.bbs
  }

  /// Returns a mutable reference to the basic block list.
  pub fn bbs_mut(&mut self) -> &mut BasicBlockList {
    &mut self.bbs
  }

  /// Returns a mutable reference to the basic block node
  /// by the given basic block handle.
  ///
  /// # Panics
  ///
  /// Panics if the given basic block does not exist.
  pub fn bb_mut(&mut self, bb: BasicBlock) -> &mut BasicBlockNode {
    self.bbs.node_mut(&bb).expect("`bb` does not exist")
  }

  /// Returns the entry basic block of the function, returns `None` if
  /// the function is a declaration.
  pub fn entry_bb(&self) -> Option<BasicBlock> {
    self.bbs.front_key().copied()
  }

  /// Returns the parent basic block of the given instruction, returns
  /// `None` if the given instruction is not in the current layout.
  pub fn parent_bb(&self, inst: Value) -> Option<BasicBlock> {
    self.inst_bb.as_ref().borrow().get(&inst).copied()
  }
}

impl Default for Layout {
  fn default() -> Self {
    let inst_bb = Rc::new(RefCell::new(HashMap::new()));
    Self {
      bbs: BasicBlockList::with_map(BasicBlockMap::new(Rc::downgrade(&inst_bb))),
      inst_bb,
    }
  }
}

/// Basic block list, stores the order of all basic blocks in the function.
///
/// Basic block list is a [`KeyNodeList`], with the key is [`BasicBlock`],
/// and the node is [`BasicBlockNode`], the latter holds an [`InstList`] that
/// stores the order of all instructions in the basic block.
///
/// You can push or insert new basic blocks to the list by calling
/// [`push_key_front`](BasicBlockList::push_key_front),
/// [`push_key_back`](BasicBlockList::push_key_back),
/// [`insert_key_before`](key_node_list::CursorMut::insert_key_before) or
/// [`insert_key_after`](key_node_list::CursorMut::insert_key_after).
pub type BasicBlockList = KeyNodeList<BasicBlock, BasicBlockNode, BasicBlockMap>;

type InstBBCell = Weak<RefCell<HashMap<Value, BasicBlock>>>;

/// The underlying hash map of the [`BasicBlockList`].
pub struct BasicBlockMap {
  inst_bb: InstBBCell,
  map: HashMap<BasicBlock, BasicBlockNode>,
}

impl BasicBlockMap {
  fn new(inst_bb: InstBBCell) -> Self {
    Self {
      inst_bb,
      map: HashMap::new(),
    }
  }
}

impl Map<BasicBlock, BasicBlockNode> for BasicBlockMap {
  fn len(&self) -> usize {
    self.map.len()
  }

  fn clear(&mut self) {
    self.map.clear()
  }

  fn get<Q: ?Sized>(&self, k: &Q) -> Option<&BasicBlockNode>
  where
    BasicBlock: Borrow<Q>,
    Q: Hash + Eq,
  {
    self.map.get(k)
  }

  fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut BasicBlockNode>
  where
    BasicBlock: Borrow<Q>,
    Q: Hash + Eq,
  {
    self.map.get_mut(k)
  }

  fn insert<T>(&mut self, k: BasicBlock, v: T) -> Result<(), (BasicBlock, T)>
  where
    T: Into<BasicBlockNode>,
  {
    if let Entry::Vacant(e) = self.map.entry(k) {
      let node = BasicBlockNode::new(k, self.inst_bb.clone());
      e.insert(node);
      Ok(())
    } else {
      Err((k, v))
    }
  }

  fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(BasicBlock, BasicBlockNode)>
  where
    BasicBlock: Borrow<Q>,
    Q: Hash + Eq,
  {
    self.map.remove_entry(k)
  }
}

/// The node in [`BasicBlockList`] that holds the instruction list
/// ([`InstList`]) in the basic block.
pub struct BasicBlockNode {
  insts: InstList,
  prev: Option<BasicBlock>,
  next: Option<BasicBlock>,
}

impl_node!(BasicBlockNode { Key = BasicBlock, prev = prev, next = next });

impl BasicBlockNode {
  fn new(bb: BasicBlock, inst_bb: InstBBCell) -> Self {
    Self {
      insts: InstList::with_map(InstMap::new(bb, inst_bb)),
      prev: None,
      next: None,
    }
  }

  /// Returns a reference to the instruction list.
  pub fn insts(&self) -> &InstList {
    &self.insts
  }

  /// Returns a mutable reference to the instruction list.
  pub fn insts_mut(&mut self) -> &mut InstList {
    &mut self.insts
  }
}

impl From<()> for BasicBlockNode {
  /// This function will always panic, so do not call this.
  ///
  /// This function is declared to fit the type bounds of methods in
  /// [`KeyNodeList`] such as [`push_key_front`](KeyNodeList::push_key_front).
  /// The actual construction of `BasicBlockNode` is done in
  /// [`BasicBlockMap`].
  fn from(_: ()) -> Self {
    panic!("shound not be called")
  }
}

/// Instruction list, stores the order of all instructions in the basic
/// block.
///
/// Instruction list is a [`KeyNodeList`], with the key is [`Value`],
/// and the node is [`InstNode`].
///
/// You can push or insert new instructions to the list by calling
/// [`push_key_front`](BasicBlockList::push_key_front),
/// [`push_key_back`](BasicBlockList::push_key_back),
/// [`insert_key_before`](key_node_list::CursorMut::insert_key_before) or
/// [`insert_key_after`](key_node_list::CursorMut::insert_key_after).
pub type InstList = KeyNodeList<Value, InstNode, InstMap>;

/// The underlying hash map of the [`InstList`].
pub struct InstMap {
  bb: BasicBlock,
  inst_bb: InstBBCell,
  map: HashMap<Value, InstNode>,
}

impl InstMap {
  fn new(bb: BasicBlock, inst_bb: InstBBCell) -> Self {
    Self {
      bb,
      inst_bb,
      map: HashMap::new(),
    }
  }
}

impl Map<Value, InstNode> for InstMap {
  fn len(&self) -> usize {
    self.map.len()
  }

  fn clear(&mut self) {
    self.map.clear()
  }

  fn get<Q: ?Sized>(&self, k: &Q) -> Option<&InstNode>
  where
    Value: Borrow<Q>,
    Q: Hash + Eq,
  {
    self.map.get(k)
  }

  fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut InstNode>
  where
    Value: Borrow<Q>,
    Q: Hash + Eq,
  {
    self.map.get_mut(k)
  }

  fn insert<T>(&mut self, k: Value, v: T) -> Result<(), (Value, T)>
  where
    T: Into<InstNode>,
  {
    if self.contains_key(&k) {
      Err((k, v))
    } else {
      self
        .inst_bb
        .upgrade()
        .unwrap()
        .as_ref()
        .borrow_mut()
        .insert(k, self.bb);
      self.map.insert(k, v.into());
      Ok(())
    }
  }

  fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(Value, InstNode)>
  where
    Value: Borrow<Q>,
    Q: Hash + Eq,
  {
    let kv = self.map.remove_entry(k);
    if kv.is_some() {
      self
        .inst_bb
        .upgrade()
        .unwrap()
        .as_ref()
        .borrow_mut()
        .remove(k);
    }
    kv
  }
}

/// The node in [`InstList`].
pub struct InstNode {
  prev: Option<Value>,
  next: Option<Value>,
}

impl_node!(InstNode { Key = Value, prev = prev, next = next });

impl From<()> for InstNode {
  fn from(_: ()) -> Self {
    Self {
      prev: None,
      next: None,
    }
  }
}
