//! Layout ([`Layout`]), basic blocklist and instruction list
//! related implementations.

use crate::ir::entities::{BasicBlock, Value};
use key_node_list::{KeyNodeList, Map, impl_node};
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::{HashMap, hash_map::Entry};
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
///
/// Removing a block preserves its instruction list and detaches its
/// instructions from the layout. Inserting the returned node into a block
/// list preserves those instructions and updates their parent block.
/// Inserting a node whose instructions already occur in the destination
/// layout panics without changing the destination list.
pub type BasicBlockList = KeyNodeList<BasicBlock, BasicBlockNode, BasicBlockMap>;

type InstBBCell = Weak<RefCell<HashMap<Value, BasicBlock>>>;

#[derive(Clone)]
struct BlockAttachment {
  bb: BasicBlock,
  inst_bb: InstBBCell,
}

type AttachmentCell = Rc<RefCell<Option<BlockAttachment>>>;

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

  fn get<Q>(&self, k: &Q) -> Option<&BasicBlockNode>
  where
    BasicBlock: Borrow<Q>,
    Q: ?Sized + Hash + Eq,
  {
    self.map.get(k)
  }

  fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut BasicBlockNode>
  where
    BasicBlock: Borrow<Q>,
    Q: ?Sized + Hash + Eq,
  {
    self.map.get_mut(k)
  }

  fn insert<T>(&mut self, k: BasicBlock, v: T) -> Result<(), (BasicBlock, T)>
  where
    T: Into<BasicBlockNode>,
  {
    if let Entry::Vacant(e) = self.map.entry(k) {
      let mut node = v.into();
      node.attach(k, self.inst_bb.clone());
      e.insert(node);
      Ok(())
    } else {
      Err((k, v))
    }
  }

  fn remove_entry<Q>(&mut self, k: &Q) -> Option<(BasicBlock, BasicBlockNode)>
  where
    BasicBlock: Borrow<Q>,
    Q: ?Sized + Hash + Eq,
  {
    self.map.remove_entry(k).map(|(key, mut node)| {
      node.detach();
      (key, node)
    })
  }
}

/// The node in [`BasicBlockList`] that holds the instruction list
/// ([`InstList`]) in the basic block.
///
/// A removed node can be edited independently of its original layout,
/// including after that layout has been dropped.
pub struct BasicBlockNode {
  insts: InstList,
  attachment: AttachmentCell,
  prev: Option<BasicBlock>,
  next: Option<BasicBlock>,
}

impl_node!(BasicBlockNode { Key = BasicBlock, prev = prev, next = next });

impl BasicBlockNode {
  fn new() -> Self {
    let attachment = Rc::new(RefCell::new(None));
    Self {
      insts: InstList::with_map(InstMap::new(attachment.clone())),
      attachment,
      prev: None,
      next: None,
    }
  }

  fn attach(&mut self, bb: BasicBlock, inst_bb: InstBBCell) {
    self.detach();
    if let Some(index) = inst_bb.upgrade() {
      let mut index = index.as_ref().borrow_mut();
      assert!(
        self.insts.keys().all(|inst| !index.contains_key(inst)),
        "instruction already belongs to a basic block in this layout"
      );
      index.extend(self.insts.keys().map(|inst| (*inst, bb)));
    }
    *self.attachment.as_ref().borrow_mut() = Some(BlockAttachment { bb, inst_bb });
  }

  fn detach(&mut self) {
    let attachment = self.attachment.as_ref().borrow_mut().take();
    if let Some(index) = attachment.and_then(|a| a.inst_bb.upgrade()) {
      let mut index = index.as_ref().borrow_mut();
      for inst in self.insts.keys() {
        index.remove(inst);
      }
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
  /// Creates an empty basic block node that is not attached to a layout.
  fn from(_: ()) -> Self {
    Self::new()
  }
}

impl Drop for BasicBlockNode {
  fn drop(&mut self) {
    self.detach();
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
/// Insertion returns an error if the instruction already belongs to any
/// basic block in the same layout.
pub type InstList = KeyNodeList<Value, InstNode, InstMap>;

/// The underlying hash map of the [`InstList`].
pub struct InstMap {
  attachment: AttachmentCell,
  map: HashMap<Value, InstNode>,
}

impl InstMap {
  fn new(attachment: AttachmentCell) -> Self {
    Self {
      attachment,
      map: HashMap::new(),
    }
  }
}

impl Map<Value, InstNode> for InstMap {
  fn len(&self) -> usize {
    self.map.len()
  }

  fn clear(&mut self) {
    if let Some(index) = self
      .attachment
      .as_ref()
      .borrow()
      .as_ref()
      .and_then(|a| a.inst_bb.upgrade())
    {
      let mut index = index.as_ref().borrow_mut();
      for inst in self.map.keys() {
        index.remove(inst);
      }
    }
    self.map.clear()
  }

  fn get<Q>(&self, k: &Q) -> Option<&InstNode>
  where
    Value: Borrow<Q>,
    Q: ?Sized + Hash + Eq,
  {
    self.map.get(k)
  }

  fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut InstNode>
  where
    Value: Borrow<Q>,
    Q: ?Sized + Hash + Eq,
  {
    self.map.get_mut(k)
  }

  fn insert<T>(&mut self, k: Value, v: T) -> Result<(), (Value, T)>
  where
    T: Into<InstNode>,
  {
    if self.contains_key(&k) {
      return Err((k, v));
    }
    let attachment = self.attachment.as_ref().borrow().clone();
    let parent = attachment.and_then(|a| a.inst_bb.upgrade().map(|index| (a.bb, index)));
    if let Some((_, index)) = &parent
      && index.as_ref().borrow().contains_key(&k)
    {
      return Err((k, v));
    }
    let node = v.into();
    self.map.insert(k, node);
    if let Some((bb, index)) = parent {
      index.as_ref().borrow_mut().insert(k, bb);
    }
    Ok(())
  }

  fn remove_entry<Q>(&mut self, k: &Q) -> Option<(Value, InstNode)>
  where
    Value: Borrow<Q>,
    Q: ?Sized + Hash + Eq,
  {
    let kv = self.map.remove_entry(k);
    if kv.is_some()
      && let Some(index) = self
        .attachment
        .as_ref()
        .borrow()
        .as_ref()
        .and_then(|a| a.inst_bb.upgrade())
    {
      index.as_ref().borrow_mut().remove(k);
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

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ir::{Program, Type, builder_traits::*};

  fn handles() -> (Program, [BasicBlock; 3], [Value; 3]) {
    let mut program = Program::new();
    let func = program.new_func_def("@test".into(), Vec::new(), Type::get_unit());
    let dfg = program.func_mut(func).dfg_mut();
    let bbs = std::array::from_fn(|_| dfg.new_bb().basic_block(None));
    let insts = std::array::from_fn(|_| dfg.new_value().alloc(Type::get_i32()));
    (program, bbs, insts)
  }

  #[test]
  fn reinserting_blocks_preserves_instruction_order() {
    let (_program, [first, second, _], [a, b, c]) = handles();
    let mut layout = Layout::new();
    layout.bbs_mut().extend([first, second]);
    layout.bb_mut(first).insts_mut().extend([a, b]);
    layout.bb_mut(second).insts_mut().push_key_back(c).unwrap();

    let (key, node) = layout.bbs_mut().remove(&first).unwrap();
    assert_eq!(layout.parent_bb(a), None);
    assert_eq!(layout.parent_bb(b), None);
    assert_eq!(layout.parent_bb(c), Some(second));
    assert_eq!(node.insts().keys().copied().collect::<Vec<_>>(), [a, b]);
    assert!(layout.bbs_mut().push_back(key, node).is_ok());
    assert_eq!(
      layout.bbs().keys().copied().collect::<Vec<_>>(),
      [second, first]
    );
    assert_eq!(
      layout.bbs()[&first]
        .insts()
        .keys()
        .copied()
        .collect::<Vec<_>>(),
      [a, b]
    );
    assert_eq!(layout.parent_bb(a), Some(first));
    assert_eq!(layout.parent_bb(b), Some(first));
  }

  #[test]
  fn clearing_instructions_and_blocks_updates_parent_index() {
    let (_program, [first, second, _], [a, b, c]) = handles();
    let mut layout = Layout::new();
    layout.bbs_mut().extend([first, second]);
    layout.bb_mut(first).insts_mut().extend([a, b]);
    layout.bb_mut(second).insts_mut().push_key_back(c).unwrap();

    layout.bb_mut(first).insts_mut().clear();
    assert_eq!(layout.parent_bb(a), None);
    assert_eq!(layout.parent_bb(b), None);
    assert_eq!(layout.parent_bb(c), Some(second));
    layout.bb_mut(first).insts_mut().push_key_back(a).unwrap();
    assert_eq!(layout.parent_bb(a), Some(first));
    layout.bbs_mut().clear();
    assert!(layout.bbs().is_empty());
    assert_eq!(layout.parent_bb(a), None);
    assert_eq!(layout.parent_bb(c), None);
  }

  #[test]
  fn removed_nodes_do_not_change_the_old_parent_index() {
    let (_program, [first, second, _], [a, b, c]) = handles();
    let mut layout = Layout::new();
    layout.bbs_mut().extend([first, second]);
    layout.bb_mut(first).insts_mut().extend([a, b]);
    let (_, mut node) = layout.bbs_mut().remove(&first).unwrap();
    assert_eq!(layout.parent_bb(a), None);
    assert_eq!(layout.parent_bb(b), None);
    layout.bb_mut(second).insts_mut().extend([a, b, c]);
    node.insts_mut().remove(&a).unwrap();
    node.insts_mut().clear();
    node.insts_mut().push_key_back(c).unwrap();
    drop(node);
    for inst in [a, b, c] {
      assert_eq!(layout.parent_bb(inst), Some(second));
    }
  }

  #[test]
  fn detached_nodes_outlive_layouts_and_can_move_to_another_layout() {
    let (_program, [first, second, third], [a, b, c]) = handles();
    let mut old = Layout::new();
    old.bbs_mut().push_key_back(first).unwrap();
    old.bb_mut(first).insts_mut().push_key_back(a).unwrap();
    let (_, mut node) = old.bbs_mut().remove(&first).unwrap();
    drop(old);
    node.insts_mut().remove(&a).unwrap();
    node.insts_mut().extend([a, b]);
    node.insts_mut().clear();
    node.insts_mut().push_key_back(a).unwrap();

    let mut new = Layout::new();
    new.bbs_mut().push_key_back(second).unwrap();
    new.bb_mut(second).insts_mut().push_key_back(c).unwrap();
    assert!(new.bbs_mut().push_back(third, node).is_ok());
    assert_eq!(new.parent_bb(a), Some(third));
    assert_eq!(new.parent_bb(c), Some(second));
    new.bb_mut(third).insts_mut().push_key_back(b).unwrap();
    assert_eq!(new.parent_bb(b), Some(third));
    assert_eq!(
      new.bbs()[&third]
        .insts()
        .keys()
        .copied()
        .collect::<Vec<_>>(),
      [a, b]
    );
  }

  #[test]
  fn transferring_blocks_updates_only_the_destination_layout() {
    let (_program, [first, second, third], [a, b, _]) = handles();
    let mut source = Layout::new();
    source.bbs_mut().extend([first, second]);
    source.bb_mut(first).insts_mut().push_key_back(a).unwrap();
    let (_, node) = source.bbs_mut().remove(&first).unwrap();
    source.bb_mut(second).insts_mut().push_key_back(a).unwrap();

    let mut destination = Layout::new();
    assert!(destination.bbs_mut().push_back(third, node).is_ok());
    destination
      .bb_mut(third)
      .insts_mut()
      .push_key_back(b)
      .unwrap();
    assert_eq!(source.parent_bb(a), Some(second));
    assert_eq!(source.parent_bb(b), None);
    assert_eq!(destination.parent_bb(a), Some(third));
    assert_eq!(destination.parent_bb(b), Some(third));
    destination.bbs_mut().clear();
    assert_eq!(source.parent_bb(a), Some(second));
    assert_eq!(destination.parent_bb(a), None);
    assert_eq!(destination.parent_bb(b), None);
  }

  #[test]
  fn instructions_cannot_belong_to_two_blocks() {
    let (_program, [first, second, _], [a, _, _]) = handles();
    let mut layout = Layout::new();
    layout.bbs_mut().extend([first, second]);
    layout.bb_mut(first).insts_mut().push_key_back(a).unwrap();
    assert_eq!(layout.bb_mut(second).insts_mut().push_key_back(a), Err(a));
    assert_eq!(layout.parent_bb(a), Some(first));
    assert!(layout.bbs()[&second].insts().is_empty());
    let (inst, node) = layout.bb_mut(first).insts_mut().remove(&a).unwrap();
    assert_eq!(layout.parent_bb(a), None);
    assert!(
      layout
        .bb_mut(second)
        .insts_mut()
        .push_back(inst, node)
        .is_ok()
    );
    assert_eq!(layout.parent_bb(a), Some(second));
  }

  #[test]
  fn duplicate_block_keys_return_the_original_node() {
    let (_program, [first, second, _], [a, b, _]) = handles();
    let mut layout = Layout::new();
    layout.bbs_mut().push_key_back(first).unwrap();
    layout.bb_mut(first).insts_mut().push_key_back(a).unwrap();
    let mut node = BasicBlockNode::from(());
    node.insts_mut().push_key_back(b).unwrap();
    let Err((key, node)) = layout.bbs_mut().push_back(first, node) else {
      panic!("duplicate block key was accepted");
    };
    assert_eq!(key, first);
    assert_eq!(node.insts().keys().copied().collect::<Vec<_>>(), [b]);
    assert_eq!(layout.parent_bb(a), Some(first));
    assert_eq!(layout.parent_bb(b), None);
    assert!(layout.bbs_mut().push_back(second, node).is_ok());
    assert_eq!(layout.parent_bb(b), Some(second));
  }

  #[test]
  fn conflicting_block_insertion_preserves_the_destination() {
    let (_program, [first, second, _], [a, b, _]) = handles();
    let mut layout = Layout::new();
    layout.bbs_mut().push_key_back(first).unwrap();
    layout.bb_mut(first).insts_mut().push_key_back(a).unwrap();
    let mut node = BasicBlockNode::from(());
    node.insts_mut().extend([b, a]);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      let _ = layout.bbs_mut().push_back(second, node);
    }));
    assert!(result.is_err());
    assert_eq!(layout.bbs().keys().copied().collect::<Vec<_>>(), [first]);
    assert_eq!(layout.parent_bb(a), Some(first));
    assert_eq!(layout.parent_bb(b), None);
  }
}
