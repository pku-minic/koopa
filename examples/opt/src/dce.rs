use koopa::ir::{Function, Value, ValueKind, ValueRc};
use koopa::opt::FunctionPass;
use std::collections::HashSet;

/// Performs dead code elimination.
pub struct DeadCodeElimination {
  worklist: Vec<ValueRc>,
  liveset: HashSet<*const Value>,
}

impl FunctionPass for DeadCodeElimination {
  fn run_on(&mut self, func: &Function) {
    if !func.inner().bbs().is_empty() {
      self.mark(func);
      self.sweep(func);
    }
  }
}

impl DeadCodeElimination {
  pub fn new() -> Self {
    Self {
      worklist: Vec::new(),
      liveset: HashSet::new(),
    }
  }

  fn mark(&mut self, func: &Function) {
    // iterate through all blocks to find critical instructions
    for bb in func.inner().bbs() {
      let bb = bb.inner();
      let mut cur = bb.insts().front();
      while let Some(inst) = cur.clone_pointer() {
        if Self::is_critical_inst(&inst) {
          // mark as undead
          self.liveset.insert(inst.as_ref());
          self.worklist.push(inst);
        }
        cur.move_next();
      }
    }
    // mark more instructions
    while let Some(inst) = self.worklist.pop() {
      // mark all of its operand as undead
      for u in inst.uses() {
        if let Some(value) = u.value() {
          let ptr: *const Value = value.as_ref();
          if !self.liveset.contains(&ptr) && value.is_inst() {
            self.liveset.insert(ptr);
            self.worklist.push(value);
          }
        }
      }
    }
  }

  fn sweep(&mut self, func: &Function) {
    // iterate through all blocks
    for bb in func.inner().bbs() {
      let bb_inner = bb.inner();
      let mut cur = bb_inner.insts().front();
      let mut insts = Vec::new();
      while let Some(inst) = cur.clone_pointer() {
        if !self.liveset.contains(&(inst.as_ref() as *const Value)) {
          insts.push(inst);
        }
        cur.move_next();
      }
      drop(bb_inner);
      for inst in insts {
        bb.inner_mut().remove_inst(inst.as_ref());
      }
    }
  }

  fn is_critical_inst(inst: &ValueRc) -> bool {
    matches!(
      inst.kind(),
      ValueKind::Store(_)
        | ValueKind::Call(_)
        | ValueKind::Branch(_)
        | ValueKind::Jump(_)
        | ValueKind::Return(_)
    )
  }
}
