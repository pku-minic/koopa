use koopa::ir::{Function, FunctionData, Value, ValueKind, builder_traits::*};
use koopa::opt::FunctionPass;
use std::collections::{HashMap, HashSet};

/// Performs dead code elimination.
pub struct DeadCodeElimination {
  worklist: Vec<Value>,
  liveset: HashSet<Value>,
}

impl FunctionPass for DeadCodeElimination {
  fn run_on(&mut self, _: Function, data: &mut FunctionData) {
    let mut changed = true;
    while changed {
      self.mark(data);
      changed = self.sweep(data);
      changed |= self.opt_bb_params(data);
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

  fn mark(&mut self, data: &FunctionData) {
    self.liveset.clear();
    self.worklist.clear();
    // iterate through all values to find critical instructions
    for (v, value) in data.dfg().values() {
      if Self::is_critical_inst(value.kind()) {
        self.liveset.insert(*v);
        self.worklist.push(*v);
      }
    }
    // mark more instructions
    while let Some(inst) = self.worklist.pop() {
      // mark all of its operand as undead
      for u in data.dfg().value(inst).kind().value_uses() {
        if !u.is_global()
          && !self.liveset.contains(&u)
          && data.dfg().value(u).kind().is_local_inst()
        {
          self.liveset.insert(u);
          self.worklist.push(u);
        }
      }
    }
  }

  fn sweep(&mut self, data: &mut FunctionData) -> bool {
    // remove instructions in layout
    let mut removed = Vec::new();
    let mut bb_cur = data.layout_mut().bbs_mut().cursor_front_mut();
    while let Some(bb) = bb_cur.node_mut() {
      let mut inst_cur = bb.insts_mut().cursor_front_mut();
      while let Some(inst) = inst_cur.key() {
        if !self.liveset.contains(inst) {
          removed.push(*inst);
          inst_cur.remove_current();
        } else {
          inst_cur.move_next();
        }
      }
      bb_cur.move_next();
    }

    let changed = !removed.is_empty();

    // if we have two dead instructions, but some is used by another dead one
    // then is not ok to remove_value directly
    // we have to replace with `undef` to cut the connections first.
    for &v in &removed {
      let ty = data.dfg().value(v).ty().clone();
      data.dfg_mut().replace_value_with(v).undef(ty);
    }

    for v in removed {
      data.dfg_mut().remove_value(v);
    }

    changed
  }

  fn opt_bb_params(&self, data: &mut FunctionData) -> bool {
    // get map: bb that should be handled ->
    //          (index of param that should be removed -> param value)
    let bbs: HashMap<_, _> = data
      .dfg()
      .bbs()
      .iter()
      .filter_map(|(b, bb)| {
        let unused: HashMap<_, _> = bb
          .params()
          .iter()
          .enumerate()
          .filter_map(|(i, p)| data.dfg().value(*p).used_by().is_empty().then_some((i, *p)))
          .collect();
        (!unused.is_empty()).then_some((*b, unused))
      })
      .collect();
    let changed = !bbs.is_empty();
    // remove unused parameters of all detected basic blocks
    bbs.iter().for_each(|(b, m)| {
      let mut index = 0;
      data.dfg_mut().bb_mut(*b).params_mut().retain(|_| {
        index += 1;
        !m.contains_key(&(index - 1))
      });
      m.values().for_each(|param| {
        data.dfg_mut().remove_value(*param);
      });
      let params = data.dfg().bb(*b).params().to_vec();
      for (index, param) in params.into_iter().enumerate() {
        data.dfg_mut().update_value(param, |value| {
          let ValueKind::BlockArgRef(arg) = value.kind_mut() else {
            unreachable!("expected block parameter");
          };
          *arg.index_mut() = index;
        });
      }
    });
    // update arguments of all related branch/jump instructions
    bbs.into_iter().for_each(|(b, m)| {
      let users = data.dfg().bb(b).used_by().clone();
      users.into_iter().for_each(|user| {
        // Keep the DFG use lists in sync, and let the next liveness sweep
        // remove newly dead instructions from both the DFG and the layout.
        data.dfg_mut().update_value(user, |inst| {
          let retain_args = |args: &mut Vec<Value>| {
            let mut index = 0;
            args.retain(|_| {
              let retained = !m.contains_key(&index);
              index += 1;
              retained
            });
          };
          match inst.kind_mut() {
            ValueKind::Branch(br) => {
              if br.true_bb() == b {
                retain_args(br.true_args_mut());
              }
              if br.false_bb() == b {
                retain_args(br.false_args_mut());
              }
            }
            ValueKind::Jump(jump) => retain_args(jump.args_mut()),
            _ => panic!("invalid branch/jump instruction"),
          }
        });
      });
    });
    changed
  }

  fn is_critical_inst(kind: &ValueKind) -> bool {
    matches!(
      kind,
      ValueKind::Store(_)
        | ValueKind::Call(_)
        | ValueKind::Branch(_)
        | ValueKind::Jump(_)
        | ValueKind::Return(_)
    )
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use koopa::back::KoopaGenerator;
  use koopa::front::Driver;

  #[test]
  fn global_operands_are_not_looked_up_in_the_local_dfg() {
    let mut program = Driver::from(
      "global @g = alloc i32, 42
      decl @consume(*i32)
      fun @main(): i32 {
      %entry:
        store 42, @g
        call @consume(@g)
        %answer = load @g
        ret %answer
      }",
    )
    .generate_program()
    .unwrap();
    let mut pass = DeadCodeElimination::new();
    for (&func, data) in program.funcs_mut() {
      pass.run_on(func, data);
    }
    let mut generator = KoopaGenerator::new(Vec::new());
    generator.generate_on(&program).unwrap();
    let source = String::from_utf8(generator.writer()).unwrap();
    assert!(source.contains("store 42, @g"));
    assert!(source.contains("call @consume(@g)"));
    assert!(source.contains("load @g"));
    Driver::from(source).generate_program().unwrap();
  }

  #[test]
  fn removing_block_parameters_updates_indices_and_liveness() {
    let mut program = Driver::from(
      "global @g = alloc i32, 42
      decl @consume(*i32)
      fun @f(%input: i32): i32 {
      %entry:
        %dead = add 1, 2
        jump %merge(%dead, @g, %input)
      %merge(%unused: i32, %pointer: *i32, %answer: i32):
        call @consume(%pointer)
        ret %answer
      }",
    )
    .generate_program()
    .unwrap();
    let func = *program.func_layout().last().unwrap();
    let data = program.func_mut(func);
    DeadCodeElimination::new().run_on(func, data);
    let merge = *data.layout().bbs().back_key().unwrap();
    assert_eq!(data.dfg().bb(merge).params().len(), 2);
    for (index, param) in data.dfg().bb(merge).params().iter().enumerate() {
      let ValueKind::BlockArgRef(arg) = data.dfg().value(*param).kind() else {
        panic!("expected block parameter");
      };
      assert_eq!(arg.index(), index);
    }
    assert!(
      !data
        .dfg()
        .values()
        .values()
        .any(|v| matches!(v.kind(), ValueKind::Binary(_)))
    );
    let mut generator = KoopaGenerator::new(Vec::new());
    generator.generate_on(&program).unwrap();
    Driver::from(String::from_utf8(generator.writer()).unwrap())
      .generate_program()
      .unwrap();
  }
}
