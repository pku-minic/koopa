use koopa::ir::{builder_traits::*, BinaryOp, Function, FunctionData, Type, ValueKind};
use koopa::opt::FunctionPass;

/// Performs constant folding.
pub struct ConstantFolding;

impl FunctionPass for ConstantFolding {
  fn run_on(&mut self, _: Function, data: &mut FunctionData) {
    // handle all binary instructions
    while self.eval_const(data) {}
    // handle all basic block parameters
    self.eval_bb_params(data);
  }
}

impl ConstantFolding {
  pub fn new() -> Self {
    Self
  }

  fn eval_const(&self, data: &mut FunctionData) -> bool {
    // find all evaluable binary instructions and evaluate
    let mut evaluated = Vec::new();
    for (v, value) in data.dfg().values() {
      let ans = match value.kind() {
        ValueKind::Binary(bin) => {
          let lhs = data.dfg().value(bin.lhs()).kind();
          let rhs = data.dfg().value(bin.rhs()).kind();
          match (lhs, rhs) {
            (ValueKind::Integer(l), ValueKind::Integer(r)) => match bin.op() {
              BinaryOp::NotEq => Some((l.value() != r.value()) as i32),
              BinaryOp::Eq => Some((l.value() == r.value()) as i32),
              BinaryOp::Gt => Some((l.value() > r.value()) as i32),
              BinaryOp::Lt => Some((l.value() < r.value()) as i32),
              BinaryOp::Ge => Some((l.value() >= r.value()) as i32),
              BinaryOp::Le => Some((l.value() <= r.value()) as i32),
              BinaryOp::Add => Some(l.value() + r.value()),
              BinaryOp::Sub => Some(l.value() - r.value()),
              BinaryOp::Mul => Some(l.value() * r.value()),
              BinaryOp::Div => (r.value() != 0).then(|| l.value() / r.value()),
              BinaryOp::Mod => (r.value() != 0).then(|| l.value() % r.value()),
              BinaryOp::And => Some(l.value() & r.value()),
              BinaryOp::Or => Some(l.value() | r.value()),
              BinaryOp::Xor => Some(l.value() ^ r.value()),
              BinaryOp::Shl => Some(l.value() << r.value()),
              BinaryOp::Shr => Some((l.value() as u32 >> r.value()) as i32),
              BinaryOp::Sar => Some(l.value() >> r.value()),
            },
            (ValueKind::Undef(_), _) => todo!(),
            (_, ValueKind::Undef(_)) => todo!(),
            _ => continue,
          }
        }
        _ => continue,
      };
      evaluated.push((*v, ans, data.layout().parent_bb(*v).unwrap()));
    }
    // updated values
    let changed = !evaluated.is_empty();
    // replace the evaluated instructions
    for (v, ans, _) in &evaluated {
      let builder = data.dfg_mut().replace_value_with(*v);
      if let Some(v) = ans {
        builder.integer(*v);
      } else {
        builder.undef(Type::get_i32());
      }
    }
    // remove constant values in instruction layout
    for (v, _, bb) in evaluated {
      data.layout_mut().bb_mut(bb).insts_mut().remove(&v);
    }
    changed
  }

  fn eval_bb_params(&self, data: &mut FunctionData) {
    let mut bb_params = Vec::new();
    for (b, bb) in data.dfg().bbs() {
      // collect parameters that can be evaluated in the current basic block
      let mut evaluated = Vec::new();
      'outer: for i in 0..bb.params().len() {
        let mut ans = None;
        // check if all corresponding arguments are constant
        for user in bb.used_by() {
          // get the argument value handle
          let value = match data.dfg().value(*user).kind() {
            ValueKind::Branch(branch) => {
              if branch.true_bb() == *b {
                branch.true_args()[i]
              } else {
                branch.false_args()[i]
              }
            }
            ValueKind::Jump(jump) => jump.args()[i],
            _ => panic!("invalid branch/jump instruction"),
          };
          // check if is constant
          let value = data.dfg().value(value);
          if !value.kind().is_const() || !ans.map_or(true, |v| data.dfg().data_eq(&v, value)) {
            continue 'outer;
          }
          ans = Some(value.clone());
        }
        evaluated.push((i, ans.unwrap()));
      }
      if !evaluated.is_empty() {
        bb_params.push((*b, evaluated));
      }
    }
    // update basic block parameters
    for (bb, evals) in bb_params {
      // replace all parameters to constants
      for (i, value) in evals {
        let p = data.dfg().bb(bb).params()[i];
        let param = data.dfg().value(p).clone();
        data.dfg_mut().replace_value_with(p).raw(value);
        let p = data.dfg_mut().new_value().raw(param);
        data.dfg_mut().bb_mut(bb).params_mut()[i] = p;
      }
    }
  }
}
