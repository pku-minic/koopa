use koopa::ir::{BinaryOp, Function, FunctionData, Type, ValueKind, builder_traits::*};
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
              BinaryOp::Add => Some(l.value().wrapping_add(r.value())),
              BinaryOp::Sub => Some(l.value().wrapping_sub(r.value())),
              BinaryOp::Mul => Some(l.value().wrapping_mul(r.value())),
              BinaryOp::Div => l.value().checked_div(r.value()),
              BinaryOp::Mod => l.value().checked_rem(r.value()),
              BinaryOp::And => Some(l.value() & r.value()),
              BinaryOp::Or => Some(l.value() | r.value()),
              BinaryOp::Xor => Some(l.value() ^ r.value()),
              BinaryOp::Shl => l.value().checked_shl(r.value() as u32),
              BinaryOp::Shr => (l.value() as u32)
                .checked_shr(r.value() as u32)
                .map(|v| v as i32),
              BinaryOp::Sar => l.value().checked_shr(r.value() as u32),
            },
            (ValueKind::Undef(_), _) | (_, ValueKind::Undef(_)) => None,
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
          if !value.kind().is_const() || !ans.is_none_or(|v| data.dfg().data_eq(&v, value)) {
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

#[cfg(test)]
mod tests {
  use super::*;
  use koopa::front::Driver;

  #[test]
  fn folds_i32_arithmetic_without_host_panics() {
    for (expression, expected) in [
      ("add 2147483647, 1", Some(i32::MIN)),
      ("sub -2147483648, 1", Some(i32::MAX)),
      ("mul 1073741824, 4", Some(0)),
      ("div 1, 0", None),
      ("div -2147483648, -1", None),
      ("mod -2147483648, -1", None),
      ("shl 1, 32", None),
      ("shr 1, -1", None),
      ("sar 1, 32", None),
      ("add undef, 1", None),
      ("add 1, undef", None),
    ] {
      let source = format!("fun @main(): i32 {{ %entry: %result = {expression} ret %result }}");
      let mut program = Driver::from(source).generate_program().unwrap();
      let func = program.func_layout()[0];
      let data = program.func_mut(func);
      ConstantFolding::new().run_on(func, data);
      let ret = *data
        .layout()
        .bbs()
        .front_node()
        .unwrap()
        .insts()
        .back_key()
        .unwrap();
      let ValueKind::Return(ret) = data.dfg().value(ret).kind() else {
        panic!("expected return");
      };
      match (data.dfg().value(ret.value().unwrap()).kind(), expected) {
        (ValueKind::Integer(value), Some(expected)) => assert_eq!(value.value(), expected),
        (ValueKind::Undef(_), None) => {}
        _ => panic!("unexpected folded value for {expression}"),
      }
    }
  }
}
