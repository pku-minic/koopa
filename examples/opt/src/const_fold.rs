use koopa::ir::instructions::{Binary, BinaryOp, Phi};
use koopa::ir::values::{Integer, Undef};
use koopa::ir::{Function, Type, ValueKind, ValueRc};
use koopa::opt::FunctionPass;
use std::rc::Rc;

/// Performs constant folding.
pub struct ConstantFolding;

impl FunctionPass for ConstantFolding {
  fn run_on(&mut self, func: &Function) {
    let mut changed = true;
    while changed {
      changed = false;
      // scan all basic blocks
      for bb in func.inner().bbs() {
        for inst in bb.inner().insts() {
          let ans = match inst.kind() {
            ValueKind::Binary(binary) => self.handle_binary(binary),
            ValueKind::Phi(phi) => self.handle_phi(phi),
            _ => continue,
          };
          // update the current instruction
          if ans.is_some() && inst.inner_mut().replace_all_uses_with(ans) {
            changed = true;
          }
        }
      }
    }
  }
}

impl ConstantFolding {
  pub fn new() -> Self {
    Self
  }

  fn handle_binary(&mut self, binary: &Binary) -> Option<ValueRc> {
    let lhs = binary.lhs().value().unwrap();
    let rhs = binary.rhs().value().unwrap();
    Some(match (lhs.kind(), rhs.kind()) {
      (ValueKind::Integer(l), ValueKind::Integer(r)) => match binary.op() {
        BinaryOp::NotEq => Integer::get((l.value() != r.value()) as i32),
        BinaryOp::Eq => Integer::get((l.value() == r.value()) as i32),
        BinaryOp::Gt => Integer::get((l.value() > r.value()) as i32),
        BinaryOp::Lt => Integer::get((l.value() < r.value()) as i32),
        BinaryOp::Ge => Integer::get((l.value() >= r.value()) as i32),
        BinaryOp::Le => Integer::get((l.value() <= r.value()) as i32),
        BinaryOp::Add => Integer::get(l.value() + r.value()),
        BinaryOp::Sub => Integer::get(l.value() - r.value()),
        BinaryOp::Mul => Integer::get(l.value() * r.value()),
        BinaryOp::Div => {
          if r.value() == 0 {
            Undef::get(Type::get_i32())
          } else {
            Integer::get(l.value() / r.value())
          }
        }
        BinaryOp::Mod => {
          if r.value() == 0 {
            Undef::get(Type::get_i32())
          } else {
            Integer::get(l.value() % r.value())
          }
        }
        BinaryOp::And => Integer::get(l.value() & r.value()),
        BinaryOp::Or => Integer::get(l.value() | r.value()),
        BinaryOp::Xor => Integer::get(l.value() ^ r.value()),
        BinaryOp::Shl => Integer::get(l.value() << r.value()),
        BinaryOp::Shr => Integer::get((l.value() as u32 >> r.value()) as i32),
        BinaryOp::Sar => Integer::get(l.value() >> r.value()),
      },
      (ValueKind::Undef(_), _) | (_, ValueKind::Undef(_)) => Undef::get(Type::get_i32()),
      _ => return None,
    })
  }

  fn handle_phi(&mut self, phi: &Phi) -> Option<ValueRc> {
    // check if all phi operands are the same value
    if phi.oprs().windows(2).all(|it| {
      let pa = it[0].0.value().unwrap();
      let pb = it[1].0.value().unwrap();
      Rc::ptr_eq(&pa, &pb)
    }) {
      phi.oprs().first().unwrap().0.value()
    } else {
      None
    }
  }
}
