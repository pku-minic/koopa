use crate::back::generator::{self, NameManager};
use crate::ir::core::{Value, ValueKind};
use crate::ir::instructions::*;
use crate::ir::structs::{BasicBlock, BasicBlockRef, Function, Program};
use crate::ir::types::Type;
use std::io::{Result, Write};

/// Visitor for generating Koopa IR structures into text formatted Koopa IR.
#[derive(Default)]
pub struct Visitor;

/// Gets the value reference of the specific use.
macro_rules! value {
  ($use:expr) => {
    $use.value().unwrap().as_ref()
  };
}

impl<W: Write> generator::Visitor<W> for Visitor {
  type Output = ();

  fn visit_program(&mut self, w: &mut W, nm: &mut NameManager, program: &Program) -> Result<()> {
    for var in program.vars() {
      write!(w, "global ")?;
      self.visit_inst(w, nm, var)?;
    }
    writeln!(w)?;
    for func in program.funcs() {
      self.visit_func(w, nm, func)?;
    }
    Ok(())
  }
}

impl Visitor {
  /// Generates the specific function.
  fn visit_func(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &Function,
  ) -> Result<()> {
    // header
    if func.inner().bbs().is_empty() {
      write!(w, "decl")?;
    } else {
      write!(w, "fun")?;
    }
    // function name
    write!(w, " {}(", nm.get_func_name(func))?;
    // parameters
    for (i, param) in func.params().iter().enumerate() {
      if i != 0 {
        write!(w, ", ")?;
      }
      write!(w, "{}: {}", nm.get_value_name(param), param.ty())?;
    }
    write!(w, ")")?;
    // return type
    if func.ty().is_unit() {
      write!(w, ": {}", func.ty())?;
    }
    // function body
    if !func.inner().bbs().is_empty() {
      writeln!(w, " {{")?;
      for (i, bb) in func.inner().bbs().iter().enumerate() {
        if i != 0 {
          writeln!(w)?;
        }
        self.visit_bb(w, nm, bb)?;
      }
      writeln!(w, "}}")
    } else {
      writeln!(w)
    }
  }

  /// Generates the specific basic block.
  fn visit_bb(&mut self, w: &mut impl Write, nm: &mut NameManager, bb: &BasicBlock) -> Result<()> {
    writeln!(w, "{}:", nm.get_bb_name(bb))?;
    for inst in bb.inner().insts() {
      write!(w, "  ")?;
      self.visit_inst(w, nm, inst)?;
    }
    Ok(())
  }

  /// Generates the specific instruction.
  fn visit_inst(&mut self, w: &mut impl Write, nm: &mut NameManager, inst: &Value) -> Result<()> {
    // definition
    if !inst.ty().is_unit() {
      write!(w, "{} = ", nm.get_value_name(inst))?;
    }
    // content of instruction
    match inst.kind() {
      ValueKind::Alloc(_) => self.visit_alloc(w, inst.ty()),
      ValueKind::GlobalAlloc(v) => self.visit_global_alloc(w, v),
      ValueKind::Load(v) => self.visit_load(w, nm, v),
      ValueKind::Store(v) => self.visit_store(w, nm, v),
      ValueKind::GetPtr(v) => self.visit_getptr(w, nm, v),
      ValueKind::GetElemPtr(v) => self.visit_getelemptr(w, nm, v),
      ValueKind::Binary(v) => self.visit_binary(w, nm, v),
      ValueKind::Unary(v) => self.visit_unary(w, nm, v),
      ValueKind::Branch(v) => self.visit_branch(w, nm, v),
      ValueKind::Jump(v) => self.visit_jump(w, nm, v),
      ValueKind::Call(v) => self.visit_call(w, nm, v),
      ValueKind::Return(v) => self.visit_return(w, nm, v),
      ValueKind::Phi(v) => self.visit_phi(w, nm, v),
      _ => panic!("invalid instruction"),
    }?;
    writeln!(w)
  }

  /// Generates allocation.
  fn visit_alloc(&mut self, w: &mut impl Write, ty: &Type) -> Result<()> {
    write!(w, "alloc {}", ty)
  }

  /// Generates global allocation.
  fn visit_global_alloc(&mut self, w: &mut impl Write, alloc: &GlobalAlloc) -> Result<()> {
    let init = alloc.init().value().unwrap();
    write!(w, "alloc {}, ", init.ty())?;
    self.visit_const(w, init.as_ref())
  }

  /// Generates memory load.
  fn visit_load(&mut self, w: &mut impl Write, nm: &mut NameManager, load: &Load) -> Result<()> {
    write!(w, "load ")?;
    self.visit_value(w, nm, value!(load.src()))
  }

  /// Generates memory store.
  fn visit_store(&mut self, w: &mut impl Write, nm: &mut NameManager, store: &Store) -> Result<()> {
    write!(w, "store ")?;
    self.visit_value(w, nm, value!(store.dest()))?;
    write!(w, ", ")?;
    self.visit_value(w, nm, value!(store.value()))
  }

  /// Generates pointer calculation.
  fn visit_getptr(&mut self, w: &mut impl Write, nm: &mut NameManager, gp: &GetPtr) -> Result<()> {
    write!(w, "getptr ")?;
    self.visit_value(w, nm, value!(gp.src()))?;
    write!(w, ", ")?;
    self.visit_value(w, nm, value!(gp.index()))
  }

  /// Generates element pointer calculation.
  fn visit_getelemptr(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    gep: &GetElemPtr,
  ) -> Result<()> {
    write!(w, "getelemptr ")?;
    self.visit_value(w, nm, value!(gep.src()))?;
    write!(w, ", ")?;
    self.visit_value(w, nm, value!(gep.index()))
  }

  /// Generates binary operation.
  fn visit_binary(&mut self, w: &mut impl Write, nm: &mut NameManager, bin: &Binary) -> Result<()> {
    write!(w, "{} ", bin.op())?;
    self.visit_value(w, nm, value!(bin.lhs()))?;
    write!(w, ", ")?;
    self.visit_value(w, nm, value!(bin.rhs()))
  }

  /// Generates unary operation.
  fn visit_unary(&mut self, w: &mut impl Write, nm: &mut NameManager, unary: &Unary) -> Result<()> {
    write!(w, "{} ", unary.op())?;
    self.visit_value(w, nm, value!(unary.opr()))
  }

  /// Generates branch.
  fn visit_branch(&mut self, w: &mut impl Write, nm: &mut NameManager, br: &Branch) -> Result<()> {
    write!(w, "br ")?;
    self.visit_value(w, nm, value!(br.cond()))?;
    write!(w, ", ")?;
    self.visit_bb_ref(w, nm, br.true_bb())?;
    write!(w, ", ")?;
    self.visit_bb_ref(w, nm, br.false_bb())
  }

  /// Generates jump.
  fn visit_jump(&mut self, w: &mut impl Write, nm: &mut NameManager, jump: &Jump) -> Result<()> {
    write!(w, "jump ")?;
    self.visit_bb_ref(w, nm, jump.target())
  }

  /// Generates function call.
  fn visit_call(&mut self, w: &mut impl Write, nm: &mut NameManager, call: &Call) -> Result<()> {
    write!(
      w,
      "call {}(",
      nm.get_func_name(call.callee().upgrade().unwrap().as_ref())
    )?;
    for (i, arg) in call.args().iter().enumerate() {
      if i != 0 {
        write!(w, ", ")?;
      }
      self.visit_value(w, nm, value!(arg))?;
    }
    write!(w, ")")
  }

  /// Generates function return.
  fn visit_return(&mut self, w: &mut impl Write, nm: &mut NameManager, ret: &Return) -> Result<()> {
    write!(w, "ret")?;
    if let Some(val) = ret.value().value() {
      write!(w, " ")?;
      self.visit_value(w, nm, val.as_ref())?;
    }
    Ok(())
  }

  /// Generates phi function.
  fn visit_phi(&mut self, w: &mut impl Write, nm: &mut NameManager, phi: &Phi) -> Result<()> {
    let mut oprs = phi.oprs().iter();
    // the first operand
    let (first_use, first_bb) = oprs.next().unwrap();
    let first_opr = first_use.value().unwrap();
    write!(w, "phi {} (", first_opr.ty())?;
    self.visit_value(w, nm, first_opr.as_ref())?;
    write!(w, ", ")?;
    self.visit_bb_ref(w, nm, first_bb)?;
    write!(w, ")")?;
    // the rest operands
    for (opr, bb) in oprs {
      write!(w, ", (")?;
      self.visit_value(w, nm, value!(opr))?;
      write!(w, ", ")?;
      self.visit_bb_ref(w, nm, bb)?;
      write!(w, ")")?;
    }
    Ok(())
  }

  /// Generates the specific value.
  fn visit_value(&mut self, w: &mut impl Write, nm: &mut NameManager, value: &Value) -> Result<()> {
    if value.is_const() {
      self.visit_const(w, value)
    } else {
      write!(w, "{}", nm.get_value_name(value))
    }
  }

  /// Generates the specific constant.
  fn visit_const(&mut self, w: &mut impl Write, value: &Value) -> Result<()> {
    match value.kind() {
      ValueKind::Integer(v) => write!(w, "{}", v.value()),
      ValueKind::ZeroInit(_) => write!(w, "zeroinit"),
      ValueKind::Undef(_) => write!(w, "undef"),
      ValueKind::Aggregate(v) => {
        for elem in v.elems() {
          self.visit_const(w, value!(elem))?;
        }
        Ok(())
      }
      _ => panic!("invalid constant"),
    }
  }

  /// Generates the specific basic block reference.
  fn visit_bb_ref(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    bb: &BasicBlockRef,
  ) -> Result<()> {
    write!(w, "{}", nm.get_bb_name(bb.upgrade().unwrap().as_ref()))
  }
}
