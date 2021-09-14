use crate::back::generator::{self, value, NameManager, Prefix};
use crate::ir::core::{Value, ValueKind};
use crate::ir::instructions::*;
use crate::ir::structs::{BasicBlock, BasicBlockRef, Function, Program};
use crate::ir::types::{Type, TypeKind};
use std::io::{Result, Write};

/// Visitor for generating Koopa IR into LLVM IR.
#[derive(Default)]
pub struct Visitor;

impl<W: Write> generator::Visitor<W> for Visitor {
  type Output = ();

  fn visit_program(&mut self, w: &mut W, nm: &mut NameManager, program: &Program) -> Result<()> {
    // global variables
    nm.set_prefix(Prefix::Custom {
      named: "@".into(),
      temp: "@_".into(),
    });
    for var in program.vars() {
      self.visit_inst(w, nm, var)?;
    }
    if !program.vars().is_empty() {
      writeln!(w)?;
    }
    // functions
    for (i, func) in program.funcs().iter().enumerate() {
      if i != 0 {
        writeln!(w)?;
      }
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
      write!(w, "declare")?;
    } else {
      write!(w, "define")?;
    }
    // return type
    let ret_ty = match func.ty().kind() {
      TypeKind::Function(_, ret) => ret,
      _ => panic!("invalid function type"),
    };
    write!(w, " ")?;
    self.visit_type(w, ret_ty)?;
    // function name
    write!(w, " {}(", nm.get_func_name(func))?;
    // change prefix
    nm.set_prefix(Prefix::Custom {
      named: "%".into(),
      temp: "%_".into(),
    });
    // parameters
    for (i, param) in func.params().iter().enumerate() {
      if i != 0 {
        write!(w, ", ")?;
      }
      self.visit_type(w, param.ty())?;
      write!(w, " {}", nm.get_value_name(param))?;
    }
    write!(w, ")")?;
    // function body
    if !func.inner().bbs().is_empty() {
      writeln!(w, " {{")?;
      for (i, bb) in func.inner().bbs().iter().enumerate() {
        if i != 0 {
          writeln!(w)?;
        }
        self.visit_bb(w, nm, bb)?;
      }
      writeln!(w, "}}")?;
    } else {
      writeln!(w)?;
    }
    // restore prefix
    nm.set_prefix(Prefix::Custom {
      named: "@".into(),
      temp: "@_".into(),
    });
    Ok(())
  }

  /// Generates the specific basic block.
  fn visit_bb(&mut self, w: &mut impl Write, nm: &mut NameManager, bb: &BasicBlock) -> Result<()> {
    writeln!(w, "{}:", &nm.get_bb_name(bb)[1..])?;
    for inst in bb.inner().insts() {
      write!(w, "  ")?;
      self.visit_inst(w, nm, inst)?;
    }
    Ok(())
  }

  /// Generates the specific instruction.
  fn visit_inst(&mut self, w: &mut impl Write, nm: &mut NameManager, inst: &Value) -> Result<()> {
    // definition
    if !matches!(inst.kind(), ValueKind::Binary(_)) && !inst.ty().is_unit() {
      write!(w, "{} = ", nm.get_value_name(inst))?;
    }
    // content of instruction
    match inst.kind() {
      ValueKind::Alloc(_) => self.visit_alloc(w, inst.ty()),
      ValueKind::GlobalAlloc(v) => self.visit_global_alloc(w, v),
      ValueKind::Load(v) => self.visit_load(w, nm, inst.ty(), v),
      ValueKind::Store(v) => self.visit_store(w, nm, v),
      ValueKind::GetPtr(v) => self.visit_getptr(w, nm, v),
      ValueKind::GetElemPtr(v) => self.visit_getelemptr(w, nm, v),
      ValueKind::Binary(v) => self.visit_binary(w, nm, inst, v),
      ValueKind::Unary(v) => self.visit_unary(w, nm, v),
      ValueKind::Branch(v) => self.visit_branch(w, nm, v),
      ValueKind::Jump(v) => self.visit_jump(w, nm, v),
      ValueKind::Call(v) => self.visit_call(w, nm, inst.ty(), v),
      ValueKind::Return(v) => self.visit_return(w, nm, v),
      ValueKind::Phi(v) => self.visit_phi(w, nm, v),
      _ => panic!("invalid instruction"),
    }?;
    writeln!(w)
  }

  /// Generates allocation.
  fn visit_alloc(&mut self, w: &mut impl Write, ty: &Type) -> Result<()> {
    write!(w, "alloca ")?;
    self.visit_type(w, ty)
  }

  /// Generates global allocation.
  fn visit_global_alloc(&mut self, w: &mut impl Write, alloc: &GlobalAlloc) -> Result<()> {
    let init = alloc.init().value().unwrap();
    write!(w, "global ")?;
    self.visit_const(w, true, init.as_ref())
  }

  /// Generates memory load.
  fn visit_load(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    ty: &Type,
    load: &Load,
  ) -> Result<()> {
    write!(w, "load ")?;
    self.visit_type(w, ty)?;
    write!(w, ", ")?;
    self.visit_value(w, nm, true, value!(load.src()))
  }

  /// Generates memory store.
  fn visit_store(&mut self, w: &mut impl Write, nm: &mut NameManager, store: &Store) -> Result<()> {
    write!(w, "store ")?;
    self.visit_value(w, nm, true, value!(store.value()))?;
    write!(w, ", ")?;
    self.visit_value(w, nm, true, value!(store.dest()))
  }

  /// Generates pointer calculation.
  fn visit_getptr(&mut self, w: &mut impl Write, nm: &mut NameManager, gp: &GetPtr) -> Result<()> {
    write!(w, "getelementptr inbounds ")?;
    let src = gp.src().value().unwrap();
    self.visit_type(
      w,
      match src.ty().kind() {
        TypeKind::Pointer(base) => base,
        _ => panic!("invalid pointer type"),
      },
    )?;
    write!(w, ", ")?;
    self.visit_value(w, nm, true, src.as_ref())?;
    write!(w, ", ")?;
    self.visit_value(w, nm, true, value!(gp.index()))
  }

  /// Generates element pointer calculation.
  fn visit_getelemptr(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    gep: &GetElemPtr,
  ) -> Result<()> {
    write!(w, "getelementptr inbounds ")?;
    let src = gep.src().value().unwrap();
    self.visit_type(
      w,
      match src.ty().kind() {
        TypeKind::Pointer(base) => base,
        _ => panic!("invalid pointer type"),
      },
    )?;
    write!(w, ", ")?;
    self.visit_value(w, nm, true, src.as_ref())?;
    write!(w, ", i32 0, ")?;
    self.visit_value(w, nm, true, value!(gep.index()))
  }

  /// Generates binary operation.
  fn visit_binary(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    value: &Value,
    bin: &Binary,
  ) -> Result<()> {
    // generate definition
    let temp_name = if matches!(
      bin.op(),
      BinaryOp::NotEq | BinaryOp::Eq | BinaryOp::Gt | BinaryOp::Lt | BinaryOp::Ge | BinaryOp::Le
    ) {
      let t = nm.get_temp_value_name();
      write!(w, "{} = ", t)?;
      Some(t)
    } else {
      write!(w, "{} = ", nm.get_value_name(value))?;
      None
    };
    // generate operator
    match bin.op() {
      BinaryOp::NotEq | BinaryOp::Eq => write!(w, "icmp {}", bin.op()),
      BinaryOp::Gt | BinaryOp::Lt | BinaryOp::Ge | BinaryOp::Le => {
        write!(w, "icmp s{}", bin.op())
      }
      BinaryOp::Div => write!(w, "sdiv"),
      BinaryOp::Mod => write!(w, "srem"),
      BinaryOp::Shr => write!(w, "lshr"),
      BinaryOp::Sar => write!(w, "ashr"),
      _ => write!(w, "{}", bin.op()),
    }?;
    write!(w, " i32 ")?;
    // generate lhs & rhs
    self.visit_value(w, nm, false, value!(bin.lhs()))?;
    write!(w, ", ")?;
    self.visit_value(w, nm, false, value!(bin.rhs()))?;
    // generate zero extension if is a compare instruction
    if let Some(t) = temp_name {
      write!(w, "\n  {} = zext i1 {} to i32", nm.get_value_name(value), t)?;
    }
    Ok(())
  }

  /// Generates unary operation.
  fn visit_unary(&mut self, w: &mut impl Write, nm: &mut NameManager, unary: &Unary) -> Result<()> {
    match unary.op() {
      UnaryOp::Neg => write!(w, "sub i32 0, "),
      UnaryOp::Not => write!(w, "xor i32 -1, "),
    }?;
    self.visit_value(w, nm, false, value!(unary.opr()))
  }

  /// Generates branch.
  fn visit_branch(&mut self, w: &mut impl Write, nm: &mut NameManager, br: &Branch) -> Result<()> {
    // generate condition
    let cond = br.cond().value().unwrap();
    let temp = nm.get_temp_value_name();
    write!(w, "{} = trunc i32 ", temp)?;
    self.visit_value(w, nm, false, cond.as_ref())?;
    write!(w, " to i1\n  br i1 {}, label ", temp)?;
    // generate targets
    self.visit_bb_ref(w, nm, br.true_bb())?;
    write!(w, ", label ")?;
    self.visit_bb_ref(w, nm, br.false_bb())
  }

  /// Generates jump.
  fn visit_jump(&mut self, w: &mut impl Write, nm: &mut NameManager, jump: &Jump) -> Result<()> {
    write!(w, "br label ")?;
    self.visit_bb_ref(w, nm, jump.target())
  }

  /// Generates function call.
  fn visit_call(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    ty: &Type,
    call: &Call,
  ) -> Result<()> {
    write!(w, "call ")?;
    self.visit_type(w, ty)?;
    write!(
      w,
      " {}(",
      nm.get_func_name(call.callee().upgrade().unwrap().as_ref())
    )?;
    for (i, arg) in call.args().iter().enumerate() {
      if i != 0 {
        write!(w, ", ")?;
      }
      self.visit_value(w, nm, true, value!(arg))?;
    }
    write!(w, ")")
  }

  /// Generates function return.
  fn visit_return(&mut self, w: &mut impl Write, nm: &mut NameManager, ret: &Return) -> Result<()> {
    write!(w, "ret ")?;
    if let Some(val) = ret.value().value() {
      self.visit_value(w, nm, true, val.as_ref())
    } else {
      write!(w, "void")
    }
  }

  /// Generates phi function.
  fn visit_phi(&mut self, w: &mut impl Write, nm: &mut NameManager, phi: &Phi) -> Result<()> {
    let mut oprs = phi.oprs().iter();
    // the first operand
    let (first_use, first_bb) = oprs.next().unwrap();
    let first_opr = first_use.value().unwrap();
    write!(w, "phi ")?;
    self.visit_type(w, first_opr.ty())?;
    write!(w, " [ ")?;
    self.visit_value(w, nm, false, first_opr.as_ref())?;
    write!(w, ", ")?;
    self.visit_bb_ref(w, nm, first_bb)?;
    write!(w, " ]")?;
    // the rest operands
    for (opr, bb) in oprs {
      write!(w, ", [ ")?;
      self.visit_value(w, nm, false, value!(opr))?;
      write!(w, ", ")?;
      self.visit_bb_ref(w, nm, bb)?;
      write!(w, " ]")?;
    }
    Ok(())
  }

  /// Generates the specific value.
  fn visit_value(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    with_ty: bool,
    value: &Value,
  ) -> Result<()> {
    if value.is_const() {
      self.visit_const(w, with_ty, value)
    } else {
      if with_ty {
        self.visit_type(w, value.ty())?;
        write!(w, " ")?;
      }
      write!(w, "{}", nm.get_value_name(value))
    }
  }

  /// Generates the specific constant.
  fn visit_const(&mut self, w: &mut impl Write, with_ty: bool, value: &Value) -> Result<()> {
    if with_ty {
      self.visit_type(w, value.ty())?;
      write!(w, " ")?;
    }
    match value.kind() {
      ValueKind::Integer(v) => write!(w, "{}", v.value()),
      ValueKind::ZeroInit(_) => write!(w, "zeroinitializer"),
      ValueKind::Undef(_) => write!(w, "undef"),
      ValueKind::Aggregate(v) => {
        write!(w, "[")?;
        for (i, elem) in v.elems().iter().enumerate() {
          if i != 0 {
            write!(w, ", ")?;
          }
          self.visit_const(w, with_ty, value!(elem))?;
        }
        write!(w, "]")
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

  /// Generates the specific type.
  fn visit_type(&mut self, w: &mut impl Write, ty: &Type) -> Result<()> {
    match ty.kind() {
      TypeKind::Int32 => write!(w, "i32"),
      TypeKind::Unit => write!(w, "void"),
      TypeKind::Array(base, len) => {
        write!(w, "[{} x ", len)?;
        self.visit_type(w, base)?;
        write!(w, "]")
      }
      TypeKind::Pointer(base) => {
        self.visit_type(w, base)?;
        write!(w, "*")
      }
      // actually a function pointer
      TypeKind::Function(params, ret) => {
        self.visit_type(w, ret)?;
        write!(w, " (")?;
        for (i, param) in params.iter().enumerate() {
          if i != 0 {
            write!(w, ", ")?;
          }
          self.visit_type(w, param)?;
        }
        write!(w, ")*")
      }
    }
  }
}

#[cfg(test)]
mod test {
  use crate::back::LlvmGenerator;
  use crate::front::Driver;
  use std::str;

  #[test]
  fn dump_ir() {
    let driver: Driver<_> = r#"
      global @x = alloc [i32, 10], zeroinit

      fun @test(@i: i32): i32 {
      %entry:
        %0 = getptr @x, 0
        store {1, 2, 3, 4, 5, 0, 0, 0, 0, 10}, %0
        %1 = getelemptr @x, @i
        %2 = load %1
        %3 = mul %2, 7
        ret %3
      }
    "#
    .into();
    let mut gen = LlvmGenerator::new(Vec::new());
    gen
      .generate_on(&driver.generate_program().unwrap())
      .unwrap();
    assert_eq!(
      str::from_utf8(&gen.writer()).unwrap(),
      r#"@x = global [10 x i32] zeroinitializer

define i32 @test(i32 %i) {
_entry:
  %_0 = getelementptr inbounds [10 x i32], [10 x i32]* @x, i32 0
  store [10 x i32] [i32 1, i32 2, i32 3, i32 4, i32 5, i32 0, i32 0, i32 0, i32 0, i32 10], [10 x i32]* %_0
  %_1 = getelementptr inbounds [10 x i32], [10 x i32]* @x, i32 0, i32 %i
  %_2 = load i32, i32* %_1
  %_3 = mul i32 %_2, 7
  ret i32 %_3
}
"#
    );
  }

  #[test]
  fn dump_ir_phi() {
    let driver: Driver<_> = r#"
      decl @getint(): i32

      fun @main(): i32 {
      %entry:
        %ans_0 = call @getint()
        jump %while_entry

      %while_entry:
        %ind_var_0 = phi i32 (0, %entry), (%ind_var_1, %while_body)
        %ans_1 = phi i32 (%ans_0, %entry), (%ans_2, %while_body)
        %cond = lt %ind_var_0, 10
        br %cond, %while_body, %while_end

      %while_body:
        %ans_2 = add %ans_1, %ind_var_0
        %ind_var_1 = add %ind_var_0, 1
        jump %while_entry

      %while_end:
        ret %ans_1
      }
    "#
    .into();
    let mut gen = LlvmGenerator::new(Vec::new());
    gen
      .generate_on(&driver.generate_program().unwrap())
      .unwrap();
    assert_eq!(
      str::from_utf8(&gen.writer()).unwrap(),
      r#"declare i32 @getint()

define i32 @main() {
_entry:
  %_ans_0 = call i32 @getint()
  br label %_while_entry

_while_entry:
  %_ind_var_0 = phi i32 [ 0, %_entry ], [ %_ind_var_1, %_while_body ]
  %_ans_1 = phi i32 [ %_ans_0, %_entry ], [ %_ans_2, %_while_body ]
  %_0 = icmp slt i32 %_ind_var_0, 10
  %_cond = zext i1 %_0 to i32
  %_1 = trunc i32 %_cond to i1
  br i1 %_1, label %_while_body, label %_while_end

_while_body:
  %_ans_2 = add i32 %_ans_1, %_ind_var_0
  %_ind_var_1 = add i32 %_ind_var_0, 1
  br label %_while_entry

_while_end:
  ret i32 %_ans_1
}
"#
    );
  }

  #[test]
  fn dump_nested_loop() {
    let src = r#"decl @getint(): i32

fun @main(): i32 {
%args_0:
  %0 = call @getint()
  %1 = call @getint()
  jump %while_cond_2

%while_cond_2:
  %2 = phi i32 (0, %args_0), (%3, %while_end_5)
  %4 = phi i32 (0, %args_0), (%5, %while_end_5)
  %6 = lt %4, %1
  br %6, %while_body_3, %while_end_1

%while_body_3:
  jump %while_cond_4

%while_end_1:
  ret %2

%while_cond_4:
  %3 = phi i32 (%2, %while_body_3), (%7, %while_body_6)
  %8 = phi i32 (0, %while_body_3), (%9, %while_body_6)
  %10 = lt %8, %0
  br %10, %while_body_6, %while_end_5

%while_body_6:
  %11 = add %3, %4
  %7 = add %11, %8
  %9 = add %8, 1
  jump %while_cond_4

%while_end_5:
  %5 = add %4, 1
  jump %while_cond_2
}
"#;
    let driver: Driver<_> = src.into();
    let mut gen = LlvmGenerator::new(Vec::new());
    gen
      .generate_on(&driver.generate_program().unwrap())
      .unwrap();
    assert_eq!(
      str::from_utf8(&gen.writer()).unwrap(),
      r#"declare i32 @getint()

define i32 @main() {
_args_0:
  %_0 = call i32 @getint()
  %_1 = call i32 @getint()
  br label %_while_cond_2

_while_cond_2:
  %_2 = phi i32 [ 0, %_args_0 ], [ %_3, %_while_end_5 ]
  %_4 = phi i32 [ 0, %_args_0 ], [ %_5, %_while_end_5 ]
  %_6 = icmp slt i32 %_4, %_1
  %_7 = zext i1 %_6 to i32
  %_8 = trunc i32 %_7 to i1
  br i1 %_8, label %_while_body_3, label %_while_end_1

_while_body_3:
  br label %_while_cond_4

_while_end_1:
  ret i32 %_2

_while_cond_4:
  %_3 = phi i32 [ %_2, %_while_body_3 ], [ %_9, %_while_body_6 ]
  %_10 = phi i32 [ 0, %_while_body_3 ], [ %_11, %_while_body_6 ]
  %_12 = icmp slt i32 %_10, %_0
  %_13 = zext i1 %_12 to i32
  %_14 = trunc i32 %_13 to i1
  br i1 %_14, label %_while_body_6, label %_while_end_5

_while_body_6:
  %_15 = add i32 %_3, %_4
  %_9 = add i32 %_15, %_10
  %_11 = add i32 %_10, 1
  br label %_while_cond_4

_while_end_5:
  %_5 = add i32 %_4, 1
  br label %_while_cond_2
}
"#
    );
  }
}
