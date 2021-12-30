use crate::back::{self, NameManager};
use crate::ir::entities::{FunctionData, ValueData};
use crate::ir::layout::BasicBlockNode;
use crate::ir::values::*;
use crate::ir::{BasicBlock, Program, Type, TypeKind, Value, ValueKind};
use crate::value;
use std::io::{Result, Write};

/// Visitor for generating Koopa IR structures into text formatted Koopa IR.
#[derive(Default)]
pub struct Visitor;

impl<W: Write> back::Visitor<W> for Visitor {
  type Output = ();

  fn visit(&mut self, w: &mut W, nm: &mut NameManager, program: &Program) -> Result<()> {
    for var in program.borrow_values().values() {
      self.visit_global_inst(w, nm, program, var)?;
    }
    if !program.borrow_values().is_empty() {
      writeln!(w)?;
    }
    for (i, func) in program.funcs().values().enumerate() {
      if i != 0 {
        writeln!(w)?;
      }
      nm.enter_func_scope();
      self.visit_func(w, nm, program, func)?;
      nm.exit_func_scope();
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
    program: &Program,
    func: &FunctionData,
  ) -> Result<()> {
    // header
    let is_decl = func.dfg().bbs().is_empty();
    if is_decl {
      write!(w, "decl")?;
    } else {
      write!(w, "fun")?;
    }
    // function name
    write!(w, " {}(", nm.func_name(func))?;
    // unwrap function type
    let (param_ty, ret_ty) = match func.ty().kind() {
      TypeKind::Function(param, ret) => (param, ret),
      _ => panic!("invalid function type"),
    };
    // parameters
    if is_decl {
      for (i, ty) in param_ty.iter().enumerate() {
        if i != 0 {
          write!(w, ", ")?;
        }
        write!(w, "{}", ty)?;
      }
    } else {
      for (i, param) in func.params().iter().enumerate() {
        if i != 0 {
          write!(w, ", ")?;
        }
        let param = value!(func, *param);
        write!(w, "{}: {}", nm.value_name(param), param.ty())?;
      }
    }
    write!(w, ")")?;
    // return type
    if !ret_ty.is_unit() {
      write!(w, ": {}", ret_ty)?;
    }
    // function body
    if !func.dfg().bbs().is_empty() {
      writeln!(w, " {{")?;
      for (i, (bb, node)) in func.layout().bbs().iter().enumerate() {
        if i != 0 {
          writeln!(w)?;
        }
        self.visit_bb(w, nm, program, func, *bb, node)?;
      }
      writeln!(w, "}}")
    } else {
      writeln!(w)
    }
  }

  /// Generates the specific basic block.
  fn visit_bb(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    program: &Program,
    func: &FunctionData,
    bb: BasicBlock,
    node: &BasicBlockNode,
  ) -> Result<()> {
    // basic block name
    let bb = func.dfg().bb(bb);
    write!(w, "{}", nm.bb_name(bb))?;
    // basic block parameters
    if !bb.params().is_empty() {
      write!(w, "(")?;
      for (i, param) in bb.params().iter().enumerate() {
        if i != 0 {
          write!(w, ", ")?;
        }
        let param = value!(func, *param);
        write!(w, "{}: {}", nm.value_name(param), param.ty())?;
      }
      write!(w, ")")?;
    }
    writeln!(w, ":")?;
    // instrustions in basic block
    for inst in node.insts().keys() {
      write!(w, "  ")?;
      self.visit_local_inst(w, nm, program, func, value!(func, *inst))?;
    }
    Ok(())
  }

  /// Generates the specific global instruction.
  fn visit_global_inst(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    program: &Program,
    inst: &ValueData,
  ) -> Result<()> {
    let alloc = match inst.kind() {
      ValueKind::GlobalAlloc(alloc) => alloc,
      _ => panic!("invalid global instruction"),
    };
    let init = program.borrow_value(alloc.init());
    write!(w, "global {} = alloc {}, ", nm.value_name(inst), init.ty())?;
    self.visit_global_const(w, program, &init)
  }

  /// Generates the specific local instruction.
  fn visit_local_inst(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    program: &Program,
    func: &FunctionData,
    inst: &ValueData,
  ) -> Result<()> {
    // definition
    if !inst.ty().is_unit() {
      write!(w, "{} = ", nm.value_name(inst))?;
    }
    // content of instruction
    match inst.kind() {
      ValueKind::Alloc(_) => self.visit_alloc(w, inst.ty()),
      ValueKind::Load(v) => self.visit_load(w, nm, func, v),
      ValueKind::Store(v) => self.visit_store(w, nm, func, v),
      ValueKind::GetPtr(v) => self.visit_getptr(w, nm, func, v),
      ValueKind::GetElemPtr(v) => self.visit_getelemptr(w, nm, func, v),
      ValueKind::Binary(v) => self.visit_binary(w, nm, func, v),
      ValueKind::Branch(v) => self.visit_branch(w, nm, func, v),
      ValueKind::Jump(v) => self.visit_jump(w, nm, func, v),
      ValueKind::Call(v) => self.visit_call(w, nm, program, func, v),
      ValueKind::Return(v) => self.visit_return(w, nm, func, v),
      _ => panic!("invalid local instruction"),
    }?;
    writeln!(w)
  }

  /// Generates allocation.
  fn visit_alloc(&mut self, w: &mut impl Write, ty: &Type) -> Result<()> {
    let base = match ty.kind() {
      TypeKind::Pointer(base) => base,
      _ => panic!("invalid pointer type"),
    };
    write!(w, "alloc {}", base)
  }

  /// Generates memory load.
  fn visit_load(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &FunctionData,
    load: &Load,
  ) -> Result<()> {
    write!(w, "load ")?;
    self.visit_value(w, nm, func, value!(func, load.src()))
  }

  /// Generates memory store.
  fn visit_store(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &FunctionData,
    store: &Store,
  ) -> Result<()> {
    write!(w, "store ")?;
    self.visit_value(w, nm, func, value!(func, store.value()))?;
    write!(w, ", ")?;
    self.visit_value(w, nm, func, value!(func, store.dest()))
  }

  /// Generates pointer calculation.
  fn visit_getptr(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &FunctionData,
    gp: &GetPtr,
  ) -> Result<()> {
    write!(w, "getptr ")?;
    self.visit_value(w, nm, func, value!(func, gp.src()))?;
    write!(w, ", ")?;
    self.visit_value(w, nm, func, value!(func, gp.index()))
  }

  /// Generates element pointer calculation.
  fn visit_getelemptr(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &FunctionData,
    gep: &GetElemPtr,
  ) -> Result<()> {
    write!(w, "getelemptr ")?;
    self.visit_value(w, nm, func, value!(func, gep.src()))?;
    write!(w, ", ")?;
    self.visit_value(w, nm, func, value!(func, gep.index()))
  }

  /// Generates binary operation.
  fn visit_binary(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &FunctionData,
    bin: &Binary,
  ) -> Result<()> {
    write!(w, "{} ", bin.op())?;
    self.visit_value(w, nm, func, value!(func, bin.lhs()))?;
    write!(w, ", ")?;
    self.visit_value(w, nm, func, value!(func, bin.rhs()))
  }

  /// Generates branch.
  fn visit_branch(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &FunctionData,
    br: &Branch,
  ) -> Result<()> {
    write!(w, "br ")?;
    self.visit_value(w, nm, func, value!(func, br.cond()))?;
    write!(w, ", ")?;
    self.visit_bb_target(w, nm, func, br.true_bb(), br.true_args())?;
    write!(w, ", ")?;
    self.visit_bb_target(w, nm, func, br.false_bb(), br.false_args())
  }

  /// Generates jump.
  fn visit_jump(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &FunctionData,
    jump: &Jump,
  ) -> Result<()> {
    write!(w, "jump ")?;
    self.visit_bb_target(w, nm, func, jump.target(), jump.args())
  }

  /// Generates function call.
  fn visit_call(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    program: &Program,
    func: &FunctionData,
    call: &Call,
  ) -> Result<()> {
    write!(w, "call {}(", nm.func_name(program.func(call.callee())))?;
    for (i, arg) in call.args().iter().enumerate() {
      if i != 0 {
        write!(w, ", ")?;
      }
      self.visit_value(w, nm, func, value!(func, *arg))?;
    }
    write!(w, ")")
  }

  /// Generates function return.
  fn visit_return(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &FunctionData,
    ret: &Return,
  ) -> Result<()> {
    write!(w, "ret")?;
    if let Some(val) = ret.value() {
      write!(w, " ")?;
      self.visit_value(w, nm, func, value!(func, val))?;
    }
    Ok(())
  }

  /// Generates the specific value.
  fn visit_value(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &FunctionData,
    value: &ValueData,
  ) -> Result<()> {
    if value.kind().is_const() {
      self.visit_local_const(w, func, value)
    } else {
      write!(w, "{}", nm.value_name(value))
    }
  }

  /// Generates the specific global constant.
  fn visit_global_const(
    &mut self,
    w: &mut impl Write,
    program: &Program,
    value: &ValueData,
  ) -> Result<()> {
    match value.kind() {
      ValueKind::Integer(v) => write!(w, "{}", v.value()),
      ValueKind::ZeroInit(_) => write!(w, "zeroinit"),
      ValueKind::Undef(_) => write!(w, "undef"),
      ValueKind::Aggregate(v) => {
        write!(w, "{{")?;
        for (i, elem) in v.elems().iter().enumerate() {
          if i != 0 {
            write!(w, ", ")?;
          }
          self.visit_global_const(w, program, &program.borrow_value(*elem))?;
        }
        write!(w, "}}")
      }
      _ => panic!("invalid constant"),
    }
  }

  /// Generates the specific local constant.
  fn visit_local_const(
    &mut self,
    w: &mut impl Write,
    func: &FunctionData,
    value: &ValueData,
  ) -> Result<()> {
    match value.kind() {
      ValueKind::Integer(v) => write!(w, "{}", v.value()),
      ValueKind::ZeroInit(_) => write!(w, "zeroinit"),
      ValueKind::Undef(_) => write!(w, "undef"),
      ValueKind::Aggregate(v) => {
        write!(w, "{{")?;
        for (i, elem) in v.elems().iter().enumerate() {
          if i != 0 {
            write!(w, ", ")?;
          }
          self.visit_local_const(w, func, value!(func, *elem))?;
        }
        write!(w, "}}")
      }
      _ => panic!("invalid constant"),
    }
  }

  /// Generates the specific basic block target.
  fn visit_bb_target(
    &mut self,
    w: &mut impl Write,
    nm: &mut NameManager,
    func: &FunctionData,
    bb: BasicBlock,
    params: &[Value],
  ) -> Result<()> {
    write!(w, "{}", nm.bb_name(func.dfg().bb(bb)))?;
    if !params.is_empty() {
      write!(w, "(")?;
      for (i, param) in params.iter().enumerate() {
        if i != 0 {
          write!(w, ", ")?;
        }
        write!(w, "{}", nm.value_name(value!(func, *param)))?;
      }
      write!(w, ")")?;
    }
    Ok(())
  }
}

#[cfg(test)]
mod test {
  use crate::back::KoopaGenerator;
  use crate::front::Driver;
  use std::str;

  #[test]
  fn dump_ir() {
    let src = r#"global @x = alloc [i32, 10], zeroinit

fun @test(@i: i32): i32 {
%entry:
  %0 = getptr @x, 0
  store {1, 2, 3, 4, 5, 0, 0, 0, 0, 10}, %0
  %1 = getelemptr @x, @i
  %2 = load %1
  %3 = mul %2, 7
  ret %3
}
"#;
    let driver: Driver<_> = src.into();
    let mut gen = KoopaGenerator::new(Vec::new());
    gen
      .generate_on(&driver.generate_program().unwrap())
      .unwrap();
    assert_eq!(str::from_utf8(&gen.writer()).unwrap(), src);
  }

  #[test]
  fn dump_ir_phi() {
    let src = r#"decl @getint(): i32

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
"#;
    let driver: Driver<_> = src.into();
    let mut gen = KoopaGenerator::new(Vec::new());
    gen
      .generate_on(&driver.generate_program().unwrap())
      .unwrap();
    assert_eq!(str::from_utf8(&gen.writer()).unwrap(), src);
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
    let mut gen = KoopaGenerator::new(Vec::new());
    gen
      .generate_on(&driver.generate_program().unwrap())
      .unwrap();
    assert_eq!(str::from_utf8(&gen.writer()).unwrap(), src);
  }
}
