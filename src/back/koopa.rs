//! Implementations of the visitor for the text form Koopa IR generator.

use crate::back::{self, NameManager};
use crate::ir::entities::{FunctionData, ValueData};
use crate::ir::layout::BasicBlockNode;
use crate::ir::values::*;
use crate::ir::{BasicBlock, Program, Type, TypeKind, Value, ValueKind};
use std::io::{Result, Write};

/// Visitor for generating the in-memeory form Koopa IR program into
/// the text form.
#[derive(Default)]
pub struct Visitor;

impl<W: Write> back::Visitor<W> for Visitor {
  type Output = ();

  fn visit(&mut self, w: &mut W, nm: &mut NameManager, program: &Program) -> Result<()> {
    let mut visitor = VisitorImpl {
      w,
      nm,
      program,
      func: None,
    };
    visitor.visit()
  }
}

/// The implementation of text form Koopa IR generator.
struct VisitorImpl<'a, W: Write> {
  w: &'a mut W,
  nm: &'a mut NameManager,
  program: &'a Program,
  func: Option<&'a FunctionData>,
}

/// Returns a reference to the current function.
macro_rules! func {
  ($self:ident) => {
    $self.func.unwrap()
  };
}

/// Returns a reference to the given value in the current function.
macro_rules! value {
  ($self:ident, $value:expr) => {
    func!($self).dfg().value($value)
  };
}

impl<'a, W: Write> VisitorImpl<'a, W> {
  /// Visits the program.
  fn visit(&mut self) -> Result<()> {
    for inst in self.program.inst_layout() {
      self.visit_global_inst(&self.program.borrow_value(*inst))?;
    }
    if !self.program.inst_layout().is_empty() {
      writeln!(self.w)?;
    }
    for (i, func) in self.program.func_layout().iter().enumerate() {
      if i != 0 {
        writeln!(self.w)?;
      }
      let func = self.program.func(*func);
      self.func = Some(func);
      self.nm.enter_func_scope();
      self.visit_func(func)?;
      self.nm.exit_func_scope();
    }
    Ok(())
  }

  /// Generates the given function.
  fn visit_func(&mut self, func: &FunctionData) -> Result<()> {
    // header
    let is_decl = func.dfg().bbs().is_empty();
    if is_decl {
      write!(self.w, "decl")?;
    } else {
      write!(self.w, "fun")?;
    }
    // function name
    write!(self.w, " {}(", self.nm.func_name(func))?;
    // unwrap function type
    let (param_ty, ret_ty) = match func.ty().kind() {
      TypeKind::Function(param, ret) => (param, ret),
      _ => panic!("invalid function type"),
    };
    // parameters
    if is_decl {
      for (i, ty) in param_ty.iter().enumerate() {
        if i != 0 {
          write!(self.w, ", ")?;
        }
        write!(self.w, "{}", ty)?;
      }
    } else {
      for (i, param) in func.params().iter().enumerate() {
        if i != 0 {
          write!(self.w, ", ")?;
        }
        let param = value!(self, *param);
        write!(self.w, "{}: {}", self.nm.value_name(param), param.ty())?;
      }
    }
    write!(self.w, ")")?;
    // return type
    if !ret_ty.is_unit() {
      write!(self.w, ": {}", ret_ty)?;
    }
    // function body
    if !is_decl {
      writeln!(self.w, " {{")?;
      for (i, (bb, node)) in func.layout().bbs().iter().enumerate() {
        if i != 0 {
          writeln!(self.w)?;
        }
        self.visit_bb(*bb, node)?;
      }
      writeln!(self.w, "}}")
    } else {
      writeln!(self.w)
    }
  }

  /// Generates the given basic block.
  fn visit_bb(&mut self, bb: BasicBlock, node: &BasicBlockNode) -> Result<()> {
    // basic block name
    let bb = func!(self).dfg().bb(bb);
    write!(self.w, "{}", self.nm.bb_name(bb))?;
    // basic block parameters
    if !bb.params().is_empty() {
      write!(self.w, "(")?;
      for (i, param) in bb.params().iter().enumerate() {
        if i != 0 {
          write!(self.w, ", ")?;
        }
        let param = value!(self, *param);
        write!(self.w, "{}: {}", self.nm.value_name(param), param.ty())?;
      }
      write!(self.w, ")")?;
    }
    writeln!(self.w, ":")?;
    // instrustions in basic block
    for inst in node.insts().keys() {
      write!(self.w, "  ")?;
      self.visit_local_inst(value!(self, *inst))?;
    }
    Ok(())
  }

  /// Generates the given global instruction.
  fn visit_global_inst(&mut self, inst: &ValueData) -> Result<()> {
    let alloc = match inst.kind() {
      ValueKind::GlobalAlloc(alloc) => alloc,
      _ => panic!("invalid global instruction"),
    };
    let init = self.program.borrow_value(alloc.init());
    write!(
      self.w,
      "global {} = alloc {}, ",
      self.nm.value_name(inst),
      init.ty()
    )?;
    self.visit_global_const(&init)?;
    writeln!(self.w)
  }

  /// Generates the given local instruction.
  fn visit_local_inst(&mut self, inst: &ValueData) -> Result<()> {
    // definition
    if !inst.ty().is_unit() {
      write!(self.w, "{} = ", self.nm.value_name(inst))?;
    }
    // content of instruction
    match inst.kind() {
      ValueKind::Alloc(_) => self.visit_alloc(inst.ty()),
      ValueKind::Load(v) => self.visit_load(v),
      ValueKind::Store(v) => self.visit_store(v),
      ValueKind::GetPtr(v) => self.visit_getptr(v),
      ValueKind::GetElemPtr(v) => self.visit_getelemptr(v),
      ValueKind::Binary(v) => self.visit_binary(v),
      ValueKind::Branch(v) => self.visit_branch(v),
      ValueKind::Jump(v) => self.visit_jump(v),
      ValueKind::Call(v) => self.visit_call(v),
      ValueKind::Return(v) => self.visit_return(v),
      _ => panic!("invalid local instruction"),
    }?;
    writeln!(self.w)
  }

  /// Generates allocation.
  fn visit_alloc(&mut self, ty: &Type) -> Result<()> {
    let base = match ty.kind() {
      TypeKind::Pointer(base) => base,
      _ => panic!("invalid pointer type"),
    };
    write!(self.w, "alloc {}", base)
  }

  /// Generates memory load.
  fn visit_load(&mut self, load: &Load) -> Result<()> {
    write!(self.w, "load ")?;
    self.visit_value(load.src())
  }

  /// Generates memory store.
  fn visit_store(&mut self, store: &Store) -> Result<()> {
    write!(self.w, "store ")?;
    self.visit_value(store.value())?;
    write!(self.w, ", ")?;
    self.visit_value(store.dest())
  }

  /// Generates pointer calculation.
  fn visit_getptr(&mut self, gp: &GetPtr) -> Result<()> {
    write!(self.w, "getptr ")?;
    self.visit_value(gp.src())?;
    write!(self.w, ", ")?;
    self.visit_value(gp.index())
  }

  /// Generates element pointer calculation.
  fn visit_getelemptr(&mut self, gep: &GetElemPtr) -> Result<()> {
    write!(self.w, "getelemptr ")?;
    self.visit_value(gep.src())?;
    write!(self.w, ", ")?;
    self.visit_value(gep.index())
  }

  /// Generates binary operation.
  fn visit_binary(&mut self, bin: &Binary) -> Result<()> {
    write!(self.w, "{} ", bin.op())?;
    self.visit_value(bin.lhs())?;
    write!(self.w, ", ")?;
    self.visit_value(bin.rhs())
  }

  /// Generates branch.
  fn visit_branch(&mut self, br: &Branch) -> Result<()> {
    write!(self.w, "br ")?;
    self.visit_value(br.cond())?;
    write!(self.w, ", ")?;
    self.visit_bb_target(br.true_bb(), br.true_args())?;
    write!(self.w, ", ")?;
    self.visit_bb_target(br.false_bb(), br.false_args())
  }

  /// Generates jump.
  fn visit_jump(&mut self, jump: &Jump) -> Result<()> {
    write!(self.w, "jump ")?;
    self.visit_bb_target(jump.target(), jump.args())
  }

  /// Generates function call.
  fn visit_call(&mut self, call: &Call) -> Result<()> {
    write!(
      self.w,
      "call {}(",
      self.nm.func_name(self.program.func(call.callee()))
    )?;
    for (i, arg) in call.args().iter().enumerate() {
      if i != 0 {
        write!(self.w, ", ")?;
      }
      self.visit_value(*arg)?;
    }
    write!(self.w, ")")
  }

  /// Generates function return.
  fn visit_return(&mut self, ret: &Return) -> Result<()> {
    write!(self.w, "ret")?;
    if let Some(val) = ret.value() {
      write!(self.w, " ")?;
      self.visit_value(val)?;
    }
    Ok(())
  }

  /// Generates the given value.
  fn visit_value(&mut self, value: Value) -> Result<()> {
    if value.is_global() {
      let value = self.program.borrow_value(value);
      assert!(!value.kind().is_const());
      write!(self.w, "{}", self.nm.value_name(&value))
    } else {
      let value = value!(self, value);
      if value.kind().is_const() {
        self.visit_local_const(value)
      } else {
        write!(self.w, "{}", self.nm.value_name(value))
      }
    }
  }

  /// Generates the given global constant.
  fn visit_global_const(&mut self, value: &ValueData) -> Result<()> {
    match value.kind() {
      ValueKind::Integer(v) => write!(self.w, "{}", v.value()),
      ValueKind::ZeroInit(_) => write!(self.w, "zeroinit"),
      ValueKind::Undef(_) => write!(self.w, "undef"),
      ValueKind::Aggregate(v) => {
        write!(self.w, "{{")?;
        for (i, elem) in v.elems().iter().enumerate() {
          if i != 0 {
            write!(self.w, ", ")?;
          }
          self.visit_global_const(&self.program.borrow_value(*elem))?;
        }
        write!(self.w, "}}")
      }
      _ => panic!("invalid constant"),
    }
  }

  /// Generates the given local constant.
  fn visit_local_const(&mut self, value: &ValueData) -> Result<()> {
    match value.kind() {
      ValueKind::Integer(v) => write!(self.w, "{}", v.value()),
      ValueKind::ZeroInit(_) => write!(self.w, "zeroinit"),
      ValueKind::Undef(_) => write!(self.w, "undef"),
      ValueKind::Aggregate(v) => {
        write!(self.w, "{{")?;
        for (i, elem) in v.elems().iter().enumerate() {
          if i != 0 {
            write!(self.w, ", ")?;
          }
          self.visit_local_const(value!(self, *elem))?;
        }
        write!(self.w, "}}")
      }
      _ => panic!("invalid constant"),
    }
  }

  /// Generates the given basic block target.
  fn visit_bb_target(&mut self, bb: BasicBlock, params: &[Value]) -> Result<()> {
    write!(self.w, "{}", self.nm.bb_name(func!(self).dfg().bb(bb)))?;
    if !params.is_empty() {
      write!(self.w, "(")?;
      for (i, param) in params.iter().enumerate() {
        if i != 0 {
          write!(self.w, ", ")?;
        }
        self.visit_value(*param)?;
      }
      write!(self.w, ")")?;
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
  fn dump_ir_bb_params() {
    let src = r#"decl @getint(): i32

fun @main(): i32 {
%entry:
  %ans_0 = call @getint()
  jump %while_entry(0, %ans_0)

%while_entry(%ind_var_0: i32, %ans_1: i32):
  %cond = lt %ind_var_0, 10
  br %cond, %while_body, %while_end

%while_body:
  %ans_2 = add %ans_1, %ind_var_0
  %ind_var_1 = add %ind_var_0, 1
  jump %while_entry(%ind_var_1, %ans_2)

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
  jump %while_cond_2(0, 0)

%while_cond_2(%2: i32, %3: i32):
  %4 = lt %3, %1
  br %4, %while_body_3, %while_end_1

%while_body_3:
  jump %while_cond_4(%2, 0)

%while_end_1:
  ret %2

%while_cond_4(%5: i32, %6: i32):
  %7 = lt %6, %0
  br %7, %while_body_6, %while_end_5

%while_body_6:
  %8 = add %5, %3
  %9 = add %8, %6
  %10 = add %6, 1
  jump %while_cond_4(%9, %10)

%while_end_5:
  %11 = add %3, 1
  jump %while_cond_2(%5, %11)
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
