//! Implementations of the visitor for the LLVM IR generator.

use crate::back::{self, NameManager, Prefix};
use crate::ir::entities::{FunctionData, ValueData};
use crate::ir::layout::BasicBlockNode;
use crate::ir::values::*;
use crate::ir::{BasicBlock, Program, Type, TypeKind, Value, ValueKind};
use std::io::{Result, Write};
use std::num::NonZeroUsize;

/// Visitor for generating the in-memory form Koopa IR program into
/// the text form LLVM IR program.
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

/// The implementation of LLVM IR generator.
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

/// Returns the type of the given value in the current function.
macro_rules! value_ty {
  ($self:ident, $value:expr) => {
    if $value.is_global() {
      $self.program.borrow_value($value).ty().clone()
    } else {
      func!($self).dfg().value($value).ty().clone()
    }
  };
}

impl<'a, W: Write> VisitorImpl<'a, W> {
  /// Maximum length of LLVM IR identifier.
  const MAX_ID_LEN: usize = 512;

  /// Visits the program.
  fn visit(&mut self) -> Result<()> {
    // global values
    self.nm.set_prefix(Prefix::Custom {
      named: "@".into(),
      temp: "@$".into(),
      max_len: Some(unsafe { NonZeroUsize::new_unchecked(Self::MAX_ID_LEN + 1) }),
    });
    for inst in self.program.inst_layout() {
      self.visit_global_inst(&self.program.borrow_value(*inst))?;
    }
    if !self.program.inst_layout().is_empty() {
      writeln!(self.w)?;
    }
    // functions
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
      write!(self.w, "declare")?;
    } else {
      write!(self.w, "define")?;
    }
    // unwrap function type
    let (param_ty, ret_ty) = match func.ty().kind() {
      TypeKind::Function(param, ret) => (param, ret),
      _ => panic!("invalid function type"),
    };
    // return type
    write!(self.w, " ")?;
    self.visit_type(ret_ty)?;
    // function name
    write!(self.w, " {}(", self.nm.func_name(func))?;
    // change prefix
    self.nm.set_prefix(Prefix::Custom {
      named: "%".into(),
      temp: "%$".into(),
      max_len: Some(unsafe { NonZeroUsize::new_unchecked(Self::MAX_ID_LEN + 1) }),
    });
    // parameters
    if is_decl {
      for (i, ty) in param_ty.iter().enumerate() {
        if i != 0 {
          write!(self.w, ", ")?;
        }
        self.visit_type(ty)?;
      }
    } else {
      for (i, param) in func.params().iter().enumerate() {
        if i != 0 {
          write!(self.w, ", ")?;
        }
        let param = value!(self, *param);
        self.visit_type(param.ty())?;
        write!(self.w, " {}", self.nm.value_name(param))?;
      }
    }
    write!(self.w, ")")?;
    // function body
    if !is_decl {
      writeln!(self.w, " {{")?;
      for (i, (bb, node)) in func.layout().bbs().iter().enumerate() {
        if i != 0 {
          writeln!(self.w)?;
        }
        self.visit_bb(*bb, node)?;
      }
      writeln!(self.w, "}}")?;
    } else {
      writeln!(self.w)?;
    }
    // restore prefix
    self.nm.set_prefix(Prefix::Custom {
      named: "@".into(),
      temp: "@$".into(),
      max_len: Some(unsafe { NonZeroUsize::new_unchecked(Self::MAX_ID_LEN + 1) }),
    });
    Ok(())
  }

  /// Generates the given basic block.
  fn visit_bb(&mut self, bb: BasicBlock, node: &BasicBlockNode) -> Result<()> {
    // basic block name
    let data = func!(self).dfg().bb(bb);
    writeln!(self.w, "{}:", &self.nm.bb_name(data)[1..])?;
    // basic block parameters (phi functions)
    for (i, param) in data.params().iter().enumerate() {
      let param = value!(self, *param);
      write!(self.w, "  {} = phi ", self.nm.value_name(param))?;
      self.visit_type(param.ty())?;
      write!(self.w, " ")?;
      for (k, user) in data.used_by().iter().enumerate() {
        if k != 0 {
          write!(self.w, ", ")?;
        }
        write!(self.w, "[")?;
        match value!(self, *user).kind() {
          ValueKind::Branch(br) => {
            if br.true_bb() == bb {
              self.visit_value(false, br.true_args()[i])?;
            } else {
              self.visit_value(false, br.false_args()[i])?;
            }
          }
          ValueKind::Jump(jump) => self.visit_value(false, jump.args()[i])?,
          _ => panic!("invalid branch/jump instruction"),
        }
        write!(self.w, ", ")?;
        self.visit_bb_ref(func!(self).layout().parent_bb(*user).unwrap())?;
        write!(self.w, "]")?;
      }
      writeln!(self.w)?;
    }
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
    write!(self.w, "{} = global ", self.nm.value_name(inst))?;
    self.visit_global_const(&init)?;
    writeln!(self.w)
  }

  /// Generates the given instruction.
  fn visit_local_inst(&mut self, inst: &ValueData) -> Result<()> {
    // definition
    if !matches!(inst.kind(), ValueKind::Binary(_)) && !inst.ty().is_unit() {
      write!(self.w, "{} = ", self.nm.value_name(inst))?;
    }
    // content of instruction
    match inst.kind() {
      ValueKind::Alloc(_) => self.visit_alloc(inst.ty()),
      ValueKind::Load(v) => self.visit_load(inst.ty(), v),
      ValueKind::Store(v) => self.visit_store(v),
      ValueKind::GetPtr(v) => self.visit_getptr(v),
      ValueKind::GetElemPtr(v) => self.visit_getelemptr(v),
      ValueKind::Binary(v) => self.visit_binary(inst, v),
      ValueKind::Branch(v) => self.visit_branch(v),
      ValueKind::Jump(v) => self.visit_jump(v),
      ValueKind::Call(v) => self.visit_call(inst.ty(), v),
      ValueKind::Return(v) => self.visit_return(v),
      _ => panic!("invalid instruction"),
    }?;
    writeln!(self.w)
  }

  /// Generates allocation.
  fn visit_alloc(&mut self, ty: &Type) -> Result<()> {
    let base = match ty.kind() {
      TypeKind::Pointer(base) => base,
      _ => panic!("invalid pointer type"),
    };
    write!(self.w, "alloca ")?;
    self.visit_type(base)
  }

  /// Generates memory load.
  fn visit_load(&mut self, ty: &Type, load: &Load) -> Result<()> {
    write!(self.w, "load ")?;
    self.visit_type(ty)?;
    write!(self.w, ", ")?;
    self.visit_value(true, load.src())
  }

  /// Generates memory store.
  fn visit_store(&mut self, store: &Store) -> Result<()> {
    write!(self.w, "store ")?;
    self.visit_value(true, store.value())?;
    write!(self.w, ", ")?;
    self.visit_value(true, store.dest())
  }

  /// Generates pointer calculation.
  fn visit_getptr(&mut self, gp: &GetPtr) -> Result<()> {
    write!(self.w, "getelementptr inbounds ")?;
    self.visit_type(match value_ty!(self, gp.src()).kind() {
      TypeKind::Pointer(base) => base,
      _ => panic!("invalid pointer type"),
    })?;
    write!(self.w, ", ")?;
    self.visit_value(true, gp.src())?;
    write!(self.w, ", ")?;
    self.visit_value(true, gp.index())
  }

  /// Generates element pointer calculation.
  fn visit_getelemptr(&mut self, gep: &GetElemPtr) -> Result<()> {
    write!(self.w, "getelementptr inbounds ")?;
    self.visit_type(match value_ty!(self, gep.src()).kind() {
      TypeKind::Pointer(base) => base,
      _ => panic!("invalid pointer type"),
    })?;
    write!(self.w, ", ")?;
    self.visit_value(true, gep.src())?;
    write!(self.w, ", i32 0, ")?;
    self.visit_value(true, gep.index())
  }

  /// Generates binary operation.
  fn visit_binary(&mut self, value: &ValueData, bin: &Binary) -> Result<()> {
    // generate definition
    let temp_name = if matches!(
      bin.op(),
      BinaryOp::NotEq | BinaryOp::Eq | BinaryOp::Gt | BinaryOp::Lt | BinaryOp::Ge | BinaryOp::Le
    ) {
      let t = self.nm.temp_value_name();
      write!(self.w, "{} = ", t)?;
      Some(t)
    } else {
      write!(self.w, "{} = ", self.nm.value_name(value))?;
      None
    };
    // generate operator
    match bin.op() {
      BinaryOp::NotEq | BinaryOp::Eq => write!(self.w, "icmp {}", bin.op()),
      BinaryOp::Gt | BinaryOp::Lt | BinaryOp::Ge | BinaryOp::Le => {
        write!(self.w, "icmp s{}", bin.op())
      }
      BinaryOp::Div => write!(self.w, "sdiv"),
      BinaryOp::Mod => write!(self.w, "srem"),
      BinaryOp::Shr => write!(self.w, "lshr"),
      BinaryOp::Sar => write!(self.w, "ashr"),
      _ => write!(self.w, "{}", bin.op()),
    }?;
    write!(self.w, " i32 ")?;
    // generate lhs & rhs
    self.visit_value(false, bin.lhs())?;
    write!(self.w, ", ")?;
    self.visit_value(false, bin.rhs())?;
    // generate zero extension if is a compare instruction
    if let Some(t) = temp_name {
      write!(
        self.w,
        "\n  {} = zext i1 {} to i32",
        self.nm.value_name(value),
        t
      )?;
    }
    Ok(())
  }

  /// Generates branch.
  fn visit_branch(&mut self, br: &Branch) -> Result<()> {
    // generate condition
    let temp = self.nm.temp_value_name();
    write!(self.w, "{} = icmp ne i32 ", temp)?;
    self.visit_value(false, br.cond())?;
    write!(self.w, ", 0\n  br i1 {}, label ", temp)?;
    // generate targets
    // ignore basic block parameters
    // because they are handled when generating basic blocks
    self.visit_bb_ref(br.true_bb())?;
    write!(self.w, ", label ")?;
    self.visit_bb_ref(br.false_bb())
  }

  /// Generates jump.
  fn visit_jump(&mut self, jump: &Jump) -> Result<()> {
    write!(self.w, "br label ")?;
    // ignore basic block parameters
    // because they are handled when generating basic blocks
    self.visit_bb_ref(jump.target())
  }

  /// Generates function call.
  fn visit_call(&mut self, ty: &Type, call: &Call) -> Result<()> {
    write!(self.w, "call ")?;
    self.visit_type(ty)?;
    write!(
      self.w,
      " {}(",
      self.nm.func_name(self.program.func(call.callee()))
    )?;
    for (i, arg) in call.args().iter().enumerate() {
      if i != 0 {
        write!(self.w, ", ")?;
      }
      self.visit_value(true, *arg)?;
    }
    write!(self.w, ")")
  }

  /// Generates function return.
  fn visit_return(&mut self, ret: &Return) -> Result<()> {
    write!(self.w, "ret ")?;
    if let Some(val) = ret.value() {
      self.visit_value(true, val)
    } else {
      write!(self.w, "void")
    }
  }

  /// Generates the given value.
  fn visit_value(&mut self, with_ty: bool, value: Value) -> Result<()> {
    if value.is_global() {
      let value = self.program.borrow_value(value);
      assert!(!value.kind().is_const());
      if with_ty {
        self.visit_type(value.ty())?;
        write!(self.w, " ")?;
      }
      write!(self.w, "{}", self.nm.value_name(&value))
    } else {
      let value = value!(self, value);
      if value.kind().is_const() {
        self.visit_local_const(with_ty, value)
      } else {
        if with_ty {
          self.visit_type(value.ty())?;
          write!(self.w, " ")?;
        }
        write!(self.w, "{}", self.nm.value_name(value))
      }
    }
  }

  /// Generates the given global constant.
  fn visit_global_const(&mut self, value: &ValueData) -> Result<()> {
    self.visit_type(value.ty())?;
    write!(self.w, " ")?;
    match value.kind() {
      ValueKind::Integer(v) => write!(self.w, "{}", v.value()),
      ValueKind::ZeroInit(_) => write!(self.w, "zeroinitializer"),
      ValueKind::Undef(_) => write!(self.w, "undef"),
      ValueKind::Aggregate(v) => {
        write!(self.w, "[")?;
        for (i, elem) in v.elems().iter().enumerate() {
          if i != 0 {
            write!(self.w, ", ")?;
          }
          self.visit_global_const(&self.program.borrow_value(*elem))?;
        }
        write!(self.w, "]")
      }
      _ => panic!("invalid constant"),
    }
  }

  /// Generates the given local constant.
  fn visit_local_const(&mut self, with_ty: bool, value: &ValueData) -> Result<()> {
    if with_ty {
      self.visit_type(value.ty())?;
      write!(self.w, " ")?;
    }
    match value.kind() {
      ValueKind::Integer(v) => write!(self.w, "{}", v.value()),
      ValueKind::ZeroInit(_) => write!(self.w, "zeroinitializer"),
      ValueKind::Undef(_) => write!(self.w, "undef"),
      ValueKind::Aggregate(v) => {
        write!(self.w, "[")?;
        for (i, elem) in v.elems().iter().enumerate() {
          if i != 0 {
            write!(self.w, ", ")?;
          }
          self.visit_local_const(with_ty, value!(self, *elem))?;
        }
        write!(self.w, "]")
      }
      _ => panic!("invalid constant"),
    }
  }

  /// Generates the given basic block reference.
  fn visit_bb_ref(&mut self, bb: BasicBlock) -> Result<()> {
    write!(self.w, "{}", self.nm.bb_name(func!(self).dfg().bb(bb)))
  }

  /// Generates the given type.
  fn visit_type(&mut self, ty: &Type) -> Result<()> {
    match ty.kind() {
      TypeKind::Int32 => write!(self.w, "i32"),
      TypeKind::Unit => write!(self.w, "void"),
      TypeKind::Array(base, len) => {
        write!(self.w, "[{} x ", len)?;
        self.visit_type(base)?;
        write!(self.w, "]")
      }
      TypeKind::Pointer(base) => {
        self.visit_type(base)?;
        write!(self.w, "*")
      }
      // actually a function pointer
      TypeKind::Function(params, ret) => {
        self.visit_type(ret)?;
        write!(self.w, " (")?;
        for (i, param) in params.iter().enumerate() {
          if i != 0 {
            write!(self.w, ", ")?;
          }
          self.visit_type(param)?;
        }
        write!(self.w, ")*")
      }
    }
  }
}

#[cfg(test)]
mod test {
  use crate::back::LlvmGenerator;
  use crate::front::Driver;
  use std::collections::VecDeque;
  use std::str;

  fn remove_phi(mut ir: String) -> String {
    let mut vec: VecDeque<_> = ir.match_indices("phi").map(|(pos, _)| pos).collect();
    let mut pos = 0usize;
    ir.retain(|c| {
      let cur = pos;
      pos += 1;
      if let Some(p) = vec.front() {
        if cur >= *p {
          if c != '\n' {
            false
          } else {
            vec.pop_front();
            true
          }
        } else {
          true
        }
      } else {
        true
      }
    });
    ir
  }

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
$entry:
  %$0 = getelementptr inbounds [10 x i32], [10 x i32]* @x, i32 0
  store [10 x i32] [i32 1, i32 2, i32 3, i32 4, i32 5, i32 0, i32 0, i32 0, i32 0, i32 10], [10 x i32]* %$0
  %$1 = getelementptr inbounds [10 x i32], [10 x i32]* @x, i32 0, i32 %i
  %$2 = load i32, i32* %$1
  %$3 = mul i32 %$2, 7
  ret i32 %$3
}
"#
    );
  }

  #[test]
  fn dump_ir_bb_params() {
    let driver: Driver<_> = r#"
      decl @getint(): i32

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
    "#
    .into();
    let mut gen = LlvmGenerator::new(Vec::new());
    gen
      .generate_on(&driver.generate_program().unwrap())
      .unwrap();
    let ans = str::from_utf8(&gen.writer()).unwrap().to_string();
    println!("{}", ans);
    assert_eq!(
      remove_phi(ans),
      r#"declare i32 @getint()

define i32 @main() {
$entry:
  %$ans_0 = call i32 @getint()
  br label %$while_entry

$while_entry:
  %$ind_var_0 = 
  %$ans_1 = 
  %$0 = icmp slt i32 %$ind_var_0, 10
  %$cond = zext i1 %$0 to i32
  %$1 = icmp ne i32 %$cond, 0
  br i1 %$1, label %$while_body, label %$while_end

$while_body:
  %$ans_2 = add i32 %$ans_1, %$ind_var_0
  %$ind_var_1 = add i32 %$ind_var_0, 1
  br label %$while_entry

$while_end:
  ret i32 %$ans_1
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
    let mut gen = LlvmGenerator::new(Vec::new());
    gen
      .generate_on(&driver.generate_program().unwrap())
      .unwrap();
    let ans = str::from_utf8(&gen.writer()).unwrap().to_string();
    println!("{}", ans);
    assert_eq!(
      remove_phi(ans),
      r#"declare i32 @getint()

define i32 @main() {
$args_0:
  %$0 = call i32 @getint()
  %$1 = call i32 @getint()
  br label %$while_cond_2

$while_cond_2:
  %$2 = 
  %$4 = 
  %$6 = icmp slt i32 %$4, %$1
  %$7 = zext i1 %$6 to i32
  %$8 = icmp ne i32 %$7, 0
  br i1 %$8, label %$while_body_3, label %$while_end_1

$while_body_3:
  br label %$while_cond_4

$while_end_1:
  ret i32 %$2

$while_cond_4:
  %$3 = 
  %$10 = 
  %$12 = icmp slt i32 %$10, %$0
  %$13 = zext i1 %$12 to i32
  %$14 = icmp ne i32 %$13, 0
  br i1 %$14, label %$while_body_6, label %$while_end_5

$while_body_6:
  %$15 = add i32 %$3, %$4
  %$9 = add i32 %$15, %$10
  %$11 = add i32 %$10, 1
  br label %$while_cond_4

$while_end_5:
  %$5 = add i32 %$4, 1
  br label %$while_cond_2
}
"#
    );
  }

  #[test]
  fn dump_underlined_symbols() {
    let driver: Driver<_> = r#"
      global @_0 = alloc i32, 0
      global %_0 = alloc i32, 1
      global %0 = alloc i32, 2

      fun @test(@_2: i32): i32 {
      %entry:
        @_1 = getptr @_0, 0
        %_1 = getptr %_0, 0
        %1 = getptr %0, 0
        %2 = load @_1
        %3 = load %_1
        %4 = add %2, %3
        %5 = load %1
        %6 = add %4, %5
        store %6, @_1
        ret %6
      }
    "#
    .into();
    let mut gen = LlvmGenerator::new(Vec::new());
    gen
      .generate_on(&driver.generate_program().unwrap())
      .unwrap();
    assert_eq!(
      str::from_utf8(&gen.writer()).unwrap(),
      r#"@_0 = global i32 0
@$_0 = global i32 1
@$0 = global i32 2

define i32 @test(i32 %_2) {
$entry:
  %_1 = getelementptr inbounds i32, i32* @_0, i32 0
  %$_1 = getelementptr inbounds i32, i32* @$_0, i32 0
  %$1 = getelementptr inbounds i32, i32* @$0, i32 0
  %$2 = load i32, i32* %_1
  %$3 = load i32, i32* %$_1
  %$4 = add i32 %$2, %$3
  %$5 = load i32, i32* %$1
  %$6 = add i32 %$4, %$5
  store i32 %$6, i32* %_1
  ret i32 %$6
}
"#
    );
  }
}
