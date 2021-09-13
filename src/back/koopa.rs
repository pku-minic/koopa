use crate::back::generator::{self, NameManager};
use crate::ir::core::Value;
use crate::ir::structs::{BasicBlock, Function, Program};
use std::io::{Result, Write};

/// Visitor for generating Koopa IR structures into text formatted Koopa IR.
#[derive(Default)]
pub struct Visitor;

impl<W: Write> generator::Visitor<W> for Visitor {
  type Output = ();

  fn generate_program(&mut self, w: &mut W, nm: &mut NameManager, program: &Program) -> Result<()> {
    for var in program.vars() {
      self.generate_value(w, nm, var)?;
    }
    writeln!(w)?;
    for func in program.funcs() {
      self.generate_func(w, nm, func)?;
    }
    Ok(())
  }

  /// Generates the specific function.
  fn generate_func(&mut self, w: &mut W, nm: &mut NameManager, func: &Function) -> Result<()> {
    writeln!(w, "fun {}()", func.name())
  }

  /// Generates the specific basic block.
  fn generate_bb(&mut self, w: &mut W, nm: &mut NameManager, bb: &BasicBlock) -> Result<()> {
    todo!()
  }

  /// Generates the specific value.
  fn generate_value(&mut self, w: &mut W, nm: &mut NameManager, value: &Value) -> Result<()> {
    todo!()
  }

  /// Generates the specific value reference.
  fn generate_value_ref(&mut self, w: &mut W, nm: &mut NameManager, value: &Value) -> Result<()> {
    write!(w, "{}", nm.get_value_name(value))
  }
}
