use crate::front::ast::{AstBox, AstKind};
use crate::front::span::Span;
use crate::ir::structs::Program;
use crate::ir::types::Type;

/// Builder for building Koopa IR from AST.
pub struct Builder {
  program: Program,
}

impl Builder {
  /// Creates a new builder.
  pub fn new() -> Self {
    Self {
      program: Program::default(),
    }
  }

  /// Accepts an AST.
  pub fn accept(ast: AstBox) {
    todo!()
  }

  /// Consumes and get the generated program.
  pub fn program(self) -> Program {
    self.program
  }

  /// Visits `IntType` AST.
  fn visit_int_type(&mut self) -> Type {
    Type::get_i32()
  }

  /// Visits `ArrayType` AST.
  fn visit_array_type(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `PointerType` AST.
  fn visit_pointer_type(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `FunType` AST.
  fn visit_fun_type(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `SymbolRef` AST.
  fn visit_symbol_ref(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `IntVal` AST.
  fn visit_int_val(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `UndefVal` AST.
  fn visit_undef_val(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `Aggregate` AST.
  fn visit_aggregate(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `ZeroInit` AST.
  fn visit_zero_init(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `SymbolDef` AST.
  fn visit_symbol_def(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `GlobalDef` AST.
  fn visit_global_def(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `MemDecl` AST.
  fn visit_mem_decl(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `GlobalDecl` AST.
  fn visit_global_decl(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `Load` AST.
  fn visit_load(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `Store` AST.
  fn visit_store(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `GetPointer` AST.
  fn visit_get_pointer(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `BinaryExpr` AST.
  fn visit_binary_expr(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `UnaryExpr` AST.
  fn visit_unary_expr(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `Branch` AST.
  fn visit_branch(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `Jump` AST.
  fn visit_jump(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `FunCall` AST.
  fn visit_fun_call(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `Return` AST.
  fn visit_return(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `FunDef` AST.
  fn visit_fun_def(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `Block` AST.
  fn visit_block(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `FunDecl` AST.
  fn visit_fun_decl(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `Phi` AST.
  fn visit_phi(&mut self, span: &Span) {
    todo!()
  }

  /// Visits `End` AST.
  fn visit_end(&mut self, span: &Span) {
    todo!()
  }
}
