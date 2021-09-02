use crate::front::ast::{self, AstBox, AstKind};
use crate::front::span::Span;
use crate::ir::core::ValueRc;
use crate::ir::instructions as inst;
use crate::ir::structs::{self, BasicBlockRc, FunctionRc, Program};
use crate::ir::types::Type;
use crate::ir::values;
use std::collections::HashMap;

/// Builder for building Koopa IR from AST.
pub struct Builder {
  program: Program,
  global_vars: HashMap<String, ValueRc>,
  global_funcs: HashMap<String, FunctionRc>,
  local_bbs: HashMap<String, BasicBlockRc>,
  local_defs: HashMap<String, ValueRc>,
}

macro_rules! unwrap_ast {
  ($ast:expr, $kind:ident) => {
    match &$ast.kind {
      AstKind::$kind(ast) => ast,
      _ => panic!("invalid `{}` AST", stringify!($kind)),
    }
  };
}

// TODO: check when inserting objects into maps!
impl Builder {
  /// Creates a new builder.
  pub fn new() -> Self {
    Self {
      program: Program::default(),
      global_vars: HashMap::new(),
      global_funcs: HashMap::new(),
      local_bbs: HashMap::new(),
      local_defs: HashMap::new(),
    }
  }

  /// Builds the specific AST into IR.
  pub fn build_on(&mut self, ast: &AstBox) {
    match &ast.kind {
      AstKind::GlobalDef(ast) => self.build_on_global_def(ast),
      AstKind::FunDef(ast) => self.build_on_fun_def(ast),
      AstKind::FunDecl(ast) => self.build_on_fun_decl(ast),
      AstKind::Error(_) => todo!(),
      AstKind::End(_) => todo!(),
      _ => panic!("invalid AST input"),
    }
  }

  /// Consumes and get the generated program.
  pub fn program(self) -> Program {
    self.program
  }

  /// Builds on global symbol definitions.
  fn build_on_global_def(&mut self, ast: &ast::GlobalDef) {
    // create global allocation
    let init = self.generate_value(&ast.value);
    let alloc = inst::GlobalAlloc::new(init);
    // set name for the created value
    if !ast.name.is_temp() {
      alloc.borrow_mut().set_name(Some(ast.name.clone()));
    }
    // add to global variable map
    self.global_vars.insert(ast.name.clone(), alloc.clone());
    // add to program
    self.program.add_var(alloc);
  }

  /// Builds on function definitions.
  fn build_on_fun_def(&mut self, ast: &ast::FunDef) {
    // create function definition
    let def = structs::Function::new(
      ast.name.clone(),
      ast
        .params
        .iter()
        .enumerate()
        .map(|(i, (name, ty))| {
          // create argument reference
          let arg = values::ArgRef::new(self.generate_type(ty), i);
          if !name.is_temp() {
            arg.borrow_mut().set_name(Some(name.clone()));
          }
          arg
        })
        .collect(),
      ast
        .ret
        .as_ref()
        .map_or(Type::get_unit(), |a| self.generate_type(a)),
    );
    // add to global function map
    self.global_funcs.insert(ast.name.clone(), def.clone());
    // add to program
    self.program.add_func(def);
    // create all basic blocks
    self.local_bbs.clear();
    for bb in ast.bbs.iter() {
      let block = unwrap_ast!(bb, Block);
      let bb = structs::BasicBlock::new((!block.name.is_temp()).then(|| block.name.clone()));
      self.local_bbs.insert(block.name.clone(), bb);
    }
    // build on all basic blocks
    for bb in ast.bbs.iter() {
      self.build_on_block(unwrap_ast!(bb, Block));
    }
  }

  /// Builds on function declarations.
  fn build_on_fun_decl(&mut self, ast: &ast::FunDecl) {
    // get function type
    let ty = Type::get_function(
      ast.params.iter().map(|a| self.generate_type(a)).collect(),
      ast
        .ret
        .as_ref()
        .map_or(Type::get_unit(), |a| self.generate_type(a)),
    );
    // create function declaration
    let decl = structs::Function::new_decl(ast.name.clone(), ty);
    // add to global function map
    self.global_funcs.insert(ast.name.clone(), decl.clone());
    // add to program
    self.program.add_func(decl);
  }

  /// Builds on basic blocks.
  fn build_on_block(&mut self, ast: &ast::Block) {
    todo!()
  }

  /// Generates the type by the specific AST.
  fn generate_type(&self, ast: &AstBox) -> Type {
    match &ast.kind {
      AstKind::IntType(_) => Type::get_i32(),
      AstKind::ArrayType(ast) => Type::get_array(self.generate_type(&ast.base), ast.len),
      AstKind::PointerType(ast) => Type::get_pointer(self.generate_type(&ast.base)),
      AstKind::FunType(ast) => Type::get_function(
        ast.params.iter().map(|a| self.generate_type(a)).collect(),
        ast
          .ret
          .as_ref()
          .map_or(Type::get_unit(), |a| self.generate_type(a)),
      ),
      _ => panic!("invalid type AST"),
    }
  }

  /// Generates the value by the specific AST.
  fn generate_value(&self, ast: &AstBox) -> ValueRc {
    match &ast.kind {
      AstKind::SymbolRef(ast) => todo!(),
      AstKind::IntVal(ast) => todo!(),
      AstKind::UndefVal(ast) => todo!(),
      AstKind::Aggregate(ast) => todo!(),
      AstKind::ZeroInit(ast) => todo!(),
      _ => panic!("invalid value AST"),
    }
  }

  /// Generates the statement by the specific AST.
  fn generate_stmt(&self, ast: &AstBox) -> ValueRc {
    match &ast.kind {
      AstKind::SymbolDef(ast) => todo!(),
      AstKind::Store(ast) => todo!(),
      AstKind::Branch(ast) => todo!(),
      AstKind::Jump(ast) => todo!(),
      AstKind::FunCall(ast) => todo!(),
      AstKind::Return(ast) => todo!(),
      _ => panic!("invalid statement"),
    }
  }

  /// Generates the instruction by the specific AST.
  fn generate_inst(&self, ast: &AstBox) -> ValueRc {
    match &ast.kind {
      AstKind::MemDecl(ast) => todo!(),
      AstKind::Load(ast) => todo!(),
      AstKind::GetPointer(ast) => todo!(),
      AstKind::BinaryExpr(ast) => todo!(),
      AstKind::UnaryExpr(ast) => todo!(),
      AstKind::FunCall(ast) => todo!(),
      AstKind::Phi(ast) => todo!(),
      _ => panic!("invalid instruction"),
    }
  }
}

/// Helper trait, for checking if the symbol name is a temporary name.
trait Symbol {
  fn is_temp(&self) -> bool;
}

impl Symbol for String {
  fn is_temp(&self) -> bool {
    self.chars().all(|c| c == '%' || c.is_numeric())
  }
}
