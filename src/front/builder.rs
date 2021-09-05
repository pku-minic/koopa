use crate::front::ast::{self, AstBox, AstKind};
use crate::front::span::{Error, Span};
use crate::ir::core::ValueRc;
use crate::ir::instructions as inst;
use crate::ir::structs::{self, BasicBlockRc, FunctionRc, FunctionRef, Program};
use crate::ir::types::{Type, TypeKind};
use crate::ir::values;
use crate::{log_error, return_error};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Builder for building Koopa IR from AST.
pub struct Builder {
  program: Program,
  global_vars: HashMap<String, ValueRc>,
  global_funcs: HashMap<String, FunctionRef>,
  local_bbs: HashMap<String, BasicBlockInfo>,
  local_symbols: HashSet<String>,
}

/// Basic block information.
struct BasicBlockInfo {
  bb: BasicBlockRc,
  preds: Vec<String>,
  local_defs: HashMap<String, ValueRc>,
}

/// Result returned by value generator methods in `Builder`.
type ValueResult = std::result::Result<ValueRc, Error>;

/// Unwraps the specific AST by its kind.
macro_rules! unwrap_ast {
  ($ast:expr, $kind:ident) => {
    match &$ast.kind {
      AstKind::$kind(ast) => ast,
      _ => panic!("invalid `{}` AST", stringify!($kind)),
    }
  };
}

impl Builder {
  /// Creates a new builder.
  pub fn new() -> Self {
    Self {
      program: Program::default(),
      global_vars: HashMap::new(),
      global_funcs: HashMap::new(),
      local_bbs: HashMap::new(),
      local_symbols: HashSet::new(),
    }
  }

  /// Builds the specific AST into IR.
  pub fn build_on(&mut self, ast: &AstBox) {
    match &ast.kind {
      AstKind::GlobalDef(def) => self.build_on_global_def(&ast.span, def),
      AstKind::FunDef(def) => self.build_on_fun_def(&ast.span, def),
      AstKind::FunDecl(decl) => self.build_on_fun_decl(&ast.span, decl),
      AstKind::Error(_) | AstKind::End(_) => { /* ignore errors and ends */ }
      _ => panic!("invalid AST input"),
    }
  }

  /// Consumes and get the generated program.
  pub fn program(self) -> Program {
    self.program
  }

  /// Builds on global symbol definitions.
  fn build_on_global_def(&mut self, span: &Span, ast: &ast::GlobalDef) {
    // create global allocation
    let decl = unwrap_ast!(ast.value, GlobalDecl);
    if let Ok(init) = self.generate_init(self.generate_type(&decl.ty), &decl.init) {
      let alloc = inst::GlobalAlloc::new(init);
      // set name for the created value
      if !ast.name.is_temp() {
        alloc.borrow_mut().set_name(Some(ast.name.clone()));
      }
      // add to global variable map
      if self
        .global_vars
        .insert(ast.name.clone(), alloc.clone())
        .is_some()
      {
        log_error!(
          span,
          "global variable '{}' has already been defined",
          ast.name
        );
      }
      // add to program
      self.program.add_var(alloc);
    }
  }

  /// Builds on function definitions.
  fn build_on_fun_def(&mut self, span: &Span, ast: &ast::FunDef) {
    // create argument references
    let args = ast.params.iter().enumerate().map(|(i, (name, ty))| {
      // create argument reference
      let arg = values::ArgRef::new(self.generate_type(ty), i);
      if !name.is_temp() {
        arg.borrow_mut().set_name(Some(name.clone()));
      }
      (name.clone(), arg)
    });
    let args: HashMap<_, _> = args.collect();
    // create function definition
    let def = structs::Function::new(
      ast.name.clone(),
      args.values().cloned().collect(),
      ast
        .ret
        .as_ref()
        .map_or(Type::get_unit(), |a| self.generate_type(a)),
    );
    // add to global function map
    if self
      .global_funcs
      .insert(ast.name.clone(), Rc::downgrade(&def))
      .is_some()
    {
      log_error!(span, "function '{}' has already been defined", ast.name);
    }
    // add to program
    self.program.add_func(def.clone());
    // initialize local basic block map
    self.init_local_bbs(def, args, &ast.bbs);
    // reset local symbol set
    self.local_symbols.clear();
    // build on all basic blocks
    for bb in &ast.bbs {
      self.build_on_block(unwrap_ast!(bb, Block));
    }
  }

  /// Builds on function declarations.
  fn build_on_fun_decl(&mut self, span: &Span, ast: &ast::FunDecl) {
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
    if self
      .global_funcs
      .insert(ast.name.clone(), Rc::downgrade(&decl))
      .is_some()
    {
      log_error!(span, "function '{}' has already been defined", ast.name);
    }
    // add to program
    self.program.add_func(decl);
  }

  /// Initializes local basic block map.
  fn init_local_bbs(&mut self, def: FunctionRc, args: HashMap<String, ValueRc>, bbs: &[AstBox]) {
    // create all basic blocks
    self.local_bbs.clear();
    for bb in bbs {
      let block = unwrap_ast!(bb, Block);
      let span = &bb.span;
      let bb = structs::BasicBlock::new((!block.name.is_temp()).then(|| block.name.clone()));
      // add to local basic block map
      if self
        .local_bbs
        .insert(
          block.name.clone(),
          BasicBlockInfo {
            bb: bb.clone(),
            preds: Vec::new(),
            local_defs: HashMap::new(),
          },
        )
        .is_some()
      {
        log_error!(
          span,
          "basic block '{}' has already been defined",
          block.name
        );
      }
      // add to the current function
      def.borrow_mut().add_bb(bb);
    }
    // add argument references to the entry basic block
    let first_bb = unwrap_ast!(bbs.first().unwrap(), Block);
    let first_bb_info = &mut self.local_bbs.get_mut(&first_bb.name).unwrap();
    first_bb_info.local_defs = args;
    // fill predecessors
    for bb in bbs {
      let block = unwrap_ast!(bb, Block);
      let last_inst = block.stmts.last().unwrap();
      let mut add_pred = |bb_name| {
        if let Some(info) = self.local_bbs.get_mut(bb_name) {
          info.preds.push(block.name.clone());
        } else {
          log_error!(last_inst.span, "invalid basic block name {}", bb_name);
        }
      };
      match &last_inst.kind {
        AstKind::Branch(ast::Branch { cond: _, tbb, fbb }) => {
          add_pred(tbb);
          add_pred(fbb);
        }
        AstKind::Jump(ast::Jump { target }) => add_pred(target),
        AstKind::Return(_) | AstKind::Error(_) => {}
        _ => panic!("invalid end statement"),
      }
    }
  }

  /// Builds on basic blocks.
  fn build_on_block(&mut self, ast: &ast::Block) {
    // generate each statements
    for stmt in &ast.stmts {
      if let Ok(stmt) = self.generate_stmt(&ast.name, &stmt) {
        // add value to the current basic block
        self.local_bbs[&ast.name].bb.borrow_mut().add_inst(stmt);
      }
    }
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

  /// Generates the initializer by the specific AST.
  fn generate_init(&self, ty: Type, ast: &AstBox) -> ValueResult {
    match &ast.kind {
      AstKind::IntVal(ast) => Ok(values::Integer::get(ast.value)),
      AstKind::UndefVal(_) => Ok(values::Undef::get(ty)),
      AstKind::ZeroInit(_) => Ok(values::ZeroInit::get(ty)),
      AstKind::Aggregate(agg) => {
        let ty = match ty.kind() {
          TypeKind::Array(base, len) => {
            if *len != agg.elems.len() {
              log_error!(
                ast.span,
                "expected array length {}, found length {}",
                len,
                agg.elems.len()
              );
            }
            base
          }
          TypeKind::Pointer(base) => base,
          _ => return_error!(ast.span, "invalid aggregate type '{}'", ty),
        };
        Ok(values::Aggregate::new(
          agg
            .elems
            .iter()
            .map(|e| self.generate_init(ty.clone(), e))
            .collect::<Result<Vec<_>, _>>()?,
        ))
      }
      _ => panic!("invalid initializer AST"),
    }
  }

  /// Generates the value by the specific AST.
  fn generate_value(&self, bb_name: &str, ty: Type, ast: &AstBox) -> ValueResult {
    match &ast.kind {
      AstKind::SymbolRef(sym) => {
        let bb_info = &self.local_bbs[bb_name];
        if let Some(value) = bb_info.local_defs.get(&sym.symbol) {
          // symbol found in the current basic block
          Ok(value.clone())
        } else if !bb_info.preds.is_empty() {
          // symbol not found, try to find in all predecessors
          if let Some(value) = bb_info
            .preds
            .iter()
            .find_map(|pred| self.generate_value(pred, ty.clone(), ast).ok())
          {
            // check the type of the value to prevent duplication of definitions
            if value.ty() == &ty {
              Ok(value)
            } else {
              return_error!(
                ast.span,
                "type mismatch, expected '{}', found '{}'",
                ty,
                value.ty()
              )
            }
          } else {
            // symbol not found
            return_error!(ast.span, "symbol '{}' not found", sym.symbol);
          }
        } else {
          // symbol not found
          return_error!(ast.span, "symbol '{}' not found", sym.symbol);
        }
      }
      _ => self.generate_init(ty, ast),
    }
  }

  /// Generates the statement by the specific AST.
  fn generate_stmt(&mut self, bb_name: &str, ast: &AstBox) -> ValueResult {
    match &ast.kind {
      AstKind::Store(ast) => self.generate_store(ast),
      AstKind::Branch(ast) => self.generate_branch(ast),
      AstKind::Jump(ast) => self.generate_jump(ast),
      AstKind::FunCall(ast) => self.generate_fun_call(ast),
      AstKind::Return(ast) => self.generate_return(ast),
      AstKind::Error(_) => todo!(),
      AstKind::SymbolDef(def) => {
        // generate the value of the instruction
        let inst = self.generate_inst(&def.value)?;
        // try to add to local basic block
        if !self.local_symbols.insert(def.name.clone()) {
          log_error!(ast.span, "symbol '{}' has already been defined", def.name);
        }
        self
          .local_bbs
          .get_mut(bb_name)
          .unwrap()
          .local_defs
          .insert(def.name.clone(), inst.clone());
        Ok(inst)
      }
      _ => panic!("invalid statement"),
    }
  }

  /// Generates the instruction by the specific AST.
  fn generate_inst(&self, ast: &AstBox) -> ValueResult {
    match &ast.kind {
      AstKind::MemDecl(ast) => self.generate_mem_decl(ast),
      AstKind::Load(ast) => self.generate_load(ast),
      AstKind::GetPointer(ast) => self.generate_get_pointer(ast),
      AstKind::BinaryExpr(ast) => self.generate_binary_expr(ast),
      AstKind::UnaryExpr(ast) => self.generate_unary_expr(ast),
      AstKind::FunCall(ast) => self.generate_fun_call(ast),
      AstKind::Phi(ast) => self.generate_phi(ast),
      _ => panic!("invalid instruction"),
    }
  }

  /// Generates memory declarations.
  fn generate_mem_decl(&self, ast: &ast::MemDecl) -> ValueResult {
    todo!()
  }

  /// Generates loads.
  fn generate_load(&self, ast: &ast::Load) -> ValueResult {
    todo!()
  }

  /// Generates stores.
  fn generate_store(&self, ast: &ast::Store) -> ValueResult {
    todo!()
  }

  /// Generates pointer calculations.
  fn generate_get_pointer(&self, ast: &ast::GetPointer) -> ValueResult {
    todo!()
  }

  /// Generates binary expressions.
  fn generate_binary_expr(&self, ast: &ast::BinaryExpr) -> ValueResult {
    todo!()
  }

  /// Generates unary expressions.
  fn generate_unary_expr(&self, ast: &ast::UnaryExpr) -> ValueResult {
    todo!()
  }

  /// Generates branchs.
  fn generate_branch(&self, ast: &ast::Branch) -> ValueResult {
    todo!()
  }

  /// Generates jumps.
  fn generate_jump(&self, ast: &ast::Jump) -> ValueResult {
    todo!()
  }

  /// Generates function calls.
  fn generate_fun_call(&self, ast: &ast::FunCall) -> ValueResult {
    todo!()
  }

  /// Generates returns.
  fn generate_return(&self, ast: &ast::Return) -> ValueResult {
    todo!()
  }

  /// Generates phi functions.
  fn generate_phi(&self, ast: &ast::Phi) -> ValueResult {
    todo!()
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
