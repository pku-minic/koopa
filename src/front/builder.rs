//! Koopa IR builder ([`Builder`]) related implementations.

use crate::front::ast::{self, AstBox, AstKind};
use crate::front::span::{Error, Span};
use crate::ir::builder_traits::*;
use crate::ir::dfg::DataFlowGraph;
use crate::ir::{BasicBlock, Function, FunctionData, Program, Type, TypeKind, Value};
use crate::{log_error, log_warning, return_error};
use std::collections::{HashMap, HashSet, VecDeque};

/// Basic block information.
struct BasicBlockInfo {
  bb: BasicBlock,
  preds: Vec<String>,
  local_defs: HashMap<String, Value>,
}

impl BasicBlockInfo {
  fn new(bb: BasicBlock) -> Self {
    Self {
      bb,
      preds: Vec::new(),
      local_defs: HashMap::new(),
    }
  }
}

/// Builder for building Koopa IR from ASTs.
///
/// `Builder` performs semantic checks (e.g. type checking) on
/// Koopa IR ASTs, and then builds the in-memory form Koopa IR.
#[derive(Default)]
pub struct Builder {
  program: Program,
  global_vars: HashMap<String, Value>,
  global_funcs: HashMap<String, Function>,
  local_bbs: HashMap<String, BasicBlockInfo>,
  local_symbols: HashSet<String>,
}

/// Result returned by value generator methods in `Builder`.
type ValueResult = Result<Value, Error>;

/// Unwraps the given AST by its kind.
macro_rules! unwrap_ast {
  ($ast:expr, $kind:ident) => {
    match &$ast.kind {
      AstKind::$kind(ast) => ast,
      _ => panic!("invalid `{}` AST", stringify!($kind)),
    }
  };
}

/// Generates global/local initializer, used in method
/// `generate_global_init` and `generate_local_init`.
macro_rules! generate_init {
  ($ty:expr, $ast:expr, $builder:expr, $agg_rec:expr, $elem_ty:ident) => {
    match &$ast.kind {
      AstKind::UndefVal(_) => Ok($builder.undef($ty.clone())),
      AstKind::ZeroInit(_) => Ok($builder.zero_init($ty.clone())),
      AstKind::IntVal(int) => {
        if !$ty.is_i32() {
          return_error!(
            $ast.span,
            "found type '{}', but it can not be applied to integers",
            $ty
          );
        }
        Ok($builder.integer(int.value))
      }
      AstKind::Aggregate(agg) => {
        let $elem_ty = match $ty.kind() {
          TypeKind::Array(base, len) => {
            if *len != agg.elems.len() {
              log_error!(
                $ast.span,
                "expected array length {}, found length {}",
                len,
                agg.elems.len()
              );
            }
            base
          }
          TypeKind::Pointer(base) => base,
          _ => return_error!($ast.span, "invalid aggregate type '{}'", $ty),
        };
        let elems = agg.elems.iter().map($agg_rec).collect::<Result<_, _>>()?;
        Ok($builder.aggregate(elems))
      }
      _ => panic!("invalid initializer AST"),
    }
  };
}

impl Builder {
  /// Creates a new builder.
  pub fn new() -> Self {
    Self::default()
  }

  /// Builds the given AST into IR.
  pub fn build_on(&mut self, ast: &AstBox) {
    match &ast.kind {
      AstKind::GlobalDef(def) => self.build_on_global_def(&ast.span, def),
      AstKind::FunDef(def) => self.build_on_fun_def(&ast.span, def),
      AstKind::FunDecl(decl) => self.build_on_fun_decl(&ast.span, decl),
      AstKind::Error(_) | AstKind::End(_) => { /* ignore errors and ends */ }
      _ => panic!("invalid AST input"),
    }
  }

  /// Consumes the builder and get the generated program.
  ///
  /// Available only when no error has occurred.
  pub fn program(self) -> Program {
    self.program
  }

  /// Returns a mutable reference to the data flow graph
  /// of the given function.
  fn dfg_mut(&mut self, func: Function) -> &mut DataFlowGraph {
    self.program.func_mut(func).dfg_mut()
  }

  /// Returns the type of the given value.
  fn value_ty(&self, func: Function, value: Value) -> Type {
    if value.is_global() {
      self.program.borrow_value(value).ty().clone()
    } else {
      self.program.func(func).dfg().value(value).ty().clone()
    }
  }

  /// Returns the parameter types of the given basic block.
  fn bb_params_ty(&self, func: Function, bb: BasicBlock) -> Vec<Type> {
    self
      .program
      .func(func)
      .dfg()
      .bb(bb)
      .params()
      .iter()
      .map(|p| self.program.func(func).dfg().value(*p).ty().clone())
      .collect()
  }

  /// Builds on global symbol definitions.
  fn build_on_global_def(&mut self, span: &Span, ast: &ast::GlobalDef) {
    // create global allocation
    let decl = unwrap_ast!(ast.value, GlobalDecl);
    if let Ok(init) = self.generate_global_init(&Self::generate_type(&decl.ty), &decl.init) {
      let alloc = self.program.new_value().global_alloc(init);
      // set name for the created value
      if !ast.name.is_temp() {
        self.program.set_value_name(alloc, Some(ast.name.clone()));
      }
      // add to global variable map
      if self.global_funcs.contains_key(&ast.name)
        || self.global_vars.insert(ast.name.clone(), alloc).is_some()
      {
        log_error!(
          span,
          "global symbol '{}' has already been defined",
          ast.name
        );
      }
    }
  }

  /// Builds on function definitions.
  fn build_on_fun_def(&mut self, span: &Span, ast: &ast::FunDef) {
    // generate return type
    let ret_ty = ast
      .ret
      .as_ref()
      .map_or_else(Type::get_unit, Self::generate_type);
    // create function definition
    let def = FunctionData::with_param_names(
      ast.name.clone(),
      ast
        .params
        .iter()
        .map(|(n, a)| ((!n.is_temp()).then(|| n.clone()), Self::generate_type(a)))
        .collect(),
      ret_ty.clone(),
    );
    // create argument map
    let mut args = HashMap::new();
    for ((n, a), p) in ast.params.iter().zip(def.params()) {
      if args.insert(n.clone(), *p).is_some() {
        log_error!(a.span, "duplicate parameter name '{}'", n);
      }
    }
    // add to program
    let func = self.program.new_func(def);
    // add to global function map
    if self.global_vars.contains_key(&ast.name)
      || self.global_funcs.insert(ast.name.clone(), func).is_some()
    {
      log_error!(
        span,
        "global function '{}' has already been defined",
        ast.name
      );
    }
    // reset local symbol set
    self.local_symbols.clear();
    // get basic block list
    let bbs = self.get_block_list(&ast.bbs);
    // initialize local basic block map
    self.init_local_bbs(func, args, &bbs);
    // build on all basic blocks
    for block in bbs {
      self.build_on_block(func, &ret_ty, block);
    }
  }

  /// Builds on function declarations.
  fn build_on_fun_decl(&mut self, span: &Span, ast: &ast::FunDecl) {
    // create function declaration
    let decl = FunctionData::new_decl(
      ast.name.clone(),
      ast.params.iter().map(Self::generate_type).collect(),
      ast
        .ret
        .as_ref()
        .map_or_else(Type::get_unit, Self::generate_type),
    );
    // add to program
    let func = self.program.new_func(decl);
    // add to global function map
    if self.global_vars.contains_key(&ast.name)
      || self.global_funcs.insert(ast.name.clone(), func).is_some()
    {
      log_error!(
        span,
        "global function '{}' has already been defined",
        ast.name
      );
    }
  }

  /// Gets basic block list in BFS order.
  fn get_block_list<'a>(&self, bbs: &'a [AstBox]) -> Vec<&'a ast::Block> {
    // initialize queue and set
    let mut queue = VecDeque::new();
    let mut visited = HashSet::new();
    let entry_bb_name = &unwrap_ast!(bbs.first().unwrap(), Block).name;
    queue.push_back(entry_bb_name);
    // initialize basic block map
    let mut bb_map = HashMap::new();
    for bb in bbs {
      let block = unwrap_ast!(bb, Block);
      if bb_map.insert(&block.name, (&bb.span, block)).is_some() {
        log_error!(
          bb.span,
          "basic block '{}' has already been defined",
          block.name
        );
      }
    }
    // visit blocks
    let mut bb_list = Vec::new();
    while let Some(bb) = queue.pop_front() {
      if visited.insert(bb) {
        let info = bb_map[bb];
        // add to basic block list
        bb_list.push(info.1);
        // add the successors to queue
        let last_stmt = info.1.stmts.last().unwrap();
        let mut add_target = |bb_name| {
          if bb_name == entry_bb_name {
            log_error!(
              last_stmt.span,
              "the entry basic block should not have any predecessors"
            );
          } else if bb_map.contains_key(bb_name) {
            queue.push_back(bb_name);
          } else {
            log_error!(last_stmt.span, "invalid basic block name '{}'", bb_name);
          }
        };
        match &last_stmt.kind {
          AstKind::Branch(ast::Branch { tbb, fbb, .. }) => {
            add_target(tbb);
            add_target(fbb);
          }
          AstKind::Jump(ast::Jump { target, .. }) => add_target(target),
          AstKind::Return(_) | AstKind::Error(_) => {}
          _ => panic!("invalid end statement"),
        }
      }
    }
    // check if there are any unvisited blocks
    for (bb_name, (span, _)) in bb_map {
      if !visited.contains(bb_name) {
        log_warning!(span, "basic block '{}' is unreachable, skipped", bb_name);
      }
    }
    bb_list
  }

  /// Initializes local basic block map.
  fn init_local_bbs(&mut self, func: Function, args: HashMap<String, Value>, bbs: &[&ast::Block]) {
    // create all basic blocks
    self.local_bbs.clear();
    for block in bbs {
      // create name and type of block parameters
      let params = block
        .params
        .iter()
        .map(|(n, a)| ((!n.is_temp()).then(|| n.clone()), Self::generate_type(a)))
        .collect();
      // create the current basic block
      let bb = self
        .dfg_mut(func)
        .new_bb()
        .basic_block_with_param_names((!block.name.is_temp()).then(|| block.name.clone()), params);
      // add to function layout
      self
        .program
        .func_mut(func)
        .layout_mut()
        .bbs_mut()
        .push_key_back(bb)
        .unwrap();
      // create basic block info
      let mut info = BasicBlockInfo::new(bb);
      // add basic block parameter to local definitions
      let params = self.program.func(func).dfg().bb(bb).params().to_vec();
      for ((n, a), p) in block.params.iter().zip(params.into_iter()) {
        // check if has already been defined
        if self.global_vars.contains_key(n) || !self.local_symbols.insert(n.clone()) {
          log_error!(a.span, "symbol '{}' has already been defined", n);
        }
        // add to local basic block
        info.local_defs.insert(n.clone(), p);
      }
      // insert block info to local basic block map
      self.local_bbs.insert(block.name.clone(), info);
    }
    // add argument references local symbols
    self.local_symbols.extend(args.keys().cloned());
    // add argument references to the entry basic block
    let entry_bb_name = &bbs[0].name;
    let entry_info = &mut self.local_bbs.get_mut(entry_bb_name).unwrap();
    entry_info.local_defs = args;
    // fill predecessors
    for block in bbs {
      let last_inst = block.stmts.last().unwrap();
      let mut add_pred = |bb_name| {
        self
          .local_bbs
          .get_mut(bb_name)
          .unwrap()
          .preds
          .push(block.name.clone());
      };
      match &last_inst.kind {
        AstKind::Branch(ast::Branch { tbb, fbb, .. }) => {
          add_pred(tbb);
          add_pred(fbb);
        }
        AstKind::Jump(ast::Jump { target, .. }) => add_pred(target),
        _ => {}
      }
    }
  }

  /// Builds on basic blocks.
  fn build_on_block(&mut self, func: Function, ret_ty: &Type, ast: &ast::Block) {
    // generate each statements
    for stmt in &ast.stmts {
      if let Ok(stmt) = self.generate_stmt(func, &ast.name, ret_ty, stmt) {
        let info = self.local_bbs.get_mut(&ast.name).unwrap();
        // add statement to the current basic block
        self
          .program
          .func_mut(func)
          .layout_mut()
          .bb_mut(info.bb)
          .insts_mut()
          .push_key_back(stmt)
          .unwrap();
      }
    }
  }

  /// Generates the type by the given AST.
  fn generate_type(ast: &AstBox) -> Type {
    match &ast.kind {
      AstKind::IntType(_) => Type::get_i32(),
      AstKind::ArrayType(ast) => Type::get_array(Self::generate_type(&ast.base), ast.len),
      AstKind::PointerType(ast) => Type::get_pointer(Self::generate_type(&ast.base)),
      AstKind::FunType(ast) => Type::get_function(
        ast.params.iter().map(Self::generate_type).collect(),
        ast
          .ret
          .as_ref()
          .map_or(Type::get_unit(), Self::generate_type),
      ),
      _ => panic!("invalid type AST"),
    }
  }

  /// Generates the global initializer by the given AST.
  fn generate_global_init(&mut self, ty: &Type, ast: &AstBox) -> ValueResult {
    generate_init!(
      ty,
      ast,
      self.program.new_value(),
      |e| self.generate_global_init(elem_ty, e),
      elem_ty
    )
  }

  /// Generates the local initializer by the given AST.
  fn generate_local_init(&mut self, func: Function, ty: &Type, ast: &AstBox) -> ValueResult {
    generate_init!(
      ty,
      ast,
      self.dfg_mut(func).new_value(),
      |e| self.generate_local_init(func, elem_ty, e),
      elem_ty
    )
  }

  /// Generates the value by the given AST.
  fn generate_value(
    &mut self,
    func: Function,
    bb_name: &str,
    ty: &Type,
    ast: &AstBox,
  ) -> ValueResult {
    match &ast.kind {
      AstKind::SymbolRef(sym) => {
        let value = self.generate_symbol(&ast.span, bb_name, &sym.symbol)?;
        // check the type of the value to prevent duplication of definitions
        let value_ty = self.value_ty(func, value);
        if &value_ty == ty {
          Ok(value)
        } else {
          return_error!(
            ast.span,
            "type mismatch, expected '{}', found '{}'",
            ty,
            value_ty
          )
        }
      }
      _ => self.generate_local_init(func, ty, ast),
    }
  }

  /// Generates the symbol by the symbol name.
  fn generate_symbol(&self, span: &Span, bb_name: &str, symbol: &str) -> ValueResult {
    // try to find symbol in global scope
    // if not found, find symbol in local definitions
    let mut visited_bbs = HashSet::new();
    self
      .global_vars
      .get(symbol)
      .copied()
      .or_else(|| self.generate_local_symbol(&mut visited_bbs, bb_name, symbol))
      .ok_or_else(|| return_error!(span, "symbol '{}' not found", symbol))
  }

  /// Generates the symbol locally by the symbol name.
  fn generate_local_symbol<'a>(
    &'a self,
    visited_bbs: &mut HashSet<&'a str>,
    bb_name: &'a str,
    symbol: &str,
  ) -> Option<Value> {
    if visited_bbs.insert(bb_name) {
      // find symbol in local scope of the current basic block
      // if not found, try to find symbol in all predecessors
      let bb_info = &self.local_bbs[bb_name];
      bb_info.local_defs.get(symbol).copied().or_else(|| {
        bb_info
          .preds
          .iter()
          .find_map(|pred| self.generate_local_symbol(visited_bbs, pred, symbol))
      })
    } else {
      None
    }
  }

  /// Generates the basic block handle by the given basic block name.
  fn generate_bb(&self, span: &Span, bb_name: &str) -> Result<BasicBlock, Error> {
    self
      .local_bbs
      .get(bb_name)
      .map(|info| info.bb)
      .ok_or_else(|| log_error!(span, "invalid basic block name '{}'", bb_name))
  }

  /// Generates argument list.
  fn generate_args(
    &mut self,
    func: Function,
    span: &Span,
    bb_name: &str,
    args: &[AstBox],
    args_ty: &[Type],
  ) -> Result<Vec<Value>, Error> {
    // check length of argument list
    if args.len() != args.len() {
      return_error!(
        span,
        "expected {} {}, found {} {}",
        args.len(),
        "arguments".to_plural(args.len()),
        args.len(),
        "arguments".to_plural(args.len())
      );
    }
    // generate arguments
    args
      .iter()
      .zip(args_ty)
      .map(|(a, ty)| self.generate_value(func, bb_name, ty, a))
      .collect()
  }

  /// Generates the statement by the given AST.
  fn generate_stmt(
    &mut self,
    func: Function,
    bb_name: &str,
    ret_ty: &Type,
    ast: &AstBox,
  ) -> ValueResult {
    match &ast.kind {
      AstKind::Store(store) => self.generate_store(func, &ast.span, bb_name, store),
      AstKind::Branch(br) => self.generate_branch(func, &ast.span, bb_name, br),
      AstKind::Jump(jump) => self.generate_jump(func, &ast.span, bb_name, jump),
      AstKind::FunCall(call) => self.generate_fun_call(func, &ast.span, bb_name, call),
      AstKind::Return(ret) => self.generate_return(func, &ast.span, bb_name, ret_ty, ret),
      AstKind::Error(_) => Error::default().into(),
      AstKind::SymbolDef(def) => {
        // check if has already been defined
        if self.global_vars.contains_key(&def.name) || !self.local_symbols.insert(def.name.clone())
        {
          log_error!(ast.span, "symbol '{}' has already been defined", def.name);
        }
        // generate the value of the instruction
        let inst = self.generate_inst(func, bb_name, &def.value)?;
        // check type
        if self.value_ty(func, inst).is_unit() {
          return_error!(
            ast.span,
            "symbol '{}' is defined as a unit type, which is not allowed",
            def.name
          );
        }
        // set value name
        if !def.name.is_temp() {
          self
            .dfg_mut(func)
            .set_value_name(inst, Some(def.name.clone()));
        }
        // add to local basic block
        self
          .local_bbs
          .get_mut(bb_name)
          .unwrap()
          .local_defs
          .insert(def.name.clone(), inst);
        Ok(inst)
      }
      _ => panic!("invalid statement"),
    }
  }

  /// Generates the instruction by the given AST.
  fn generate_inst(&mut self, func: Function, bb_name: &str, ast: &AstBox) -> ValueResult {
    match &ast.kind {
      AstKind::MemDecl(ast) => self.generate_mem_decl(func, ast),
      AstKind::Load(load) => self.generate_load(func, &ast.span, bb_name, load),
      AstKind::GetPointer(gp) => self.generate_get_pointer(func, &ast.span, bb_name, gp),
      AstKind::GetElementPointer(gep) => {
        self.generate_get_element_pointer(func, &ast.span, bb_name, gep)
      }
      AstKind::BinaryExpr(ast) => self.generate_binary_expr(func, bb_name, ast),
      AstKind::FunCall(call) => self.generate_fun_call(func, &ast.span, bb_name, call),
      _ => panic!("invalid instruction"),
    }
  }

  /// Generates memory declarations.
  fn generate_mem_decl(&mut self, func: Function, ast: &ast::MemDecl) -> ValueResult {
    let ty = Self::generate_type(&ast.ty);
    Ok(self.dfg_mut(func).new_value().alloc(ty))
  }

  /// Generates loads.
  fn generate_load(
    &mut self,
    func: Function,
    span: &Span,
    bb_name: &str,
    ast: &ast::Load,
  ) -> ValueResult {
    // get source value
    let src = self.generate_symbol(span, bb_name, &ast.symbol)?;
    // check source type
    let src_ty = self.value_ty(func, src);
    if !matches!(src_ty.kind(), TypeKind::Pointer(..)) {
      return_error!(span, "expected pointer type, found '{}'", src_ty);
    }
    Ok(self.dfg_mut(func).new_value().load(src))
  }

  /// Generates stores.
  fn generate_store(
    &mut self,
    func: Function,
    span: &Span,
    bb_name: &str,
    ast: &ast::Store,
  ) -> ValueResult {
    // get destination value
    let dest = self.generate_symbol(span, bb_name, &ast.symbol)?;
    // check destination type & get source type
    let dest_ty = self.value_ty(func, dest);
    let src_ty = match dest_ty.kind() {
      TypeKind::Pointer(base) => base,
      _ => return_error!(span, "expected pointer type, found '{}'", dest_ty),
    };
    // get source value
    let value = self.generate_value(func, bb_name, src_ty, &ast.value)?;
    Ok(self.dfg_mut(func).new_value().store(value, dest))
  }

  /// Generates pointer calculations.
  fn generate_get_pointer(
    &mut self,
    func: Function,
    span: &Span,
    bb_name: &str,
    ast: &ast::GetPointer,
  ) -> ValueResult {
    // get source value
    let src = self.generate_symbol(span, bb_name, &ast.symbol)?;
    let src_ty = self.value_ty(func, src);
    if !matches!(src_ty.kind(), TypeKind::Pointer(..)) {
      return_error!(span, "expected pointer type, found '{}'", src_ty);
    }
    // get index
    let index = self.generate_value(func, bb_name, &Type::get_i32(), &ast.value)?;
    Ok(self.dfg_mut(func).new_value().get_ptr(src, index))
  }

  /// Generates element pointer calculations.
  fn generate_get_element_pointer(
    &mut self,
    func: Function,
    span: &Span,
    bb_name: &str,
    ast: &ast::GetElementPointer,
  ) -> ValueResult {
    // get source value
    let src = self.generate_symbol(span, bb_name, &ast.symbol)?;
    let src_ty = self.value_ty(func, src);
    if !matches!(src_ty.kind(), TypeKind::Pointer(ty) if matches!(ty.kind(), TypeKind::Array(..))) {
      return_error!(span, "expected a pointer of array, found '{}'", src_ty);
    }
    // get index
    let index = self.generate_value(func, bb_name, &Type::get_i32(), &ast.value)?;
    Ok(self.dfg_mut(func).new_value().get_elem_ptr(src, index))
  }

  /// Generates binary expressions.
  fn generate_binary_expr(
    &mut self,
    func: Function,
    bb_name: &str,
    ast: &ast::BinaryExpr,
  ) -> ValueResult {
    let ty = Type::get_i32();
    // get lhs & rhs
    let lhs = self.generate_value(func, bb_name, &ty, &ast.lhs)?;
    let rhs = self.generate_value(func, bb_name, &ty, &ast.rhs)?;
    Ok(self.dfg_mut(func).new_value().binary(ast.op, lhs, rhs))
  }

  /// Generates branchs.
  fn generate_branch(
    &mut self,
    func: Function,
    span: &Span,
    bb_name: &str,
    ast: &ast::Branch,
  ) -> ValueResult {
    // get condition
    let cond = self.generate_value(func, bb_name, &Type::get_i32(), &ast.cond)?;
    // get true target basic block and true arguments
    let tbb = self.generate_bb(span, &ast.tbb)?;
    let tbb_ty = self.bb_params_ty(func, tbb);
    let targs = self.generate_args(func, span, bb_name, &ast.targs, &tbb_ty)?;
    // get false target basic block and false arguments
    let fbb = self.generate_bb(span, &ast.fbb)?;
    let fbb_ty = self.bb_params_ty(func, fbb);
    let fargs = self.generate_args(func, span, bb_name, &ast.fargs, &fbb_ty)?;
    Ok(
      self
        .dfg_mut(func)
        .new_value()
        .branch_with_args(cond, tbb, fbb, targs, fargs),
    )
  }

  /// Generates jumps.
  fn generate_jump(
    &mut self,
    func: Function,
    span: &Span,
    bb_name: &str,
    ast: &ast::Jump,
  ) -> ValueResult {
    // generate target basic block
    let target = self.generate_bb(span, &ast.target)?;
    // generate arguments
    let target_ty = self.bb_params_ty(func, target);
    let args = self.generate_args(func, span, bb_name, &ast.args, &target_ty)?;
    Ok(self.dfg_mut(func).new_value().jump_with_args(target, args))
  }

  /// Generates function calls.
  fn generate_fun_call(
    &mut self,
    func: Function,
    span: &Span,
    bb_name: &str,
    ast: &ast::FunCall,
  ) -> ValueResult {
    // get callee
    let callee = *self
      .global_funcs
      .get(&ast.fun)
      .ok_or_else(|| log_error!(span, "function '{}' not found", ast.fun))?;
    // get arguments
    let args_ty = match self.program.func(callee).ty().kind() {
      TypeKind::Function(args, _) => args.clone(),
      _ => panic!("invalid function"),
    };
    let args = self.generate_args(func, span, bb_name, &ast.args, &args_ty)?;
    Ok(self.dfg_mut(func).new_value().call(callee, args))
  }

  /// Generates returns.
  fn generate_return(
    &mut self,
    func: Function,
    span: &Span,
    bb_name: &str,
    ret_ty: &Type,
    ast: &ast::Return,
  ) -> ValueResult {
    // check return type
    if !ret_ty.is_unit() && ast.value.is_none() {
      return_error!(
        span,
        "expected return type '{}', but returned nothing",
        ret_ty
      );
    }
    if ret_ty.is_unit() && ast.value.is_some() {
      return_error!(
        span,
        "function has no return value, but a value has been returned"
      );
    }
    // generate return value
    let value = ast
      .value
      .as_ref()
      .map(|v| self.generate_value(func, bb_name, ret_ty, v))
      .transpose()?;
    Ok(self.dfg_mut(func).new_value().ret(value))
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

/// Helper trait, for getting plural form of a given word.
trait ToPlural {
  fn to_plural(self, num: usize) -> String;
}

impl ToPlural for &str {
  fn to_plural(self, num: usize) -> String {
    if num > 1 {
      format!("{}s", self)
    } else {
      self.into()
    }
  }
}
