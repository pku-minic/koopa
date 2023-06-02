//! Koopa IR generator ([`Generator`]), name manager ([`NameManager`]) and
//! Koopa IR visitor trait ([`Visitor`]) related implementations.
//!
//! The Koopa IR generator converts in-memory Koopa IR programs into
//! other forms by using IR visitors. IR visitors can use name manager
//! to generate function/basic block/value names when visiting IR programs.

use crate::ir::entities::{BasicBlockData, FunctionData, Program, ValueData};
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{Result, Write};
use std::num::NonZeroUsize;
use std::path::Path;
use std::rc::Rc;

/// A manager for storing names and allocating unique temporary
/// names of global values, functions, basic blocks and local values.
#[derive(Default)]
pub struct NameManager {
  next_id: usize,
  cur_scope: ScopeKind,
  prefix: Prefix,
  global_names: HashSet<StringRc>,
  bb_names: HashSet<StringRc>,
  global_vars: HashMap<*const ValueData, Rc<String>>,
  funcs: HashMap<*const FunctionData, Rc<String>>,
  bbs: HashMap<*const BasicBlockData, Rc<String>>,
  values: HashMap<*const ValueData, Rc<String>>,
}

impl NameManager {
  /// Creates a new name manager.
  pub fn new() -> Self {
    Self::default()
  }

  /// Enters the function scope.
  /// Call this method when generating basic blocks and local values.
  ///
  /// # Panics
  ///
  /// Panics when the current scope is already function scope.
  pub fn enter_func_scope(&mut self) {
    assert!(
      matches!(self.cur_scope, ScopeKind::Global),
      "already in function scope"
    );
    self.cur_scope = ScopeKind::Function;
    self.values.clear();
  }

  /// Exits the function scope.
  /// Call this method when quitting from function generation.
  ///
  /// # Panics
  ///
  /// Panics when the current scope is not function scope.
  pub fn exit_func_scope(&mut self) {
    assert!(
      matches!(self.cur_scope, ScopeKind::Function),
      "not in function scope"
    );
    self.cur_scope = ScopeKind::Global;
    self.bb_names.clear();
    self.bbs.clear();
    for name in self.values.values() {
      self.global_names.remove(name);
    }
  }

  /// Sets the prefix of generated names.
  pub fn set_prefix(&mut self, prefix: Prefix) {
    self.prefix = prefix;
  }

  /// Returns the name of the given function.
  pub fn func_name(&mut self, func: &FunctionData) -> Rc<String> {
    let ptr: *const FunctionData = func;
    if let Some(name) = self.funcs.get(&ptr) {
      name.clone()
    } else {
      let name = self.next_name_str(func.name(), |s| &mut s.global_names);
      self.funcs.insert(ptr, name);
      self.funcs[&ptr].clone()
    }
  }

  /// Returns the name of the given basic block.
  pub fn bb_name(&mut self, bb: &BasicBlockData) -> Rc<String> {
    let ptr: *const BasicBlockData = bb;
    if let Some(name) = self.bbs.get(&ptr) {
      name.clone()
    } else {
      let name = self.next_name(bb.name(), |s| &mut s.bb_names);
      self.bbs.insert(ptr, name);
      self.bbs[&ptr].clone()
    }
  }

  /// Returns the name of the given value.
  ///
  /// # Panics
  ///
  /// Panics if the given value is a constant.
  pub fn value_name(&mut self, value: &ValueData) -> Rc<String> {
    assert!(!value.kind().is_const(), "can not name constants");
    if value.kind().is_global_alloc() {
      self.value_name_impl(value, |s| &mut s.global_vars)
    } else {
      self.value_name_impl(value, |s| &mut s.values)
    }
  }

  fn value_name_impl<F>(&mut self, value: &ValueData, value_set: F) -> Rc<String>
  where
    F: for<'a> Fn(&'a mut Self) -> &'a mut HashMap<*const ValueData, Rc<String>>,
  {
    let ptr: *const ValueData = value;
    if let Some(name) = value_set(self).get(&ptr) {
      name.clone()
    } else {
      let name = self.next_name(value.name(), |s| &mut s.global_names);
      let values = value_set(self);
      values.insert(ptr, name);
      values[&ptr].clone()
    }
  }

  /// Returns a temporary value name.
  pub fn temp_value_name(&mut self) -> Rc<String> {
    self.next_name(&None, |s| &mut s.global_names)
  }

  /// Generates the next name by the given `Option<String>`
  /// and stores it to the given name set.
  fn next_name<F>(&mut self, name: &Option<String>, name_set: F) -> Rc<String>
  where
    F: for<'a> FnOnce(&'a mut Self) -> &'a mut HashSet<StringRc>,
  {
    // check if there is a name
    if let Some(name) = name {
      self.next_name_str(name, name_set)
    } else {
      // generate a temporary name
      let name = self.prefix.temp_name(self.next_id);
      self.next_id += 1;
      let names = name_set(self);
      names.insert(name.clone().into());
      names.get(&name).unwrap().to_rc()
    }
  }

  /// Generates the next name by the given string
  /// and stores it to the given name set.
  fn next_name_str<F>(&mut self, name: &str, name_set: F) -> Rc<String>
  where
    F: for<'a> FnOnce(&'a mut Self) -> &'a mut HashSet<StringRc>,
  {
    let name = self.prefix.name(name);
    let names = name_set(self);
    // check for duplicate names
    if !names.contains(&name) {
      names.insert(name.clone().into());
      names.get(&name).unwrap().to_rc()
    } else {
      // generate a new name
      for id in 0.. {
        let new_name = format!("{}_{}", name, id);
        if !names.contains(&new_name) {
          names.insert(new_name.clone().into());
          return names.get(&new_name).unwrap().to_rc();
        }
      }
      unreachable!()
    }
  }
}

/// Kind of scope.
#[derive(Clone, Copy, Default)]
enum ScopeKind {
  #[default]
  Global,
  Function,
}

/// Prefix of name.
#[derive(Default)]
pub enum Prefix {
  /// Default prefix,
  /// named variables start with '@' and
  /// temporary variables start with '%'.
  #[default]
  Default,
  /// Custom prefix,
  /// named variables start with `named` and
  /// temporary variables start with `temp`.
  Custom {
    /// Named variable prefix.
    named: String,
    /// Temporary variable prefix.
    temp: String,
    /// Maximum length of named variable.
    /// Truncates the variable name if its length is too long.
    /// `None` if no limit.
    max_len: Option<NonZeroUsize>,
  },
}

impl Prefix {
  /// Returns the name according to the prefix setting.
  fn name(&self, name: &str) -> String {
    match self {
      Prefix::Default => name.into(),
      Prefix::Custom {
        named,
        temp,
        max_len,
      } => {
        let mut name = if let Some(name) = name.strip_prefix('@') {
          format!("{}{}", named, name)
        } else {
          format!("{}{}", temp, &name[1..])
        };
        if let Some(max_len) = max_len {
          name.truncate(max_len.get());
        }
        name
      }
    }
  }

  /// Returns a temp name by the given id.
  fn temp_name(&self, id: usize) -> String {
    match self {
      Prefix::Default => format!("%{}", id),
      Prefix::Custom { temp, .. } => format!("{}{}", temp, id),
    }
  }
}

/// `Rc<String>` that implements `Borrow<str>`.
#[derive(Clone, PartialEq, Eq, Hash)]
struct StringRc(Rc<String>);

impl StringRc {
  fn to_rc(&self) -> Rc<String> {
    self.0.clone()
  }
}

impl From<String> for StringRc {
  fn from(s: String) -> Self {
    Self(Rc::new(s))
  }
}

impl From<&str> for StringRc {
  fn from(s: &str) -> Self {
    Self(Rc::new(s.into()))
  }
}

impl Borrow<Rc<String>> for StringRc {
  fn borrow(&self) -> &Rc<String> {
    &self.0
  }
}

impl Borrow<String> for StringRc {
  fn borrow(&self) -> &String {
    self.0.as_ref()
  }
}

impl Borrow<str> for StringRc {
  fn borrow(&self) -> &str {
    self.0.as_ref()
  }
}

/// A generator for traversing and generating Koopa IR into other forms.
pub struct Generator<W: Write, V: Visitor<W>> {
  writer: W,
  visitor: V,
  name_man: NameManager,
}

impl<W: Write, V: Visitor<W>> Generator<W, V> {
  /// Creates a new generator.
  pub fn new(writer: W) -> Self
  where
    V: Default,
  {
    Self {
      writer,
      visitor: V::default(),
      name_man: NameManager::new(),
    }
  }

  /// Creates a new generator with the given visitor.
  pub fn with_visitor(writer: W, visitor: V) -> Self {
    Self {
      writer,
      visitor,
      name_man: NameManager::new(),
    }
  }

  /// Consumes and returns the writer inside of the current generator.
  pub fn writer(self) -> W {
    self.writer
  }

  /// Generates on the given Koopa IR program.
  pub fn generate_on(&mut self, program: &Program) -> Result<V::Output> {
    self
      .visitor
      .visit(&mut self.writer, &mut self.name_man, program)
  }
}

impl<V: Visitor<File>> Generator<File, V> {
  /// Creates a new generator from the given path.
  pub fn from_path<P>(path: P) -> Result<Self>
  where
    V: Default,
    P: AsRef<Path>,
  {
    File::create(path).map(Generator::new)
  }
}

/// A visitor trait for all Koopa IR visitors.
pub trait Visitor<W: Write> {
  /// The output type of all visitor methods.
  type Output;

  /// Visits the given Koopa IR program.
  fn visit(&mut self, w: &mut W, nm: &mut NameManager, program: &Program) -> Result<Self::Output>;
}
