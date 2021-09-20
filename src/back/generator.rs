// TODO: remove this attribute after https://github.com/rust-lang/rust-clippy/pull/7640 is merged.
#![allow(clippy::mutable_key_type)]

use crate::ir::{BasicBlock, Function, Program, Value};
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{Result, Write};
use std::path::Path;
use std::rc::Rc;

/// A manager for storing names and allocating unique temporary
/// names of global variables, functions, basic blocks and values.
#[derive(Default)]
pub struct NameManager {
  next_id: usize,
  cur_scope: ScopeKind,
  prefix: Prefix,
  global_names: HashSet<StringRc>,
  bb_names: HashSet<StringRc>,
  global_vars: HashMap<*const Value, Rc<String>>,
  funcs: HashMap<*const Function, Rc<String>>,
  bbs: HashMap<*const BasicBlock, Rc<String>>,
  values: Option<HashMap<*const Value, Rc<String>>>,
}

impl NameManager {
  /// Creates a new `NameManager`.
  pub fn new() -> Self {
    Self::default()
  }

  /// Enters the function scope.
  ///
  /// Call this method when generating basic blocks and local values.
  pub fn enter_func_scope(&mut self) {
    assert!(
      matches!(self.cur_scope, ScopeKind::Global),
      "already in function scope"
    );
    self.cur_scope = ScopeKind::Function;
    self.values = Some(HashMap::new());
  }

  /// Exits the function scope.
  pub fn exit_func_scope(&mut self) {
    assert!(
      matches!(self.cur_scope, ScopeKind::Function),
      "not in function scope"
    );
    self.cur_scope = ScopeKind::Global;
    self.bb_names.clear();
    self.bbs.clear();
    let values = self.values.take().unwrap();
    for name in values.values() {
      self.global_names.remove(name);
    }
  }

  /// Sets the prefix of generated names.
  pub fn set_prefix(&mut self, prefix: Prefix) {
    self.prefix = prefix;
  }

  /// Gets the name of the specific function.
  pub fn get_func_name(&mut self, func: &Function) -> Rc<String> {
    let ptr: *const Function = func;
    if let Some(name) = self.funcs.get(&ptr) {
      name.clone()
    } else {
      let name = self.next_name_str(func.name(), |s| &mut s.global_names);
      self.funcs.insert(ptr, name);
      self.funcs[&ptr].clone()
    }
  }

  /// Gets the name of the specific basic block.
  pub fn get_bb_name(&mut self, bb: &BasicBlock) -> Rc<String> {
    let ptr: *const BasicBlock = bb;
    if let Some(name) = self.bbs.get(&ptr) {
      name.clone()
    } else {
      let name = self.next_name(bb.name(), |s| &mut s.bb_names);
      self.bbs.insert(ptr, name);
      self.bbs[&ptr].clone()
    }
  }

  /// Gets the name of the specific value.
  pub fn get_value_name(&mut self, value: &Value) -> Rc<String> {
    match self.cur_scope {
      ScopeKind::Global => self.get_value_name_impl(value, |s| &mut s.global_vars),
      _ => self.get_value_name_impl(value, |s| s.values.as_mut().unwrap()),
    }
  }

  fn get_value_name_impl<F>(&mut self, value: &Value, value_set: F) -> Rc<String>
  where
    F: for<'a> Fn(&'a mut Self) -> &'a mut HashMap<*const Value, Rc<String>>,
  {
    let ptr: *const Value = value;
    if let Some(name) = value_set(self).get(&ptr) {
      name.clone()
    } else {
      let name = self.next_name(value.inner().name(), |s| &mut s.global_names);
      let values = value_set(self);
      values.insert(ptr, name);
      values[&ptr].clone()
    }
  }

  /// Gets a temporary value name.
  pub fn get_temp_value_name(&mut self) -> Rc<String> {
    self.next_name(&None, |s| &mut s.global_names)
  }

  /// Generates the next name by the specific `Option<String>`
  /// and stores it to the specific name set.
  fn next_name<F>(&mut self, name: &Option<String>, name_set: F) -> Rc<String>
  where
    F: for<'a> FnOnce(&'a mut Self) -> &'a mut HashSet<StringRc>,
  {
    // check if there is a name
    if let Some(name) = name {
      self.next_name_str(name, name_set)
    } else {
      // generate a temporary name
      let name = self.prefix.get_temp_name(self.next_id);
      self.next_id += 1;
      let names = name_set(self);
      names.insert(name.clone().into());
      names.get(&name).unwrap().to_rc()
    }
  }

  /// Generates the next name by the specific string
  /// and stores it to the specific name set.
  fn next_name_str<F>(&mut self, name: &str, name_set: F) -> Rc<String>
  where
    F: for<'a> FnOnce(&'a mut Self) -> &'a mut HashSet<StringRc>,
  {
    let name = self.prefix.get_name(name);
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
#[derive(Clone, Copy)]
enum ScopeKind {
  Global,
  Function,
}

impl Default for ScopeKind {
  fn default() -> Self {
    Self::Global
  }
}

/// Prefix of name.
pub enum Prefix {
  /// Default prefix,
  /// named variables start with '@' and temporary variables start with '%'.
  Default,
  /// Custom prefix.
  Custom { named: String, temp: String },
}

impl Prefix {
  /// Gets the name according to the prefix setting.
  fn get_name(&self, name: &str) -> String {
    match self {
      Prefix::Default => name.into(),
      Prefix::Custom { named, temp } => {
        if let Some(name) = name.strip_prefix('@') {
          format!("{}{}", named, name)
        } else {
          format!("{}{}", temp, &name[1..])
        }
      }
    }
  }

  /// Gets a temp name by the specific id.
  fn get_temp_name(&self, id: usize) -> String {
    match self {
      Prefix::Default => format!("%{}", id),
      Prefix::Custom { temp, .. } => format!("{}{}", temp, id),
    }
  }
}

impl Default for Prefix {
  fn default() -> Self {
    Prefix::Default
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

/// Koopa IR generator
pub struct Generator<W: Write, V: Visitor<W>> {
  writer: W,
  visitor: V,
  name_man: NameManager,
}

impl<W: Write, V: Visitor<W>> Generator<W, V> {
  /// Creates a new generator
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

  /// Consumes and gets the writer inside of the current generator.
  pub fn writer(self) -> W {
    self.writer
  }

  /// Generates on the specific IR program.
  pub fn generate_on(&mut self, program: &Program) -> Result<V::Output> {
    self
      .visitor
      .visit(&mut self.writer, &mut self.name_man, program)
  }
}

impl<V: Visitor<File>> Generator<File, V> {
  /// Creates a new `Generator` from the specific path.
  pub fn from_path<P>(path: P) -> Result<Self>
  where
    V: Default,
    P: AsRef<Path>,
  {
    File::create(path).map(Generator::new)
  }
}

/// Koopa IR visitor.
pub trait Visitor<W: Write> {
  /// The output type of all visitor methods.
  type Output;

  /// Visits the specific program.
  fn visit(&mut self, w: &mut W, nm: &mut NameManager, program: &Program) -> Result<Self::Output>;
}

/// Gets the value reference of the specific use.
macro_rules! value {
  ($use:expr) => {
    $use.value().unwrap().as_ref()
  };
}
pub(crate) use value;
