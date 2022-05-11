mod builder;
mod entities;
mod ffi;
mod generator;

pub use builder::*;
pub use entities::*;
pub use ffi::*;

use generator::*;

#[cfg(test)]
mod test {
  use super::*;
  use koopa::back::KoopaGenerator;
  use koopa::front::Driver;
  use koopa::ir::Program;

  const LOOP_PROGRAM: &str = r#"global @str = alloc [i32, 15], {72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 33, 10, 0}

decl @putchar(i32): i32

fun @putstr(@arr: *i32) {
%entry:
  jump %loop_entry(@arr)

%loop_entry(%ptr: *i32):
  %cur = load %ptr
  br %cur, %loop_body, %end

%loop_body:
  %0 = call @putchar(%cur)
  %next = getptr %ptr, 1
  jump %loop_entry(%next)

%end:
  ret
}

fun @main(): i32 {
%entry:
  %str = getelemptr @str, 0
  call @putstr(%str)
  ret 0
}
"#;

  const RECURSIVE_PROGRAM: &str = r#"fun @fib(@n: i32): i32 {
%entry:
  %cond = le @n, 2
  br %cond, %then, %else

%then:
  ret 1

%else:
  %0 = sub @n, 1
  %x = call @fib(%0)
  %1 = sub @n, 2
  %y = call @fib(%1)
  %ans = add %x, %y
  ret %ans
}
"#;

  const ALLOC_PROGRAM: &str = r#"fun @main(): i32 {
%entry:
  %0 = alloc [i32, 10]
  store {0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, %0
  %1 = getelemptr %0, 0
  %2 = load %1
  ret %2
}
"#;

  fn build_raw<'rpb>(builder: &'rpb mut RawProgramBuilder, program: &str) -> RawProgram<'rpb> {
    let program = Driver::from(program).generate_program().unwrap();
    builder.build_on(&program)
  }

  fn build_and_generate(program: &str) -> Program {
    let mut builder = RawProgramBuilder::new();
    let raw = build_raw(&mut builder, program);
    match generate_program(&raw) {
      Ok(p) => p,
      Err(e) => panic!("error code: {}", e as i32),
    }
  }

  fn assert_name(name: *const std::os::raw::c_char, s: Option<&str>) {
    use std::ffi::CStr;
    let name = (!name.is_null()).then(|| unsafe { CStr::from_ptr(name).to_str().unwrap() });
    assert_eq!(name, s);
  }

  #[test]
  fn test_raw_builder_loop() {
    let mut builder = RawProgramBuilder::new();
    let raw = build_raw(&mut builder, LOOP_PROGRAM);
    assert_eq!(raw.values.len, 1);
    assert!(matches!(raw.values.kind, RawSliceItemKind::Value));
    assert_eq!(raw.funcs.len, 3);
    let global_alloc = unsafe { &**(raw.values.buffer as *const RawValue) };
    assert_name(global_alloc.name, Some("@str"));
    assert!(matches!(global_alloc.kind, RawValueKind::GlobalAlloc(_)));
  }

  #[test]
  fn test_raw_builder_recursive() {
    let mut builder = RawProgramBuilder::new();
    let raw = build_raw(&mut builder, RECURSIVE_PROGRAM);
    assert_eq!(raw.values.len, 0);
    assert_eq!(raw.funcs.len, 1);
    assert!(matches!(raw.funcs.kind, RawSliceItemKind::Function));
    let func = unsafe { &**(raw.funcs.buffer as *const RawFunction) };
    assert_name(func.name, Some("@fib"));
    assert_eq!(func.params.len, 1);
    assert_eq!(func.bbs.len, 3);
  }

  #[test]
  fn test_raw_builder_alloc() {
    let mut builder = RawProgramBuilder::new();
    let raw = build_raw(&mut builder, ALLOC_PROGRAM);
    assert_eq!(raw.values.len, 0);
    assert_eq!(raw.funcs.len, 1);
    assert!(matches!(raw.funcs.kind, RawSliceItemKind::Function));
    let func = unsafe { &**(raw.funcs.buffer as *const RawFunction) };
    assert_name(func.name, Some("@main"));
    assert_eq!(func.params.len, 0);
    assert_eq!(func.bbs.len, 1);
  }

  #[test]
  fn test_raw_generator_loop() {
    let program = build_and_generate(LOOP_PROGRAM);
    let mut gen = KoopaGenerator::new(Vec::new());
    gen.generate_on(&program).unwrap();
    assert_eq!(std::str::from_utf8(&gen.writer()).unwrap(), LOOP_PROGRAM);
  }

  #[test]
  fn test_raw_generator_recursive() {
    let program = build_and_generate(RECURSIVE_PROGRAM);
    let mut gen = KoopaGenerator::new(Vec::new());
    gen.generate_on(&program).unwrap();
    assert_eq!(
      std::str::from_utf8(&gen.writer()).unwrap(),
      RECURSIVE_PROGRAM
    );
  }

  #[test]
  fn test_raw_generator_alloc() {
    let program = build_and_generate(ALLOC_PROGRAM);
    let mut gen = KoopaGenerator::new(Vec::new());
    gen.generate_on(&program).unwrap();
    assert_eq!(
      std::str::from_utf8(&gen.writer()).unwrap(),
      ALLOC_PROGRAM
    );
  }
}
