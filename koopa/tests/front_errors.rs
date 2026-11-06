use koopa::front::Driver;

#[test]
fn rejects_mismatched_call_argument_counts() {
  for args in ["", "1, 2"] {
    let source = format!("decl @callee(i32)\nfun @main() {{ %entry: call @callee({args}) ret }}");
    assert!(Driver::from(source).generate_program().is_err());
  }
}

#[test]
fn rejects_mismatched_block_argument_counts() {
  for args in ["", "(1, 2)"] {
    for terminator in [
      format!("jump %target{args}"),
      format!("br 1, %target{args}, %other"),
      format!("br 1, %other, %target{args}"),
    ] {
      let source = format!(
        "fun @main(): i32 {{ %entry: {terminator} \
         %target(%x: i32): ret %x %other: ret 0 }}"
      );
      assert!(Driver::from(source).generate_program().is_err());
    }
  }
}

#[test]
fn accepts_matching_argument_counts() {
  let source = "decl @callee(i32): i32\nfun @main(): i32 {
    %entry: %v = call @callee(42) jump %target(%v)
    %target(%x: i32): ret %x
  }";
  assert!(Driver::from(source).generate_program().is_ok());
}

#[test]
fn rejects_undefined_branch_targets_without_panicking() {
  for terminator in [
    "jump %missing",
    "br 1, %missing, %exit",
    "br 1, %exit, %missing",
  ] {
    let source = format!("fun @main() {{ %entry: {terminator} %exit: ret }}");
    assert!(Driver::from(source).generate_program().is_err());
  }
}

#[test]
fn rejects_aggregate_initializers_with_incompatible_types() {
  for source in [
    "global @g = alloc *i32, {1, 2}",
    "global @g = alloc [*i32, 1], {{1}}",
    "global @g = alloc [[i32, 2], 2], {{1}, {2, 3}}",
    "fun @f() { %entry: %p = alloc *i32 store {1}, %p ret }",
    "fun @f() { %entry: %p = alloc [i32, 2] store {1}, %p ret }",
  ] {
    assert!(Driver::from(source).generate_program().is_err(), "{source}");
  }
}

#[test]
fn accepts_array_and_pointer_initializers_of_the_declared_type() {
  for source in [
    "global @g = alloc *i32, zeroinit",
    "global @g = alloc *i32, undef",
    "global @g = alloc [[i32, 2], 2], {{1, 2}, {3, 4}}",
  ] {
    assert!(Driver::from(source).generate_program().is_ok(), "{source}");
  }
}
