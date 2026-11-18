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

#[test]
fn rejects_nonpositive_array_lengths() {
  for ty in ["[i32, 0]", "[i32, -1]", "[[i32, 0], 2]", "*[i32, -1]"] {
    for source in [
      format!("global @g = alloc {ty}, zeroinit"),
      format!("fun @f() {{ %entry: %p = alloc {ty} ret }}"),
      format!("decl @f({ty})"),
    ] {
      assert!(Driver::from(source).generate_program().is_err());
    }
  }
}

#[test]
fn rejects_arrays_whose_byte_size_overflows() {
  let len = usize::MAX / 4 + 1;
  for ty in [format!("[i32, {len}]"), format!("*[[i32, 2], {}]", len / 2)] {
    let source = format!("decl @f({ty})");
    assert!(Driver::from(source).generate_program().is_err());
  }
  let source = format!("decl @f([i32, {}])", len - 1);
  assert!(Driver::from(source).generate_program().is_ok());
}

#[test]
fn rejects_values_that_do_not_dominate_their_uses() {
  for branch in ["br @cond, %define, %skip", "br @cond, %skip, %define"] {
    let source = format!(
      "fun @f(@cond: i32): i32 {{
        %entry: {branch}
        %define: %value = add 1, 2 jump %merge
        %skip: jump %merge
        %merge: ret %value
      }}"
    );
    assert!(Driver::from(source).generate_program().is_err());
  }
}

#[test]
fn accepts_dominating_values_across_diamonds_and_loops() {
  let source = "fun @f(@cond: i32): i32 {
    %entry: %value = add 1, 2 br @cond, %left, %right
    %left: jump %loop
    %right: jump %loop
    %loop: br @cond, %body, %exit
    %body: jump %loop
    %exit: ret %value
  }";
  assert!(Driver::from(source).generate_program().is_ok());
}
