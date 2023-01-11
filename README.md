# Koopa

[<img alt="github" src="https://img.shields.io/badge/github-pku--minic/koopa-8da0cb?style=for-the-badge&labelColor=555555&logo=github" height="20">](https://github.com/pku-minic/koopa)
[<img alt="crates.io" src="https://img.shields.io/crates/v/koopa.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/koopa)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-koopa-66c2a5?style=for-the-badge&labelColor=555555&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/koopa)
[<img alt="build status" src="https://img.shields.io/github/actions/workflow/status/pku-minic/koopa/build-test.yml?branch=master&style=for-the-badge" height="20">](https://github.com/pku-minic/koopa/actions?query=branch%3Amaster)

Library for generating/parsing/optimizing Koopa IR.

Koopa IR is the next generation of education-oriented intermediate representation designed for compiler courses at Peking University.

## Usage

```
cargo add koopa
```

## Koopa IR

Here is a "Hello, world!" program in Koopa IR:

```koopa
// `putchar` function in libc.
decl @putchar(i32): i32

// A helper function for printing strings (integer arrays).
fun @putstr(@arr: *i32) {
%entry:
  jump %loop_entry(@arr)

%loop_entry(%ptr: *i32):
  %cur = load %ptr
  br %cur, %loop_body, %end

%loop_body:
  call @putchar(%cur)
  %next = getptr %ptr, 1
  jump %loop_entry(%next)

%end:
  ret
}

// String "Hello, world!\n\0".
global @str = alloc [i32, 15], {
  72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 33, 10, 0
}

// `main` function, the entry point of the program.
fun @main(): i32 {
%entry:
  %str = getelemptr @str, 0
  call @putstr(%str)
  ret 0
}
```

Koopa IR is a strongly-typed, SSA form based intermediate representation. It's simple but powerful enough to support compilation of code into machine instructions, or some advanced optimizations of it.

For more details, see [the document of Koopa IR](https://pku-minic.github.io/online-doc/#/misc-app-ref/koopa) (Chinese).

## Examples

See the [`examples` directory](examples), which contains three examples:

* [`opt`](examples/opt): a simple Koopa IR optimizer.
* [`brainfuck`](examples/brainfuck): a brainfuck to Koopa IR compiler.
* [`interpreter`](examples/interpreter): a simple Koopa IR interpreter.

And there are some more complex examples:

* [`kira-rs`](https://github.com/pku-minic/kira-rs): The Kira compiler (Rust version), which compiles SysY language into Koopa IR and RISC-V assembly.
* [`kira-cpp`](https://github.com/pku-minic/kira-cpp): The Kira compiler (C++ version).

## References

Koopa IR library is heavily influenced by [LLVM](https://llvm.org/) and [Cranelift](https://wasmtime.dev/).

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

Copyright (C) 2010-2023 MaxXing. License GPLv3.
