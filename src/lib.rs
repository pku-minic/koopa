//! Library for generating/parsing/optimizing Koopa IR.
//!
//! Koopa IR is the next generation of education-oriented intermediate
//! representations designed for compiler courses at Peking University.
//!
//! # Koopa IR
//!
//! Here is a "Hello, world!" program in Koopa IR:
//!
//! ```koopa
//! // `putchar` function in libc.
//! decl @putchar(i32): i32
//!
//! // A helper function for printing strings (integer arrays).
//! fun @putstr(@arr: *i32) {
//! %entry:
//!   jump %loop_entry(@arr)
//!
//! %loop_entry(%ptr: *i32):
//!   %cur = load %ptr
//!   br %cur, %loop_body, %end
//!
//! %loop_body:
//!   call @putchar(%cur)
//!   %next = getptr %ptr, 1
//!   jump %loop_entry(%next)
//!
//! %end:
//!   ret
//! }
//!
//! // String "Hello, world!\n\0".
//! global @str = alloc [i32, 15], {
//!   72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 33, 10, 0
//! }
//!
//! // `main` function, the entry point of the program.
//! fun @main(): i32 {
//! %entry:
//!   %str = getelemptr @str, 0
//!   call @putstr(%str)
//!   ret 0
//! }
//! ```
//!
//! Koopa IR is a strongly-typed, SSA form based intermediate representation.
//! It's simple but powerful enough to support compilation of code into
//! machine instructions, or some advanced optimizations of it.
//!
//! For more details, see
//! [the document of Koopa IR](https://pku-minic.github.io/online-doc/#/misc-app-ref/koopa)
//! (Chinese).
//!
//! # Examples
//!
//! See the [`examples` directory](https://github.com/pku-minic/koopa/tree/master/examples),
//! which contains three examples:
//!
//! * [`opt`](https://github.com/pku-minic/koopa/tree/master/examples/opt):
//!   a simple Koopa IR optimizer.
//! * [`brainfuck`](https://github.com/pku-minic/koopa/tree/master/examples/brainfuck):
//!   a brainfuck to Koopa IR compiler.
//! * [`interpreter`](https://github.com/pku-minic/koopa/tree/master/examples/interpreter):
//!   a simple Koopa IR interpreter.
//!
//! And there are some more complex examples:
//!
//! * [`kira-rs`](https://github.com/pku-minic/kira-rs): The Kira compiler (Rust version),
//!   which compiles SysY language into Koopa IR and RISC-V assembly.
//! * [`kira-cpp`](https://github.com/pku-minic/kira-cpp): The Kira compiler (C++ version).
//!
//! # References
//!
//! Koopa IR library is heavily influenced by [LLVM](https://llvm.org/)
//! and [Cranelift](https://wasmtime.dev/).

pub mod back;
pub mod front;
pub mod ir;
pub mod opt;
