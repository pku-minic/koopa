# interpreter

A simple Koopa IR interpreter (just for example).

External functions use the host C ABI through `libffi`. The default build compiles a bundled copy of libffi and needs a C compiler, make, autoconf and automake. Function declarations must match the loaded library; supported arguments and return values are `i32` and pointers, with `void` also supported as a return type. The interpreter requires the host pointer size.

Allocations use native, contiguous memory, including nested arrays and pointer elements. External writes and returned aliases refer to the same memory used by IR loads and stores. Local allocations live until their function returns; global allocations live until interpretation finishes. Native calls are unsafe and must respect these lifetimes and allocation bounds.

## Usage

Run in the repository root:

```sh
cargo run --example interpreter -- koopa/examples/interpreter/ir/42.koopa; echo $?
```

You will see:

```
    Finished dev [unoptimized + debuginfo] target(s) in 0.02s
     Running `target/debug/examples/interpreter koopa/examples/interpreter/ir/42.koopa`
42
```

Or you can run Koopa IR programs with `libc` loaded:

```sh
# for macOS
cargo run --example interpreter -- \
    koopa/examples/interpreter/ir/hello.koopa -l /usr/lib/system/libsystem_c.dylib
```

You will see:

```
    Finished dev [unoptimized + debuginfo] target(s) in 0.03s
     Running `target/debug/examples/interpreter koopa/examples/interpreter/ir/hello.koopa -l /usr/lib/system/libsystem_c.dylib`
Hello, world!
```
