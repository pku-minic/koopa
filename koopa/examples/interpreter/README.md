# interpreter

A simple Koopa IR interpreter (just for example).

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
