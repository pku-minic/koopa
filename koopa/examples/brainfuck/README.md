# brainfuck

A brainfuck to Koopa IR compiler.

## Usage

Run in the repository root:

```sh
echo "++++++++[->++++++++<]>++++++++.<+++++[->+++++<]>++++.+++++++" \
     "..+++.<++++++++[->--------<]>---------------.<++++++[->+++++" \
     "+<]>+++++++.<++++++[->++++++<]>..+.<+++[->---<]>------.<++++" \
     "++++[->--------<]>.<" | cargo run --example brainfuck -- -o output.koopa
```

You will see the generated Koopa IR in file `output.koopa`.

Or you can convert the generated Koopa IR to LLVM IR:

```sh
echo "++++++++[->++++++++<]>++++++++.<+++++[->+++++<]>++++.+++++++" \
     "..+++.<++++++++[->--------<]>---------------.<++++++[->+++++" \
     "+<]>+++++++.<++++++[->++++++<]>..+.<+++[->---<]>------.<++++" \
     "++++[->--------<]>.<" | cargo run --example brainfuck -- -ll | opt -O3 -S | lli
```

You will see:

```
    Finished dev [unoptimized + debuginfo] target(s) in 0.11s
     Running `target/debug/brainfuck -ll`
Hello Koopa!
```

Alternatively, you can read the input brainfuck program from file:

```sh
cargo run --example brainfuck -- -i examples/brainfuck/pi.bf -ll | opt -O3 -S | lli
```
