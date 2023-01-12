# opt

A simple Koopa IR optimizer that uses `koopa::front::Driver` to parse Koopa IR, performs constant folding and dead code elimination, and then uses `koopa::back::KoopaGenerator` to generate the optimized Koopa IR.

## Usage

Run in the repository root:

```sh
cargo run --example opt -- examples/opt/ir/local_opt.koopa path/to/output.koopa
```

You will see the output IR has been constant folded and all dead code has been eliminated.
