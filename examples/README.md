# Examples

Some examples showing how to use the `koopa` crate.

## [`opt`](opt)

A simple Koopa IR optimizer that uses `koopa::front::Driver` to parse Koopa IR, performs constant folding and dead code elimination, and then uses `koopa::back::KoopaGenerator` to generate the optimized Koopa IR.

## [`brainfuck`](brainfuck)

A brainfuck to Koopa IR compiler.

## [`interpreter`](interpreter)

A simple Koopa IR interpreter, based on `koopa::back::Generator` and `koopa::back::Visitor`.
