# Examples

Some examples showing how to use the `koopa` crate.

## [`opt`](opt)

A simple Koopa IR optimizer that uses `koopa::front::Driver` to parse Koopa IR, performs constant propagation and dead code elimination, and then uses `koopa::back::KoopaGenerator` to generate the optimized Koopa IR.
