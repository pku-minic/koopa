# libkoopa

C library of the Koopa IR framework.

## Building

`libkoopa` must be built with `panic = abort` to prevent unwinding across the FFI boundary.

Because we cannot specify `[profile]` configuration for a specific package in the Cargo workspace ([Rust issue #8264](https://github.com/rust-lang/cargo/issues/8264)), you **MUST** manually set the `CARGO_PROFILE_*_PANIC` environment variable when building `libkoopa`:

```sh
CARGO_PROFILE_RELEASE_PANIC=abort cargo build --package libkoopa --release
```
