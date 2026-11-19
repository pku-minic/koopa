# Changelog

All notable changes to the Koopa will be documented in this file.

## 0.0.11 - 2026-11-19

### Added

* Added `Type::checked_size` and `Type::checked_size_with_ptr_size` to compute byte sizes for the configured target or an explicit pointer width. Both return `None` on overflow. `Type::size` now panics on overflow in all build profiles.

### Changed

* The frontend resolves definitions in the current and entry blocks directly, avoiding repeated predecessor walks for function arguments and other entry-block values.
* The `interpreter` example calls external functions through `libffi` using the declared C signature. Building the bundled `libffi` requires a C compiler, Make, Autoconf and Automake.
* Updated `key-node-list` to 0.0.7.
* CI now tests `libkoopa` on Windows and runs the `interpreter` and `opt` example tests on Linux, including their Miri suites.
* Removed the Cargo cache from CI and kept the nightly toolchain cache on Linux.

### Fixed

* The frontend reports missing or extra arguments on calls, jumps and branches, and reports undefined branch targets. It distinguishes unknown symbols from definitions that do not dominate a use.
* The frontend rejects nonpositive array lengths, lengths and byte sizes that overflow `usize`, and aggregate initializers that do not match the declared type or array length.
* Removing and reinserting a basic block preserves its instructions and their order. Moving or clearing blocks keeps `Layout::parent_bb` accurate, and the layout rejects duplicate instruction ownership.
* LLVM output uses distinct names for block labels, local values and generated temporaries. Calls to functions defined later, including mutually recursive functions, use the correct global names.
* Reusing a `libkoopa` raw program builder produces independent snapshots. Each snapshot and its `used_by` links remain valid until the builder is deleted, even after the source program is changed or deleted.
* The `libkoopa` raw-file parse and dump functions leave caller-owned descriptors and handles open and return `KOOPA_EC_INVALID_FILE` when duplication fails.
* The `interpreter` example assigns block arguments in parallel and executes jumps and branches iteratively, so loops can swap parameters and run without growing the host call stack.
* Interpreter allocations use checked sizes and contiguous native storage, so external functions can read and update nested arrays through aliases. Zero-offset `getptr` works on allocations, and interpreter-managed pointers retain their bounds across stores and loads.
* The interpreter and the constant-folding pass use wrapping `i32` addition, subtraction and multiplication. They propagate `undef` and produce it for invalid division, remainder and shift operations.
* In the `opt` example, dead-code elimination handles global operands and keeps block parameter indices and incoming arguments in sync. Constant folding handles block parameters with global inputs or no incoming edges.

## 0.0.10 - 2026-03-19

### Added

* `DataFlowGraph::update_value` for updating value data.

### Changed

* [PR #21](https://github.com/pku-minic/koopa/pull/21): chore: optimize panic msg.

### Fixed

* [PR #15](https://github.com/pku-minic/koopa/pull/15): Fix example links in documentation.
* [PR #18](https://github.com/pku-minic/koopa/pull/18): fix(Miri): get CString pointer after HashMap insert.
* [Issue #16](https://github.com/pku-minic/koopa/issues/16): Confusing panic when using FunctionData without adding to Program first.
* [PR #24](https://github.com/pku-minic/koopa/pull/24): fix(example): resolve panic in DCE when handling interdependent dead code.
* [PR #25](https://github.com/pku-minic/koopa/pull/25): chore: fix typos suggested by typos-cli.

## 0.0.9 - 2025-11-11

### Changed

* Used `phf::Map` instead of `HashMap` in lexer to reduce usage of TLS.
* Replaced all `Cell`ed-integers with atomic integers.
* Bumped to Rust 2024 edition.
* Updated dependencies.

## 0.0.8 - 2024-11-30

### Changed

* Minor changes for making Clippy happy.

### Fixed

* [Issue #4](https://github.com/pku-minic/koopa/issues/4): `replace_value_with` malfunctions in version 0.0.7.
* [Issue #5](https://github.com/pku-minic/koopa/issues/5): branch with a single target and different arguments.
* [PR #6](https://github.com/pku-minic/koopa/pull/6): update typedef of enums.

## 0.0.7 - 2023-06-02

### Fixed

* Some typos in the documentation.
* [Issue #3](https://github.com/pku-minic/koopa/issues/3): A naming issue in Koopa to LLVM IR generator.

## 0.0.6 - 2023-01-12

### Changed

* Added all subprojects in the `examples` directory as Cargo examples.

### Fixed

* Fault about generating allocations from raw programs in `libkoopa`.
* Some deprecated and non-recommended uses in the source code.

## 0.0.5 - 2022-03-09

### Fixed

* Fault about duplicate parameter names.
* Fault about local symbol redefinition.

## 0.0.4 - 2022-02-21

### Added

* Library crate `libkoopa` for C/C++ programs that require the Koopa IR framework.

### Changed

* Supported setting maximum variable name length in `NameManager`.

### Fixed

* Fault about creating/initializing `Parser` when error occurs in `Lexer`.

## 0.0.3 - 2022-01-05

### Changed

Brand new design with a lot of changes!

* Replaced `phi` function with basic block parameters.
* Using `DataFlowGraph` and `Layout` to manage values and basic blocks.
* `opt`, `front`, `back` modules and all examples were updated.

## 0.0.2 - 2021-12-24

### Added

* More re-imports.
* Example `opt`, `brainfuck` and `interpreter`.
* Method `Value::uses` and iterator of `Use`.
* Method `Type::size`.
* Method `Generator::new_with_visitor` for visitors that has internal state.
* `ValueCursorMut` for instruction list in basic blocks.

### Changed

* Replaced all `debug_assert`s with `assert`s.
* Removed all unary operations.
* Signature of method `Driver::from_path` and `Generator::from_path`.
* Signature of method `Value::replace_all_uses_with`.

### Fixed

* Fault about generating branch instructions into LLVM IR.
* Fault about creating file in `Generator::from_path`.
* Fault about generating Koopa IR and LLVM IR.
* Infinite loop problem in `Builder::generate_local_symbol`.
* Fault about updating `BasicBlockInner::preds`.

## 0.0.1 - 2021-09-14
