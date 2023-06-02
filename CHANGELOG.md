# Changelog

All notable changes to the Koopa will be documented in this file.

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

* Fault about creating/initializing `Parser` when error occurrs in `Lexer`.

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
