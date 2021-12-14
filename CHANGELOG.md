# Changelog

All notable changes to the Koopa will be documented in this file.

## Unreleased

# Added

* More re-imports.
* Example `opt`, `brainfuck` and `interpreter`.
* Method `Value::uses` and iterator of `Use`.
* Method `Type::size`.

# Changed

* Replaced all `debug_assert`s with `assert`s.
* Removed all unary operations.
* Signature of method `Driver::from_path` and `Generator::from_path`.
* Signature of method `Value::replace_all_uses_with`.

# Fixed

* Fault about generating branch instructions into LLVM IR.
* Fault about creating file in `Generator::from_path`.
* Fault about generating Koopa IR and LLVM IR.

## 0.0.1 - 2021-09-14
