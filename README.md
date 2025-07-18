# Theories of Abstract Interpretation on Regular Expressions

[![Build][build-badge]][build-link]

[build-badge]: https://github.com/flatypes/flat-theory/actions/workflows/build.yml/badge.svg?branch=main
[build-link]: https://github.com/flatypes/flat-theory/actions/workflows/build.yml

This repository contains the [Rocq](https://rocq-prover.org) mechanization of the FLAT-Checker paper.
It contains the definition of charsets, strings and their operations, regular expressions (regexes) and their operations,
and soundness theorem for the type inference and narrowing rules.

## Build

### Via Nix

```sh
nix build
```

This will download all dependencies and compile the Rocq code. If no error messages show, then all theorems are machine-checked.

### Documentation

To generate documentation, type `nix develop` to enter the development shell and then run `make doc`.
The HTML files will be written to the `doc/` folder under the project root.
