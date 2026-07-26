# Standard Library Catalogue

This catalogue lists every module shipped in the standard library, what each
module provides, and whether a fuller reference page exists.

`std` is the root aggregator. The `std::core`, `std::control`, `std::data`,
`std::io`, and `std::text` aggregators declare their child modules;
`std::io` also re-exports its children's public names. `std::num` combines
numeric roles with its `frac` child module.

Entry files import `std::prelude::*` unless the prelude is disabled. The
prelude re-exports the operators, roles, types, constructors, effects, and I/O
helpers used without a module qualifier in ordinary programs. A linked module
name leads to the page that documents it. **Not documented** means that no
fuller page covers the module yet. **Provisional** means the module is not part
of the stable surface: its spelling is expected to change, and a program should
not depend on it.

## Imports and aggregators

| Module | Purpose | Documentation |
| --- | --- | --- |
| `std` | Declares the twelve top-level standard-library modules. | **Not documented** |
| `std::control` | Groups control-flow effects, nondeterminism, errors, and mutable references. | **Not documented** |
| [`std::core`](./core) | Groups the core roles and operators and defines `id` and `compose`. | Reference |
| `std::data` | Groups the collection roles and the list, optional, range, and result types. | **Not documented** |
| `std::io` | Groups and re-exports the console, file, and network I/O surfaces. | **Not documented** |
| `std::text` | Groups byte, character, string, path, parsing, config, and Yumark support. | **Not documented** |
| [`std::prelude`](../modules#standard-library-modules) | Re-exports the standard names that entry files receive without an explicit import. | Reference |

## Control modules

| Module | Purpose | Documentation |
| --- | --- | --- |
| [`std::control::flow`](../control-flow) | Implements early return, loops, and labeled loop control with effects. | Reference |
| [`std::control::junction`](./nondet#junctions) | Extends comparisons over `Fold` values with the effectful `all` and `any` junctions. | Reference |
| [`std::control::nondet`](./nondet) | Provides binary choice, rejection, search helpers, and result collectors for nondeterministic computations. | Reference |
| [`std::control::throw`](../errors) | Defines the `Throw` role that associates an error value with the effect raised by `.throw` and `fail`. | Reference |
| [`std::control::var`](../../guide/cookbook) | Implements effect-backed references and the `get` and `set` operations behind local mutable bindings. | Reference |

## Core modules

| Module | Purpose | Documentation |
| --- | --- | --- |
| [`std::core::cmp`](./core#std-core-cmp) | Defines the `Eq` and `Ord` roles and their standard implementations. | Reference |
| [`std::core::convert`](./core#std-core-convert) | Defines the `Cast` role and the standard path and numeric conversion rules. | Reference |
| [`std::core::fmt`](./core#std-core-fmt) | Defines display and debug formatting roles, format specifications, and standard implementations. | Reference |
| [`std::core::ops`](../operators) | Declares the standard control, range, arithmetic, comparison, and Boolean operators. | Reference |
| [`std::core::seq`](./core#std-core-seq) | Defines the `Len` and `IsEmpty` roles and implementations for standard sequence types. | Reference |

## Data modules

| Module | Purpose | Documentation |
| --- | --- | --- |
| [`std::data::fold`](./list#iteration) | Defines `Fold` with folding, search, containment, and nondeterministic element selection. | Reference |
| [`std::data::index`](./list#indexing-and-slicing) | Defines the `Index` role that maps a container and key type to an indexed value type. | Reference |
| [`std::data::list`](./list) | Provides persistent lists, transformations, slicing, sorting, and mutable-reference views. | Reference |
| [`std::data::opt`](./opt) | Defines the `nil` or `just` optional-value type. | Reference |
| [`std::data::range`](./core#std-data-range) | Represents bounded or unbounded integer ranges and folds over their values. | Reference |
| [`std::data::result`](./result) | Defines value-level success or failure with mapping, chaining, and fallback operations. | Reference |

## Text modules

| Module | Purpose | Documentation |
| --- | --- | --- |
| `std::text::bytes` | Provides byte length, comparison, concatenation, indexing, slicing, and lossy UTF-8 decoding. | **Not documented** |
| `std::text::char` | Provides character comparison, string conversion, and whitespace, punctuation, and word classification. | **Not documented** |
| `std::text::config` | Parses an unstable, small sectioned key/value config format and reads values or source files from it. | **Not documented** |
| `std::text::parse` | Provides an effect-based parser-combinator API for reading, finding, editing, and replacing string matches. | **Not documented** |
| `std::text::path` | Converts paths to and from bytes and displays paths with lossy UTF-8 decoding. | **Not documented** |
| [`std::text::str`](./str) | Provides character-indexed strings, slices, searches, transformations, and mutable line views. | Reference |
| `std::text::yumark` | Defines the Yumark document algebra and renders documents as HTML nodes or Markdown. | **Not documented** |

## I/O modules

| Module | Purpose | Documentation |
| --- | --- | --- |
| [`std::io::console`](./core#std-io-console) | Provides stdout and stderr output plus warning and terminating effects. | Reference |
| [`std::io::file`](./fs) | Provides text-file reads, writes, metadata, scoped edits, and host-backed mutable buffers. | Reference |
| `std::io::net` | Provides host-backed listeners, server request acceptance, and byte responses. | **Provisional** |

## Numeric and scalar modules

| Module | Purpose | Documentation |
| --- | --- | --- |
| `std::bool` | Provides Boolean equality, negation, and string conversion. | **Not documented** |
| `std::float` | Provides floating-point comparison, arithmetic, and string conversion primitives. | **Not documented** |
| `std::int` | Provides integer comparison, arithmetic, division, remainder, and decimal and hexadecimal conversion primitives. | **Not documented** |
| `std::num` | Defines arithmetic and hexadecimal-formatting roles and their standard implementations, and declares the `frac` module. | **Not documented** |
| `std::num::frac` | Provides normalized rational numbers with arithmetic, comparison, and float and string conversion. | **Not documented** |

## Utility modules

| Module | Purpose | Documentation |
| --- | --- | --- |
| `std::testing` | Defines lazy assertion operators and the assertion effect. | **Not documented** |
| `std::time` | Defines instants, durations, clock access, unit constructors, arithmetic, comparison, and formatting. | **Not documented** |
