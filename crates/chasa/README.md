# chasa

`chasa` is a small, pragmatic parser-combinator library used by the YuLang project.

It is optimized for:

- Explicit backtracking control (`cut`) and “rollback unless cut”
- Separating *success/failure* from *diagnostics* (via `ErrorSink`)
- “Inline-friendly” combinator boundaries (aiming for near hand-written recursive descent after inlining)

> Status: experimental; APIs may change.

## What this crate looks like (in one sentence)

You build parsers as values, run them on an input, and get `Option<Out>` for success/failure — while diagnostics are collected separately in an `ErrorSink`.

## Quick Start (for people who know nothing)

1. `use chasa::prelude::*;`
2. Use `"<input>".test(parser)` for quick experiments.
3. If you need diagnostics, use `test_with_errors`.

### Minimal example

```rust
use chasa::prelude::*;

assert_eq!("a".test(item('a')), Some('a'));
assert_eq!("b".test(item('a')), None);
```

### Mapping outputs (`map`, `map_mut`, `map_once`)

```rust
use chasa::prelude::*;

let parser = item('a').map(|c| c.to_ascii_uppercase());
assert_eq!("a".test(parser), Some('A'));
```

### Repetition (`many` / `many1`)

```rust
use chasa::prelude::*;

let out: Option<String> = "aaab".test(item('a').many());
assert_eq!(out, Some("aaa".to_string()));

let out = "b".test(item('a').many1());
assert_eq!(out, None);
```

### Separated lists (`sep`, `sep_map`)

`sep_map` is often the most convenient API: you get an iterator and can `count()`/`collect()` etc.

```rust
use chasa::prelude::*;

let comma = to(item(','), ()).skip();
let out: Option<usize> = "a,a,a".test(item('a').sep_map_once(comma, |it| it.count()));
assert_eq!(out, Some(3));
```

## Core concepts

### Parsers are values

Parsers are plain values (structs / closures) implementing one of:

- `ParserOnce`: run by value (consumes `self`)
- `ParserMut`: run with `&mut self` (stateful parsers)
- `Parser`: run with `&self` (reusable parsers)

Most combinators are available as methods on these traits (`then_*`, `map_*`, `many_*`, `sep_*`, ...).

### Success/failure is `Option`

- `Some(out)` = success
- `None` = failure

This keeps the hot path minimal and makes “try a branch, roll it back” cheap.

### Diagnostics go to `ErrorSink`

Errors and expectations are collected into an `ErrorSink` (e.g. `LatestSink`).

```rust
use chasa::prelude::*;

let (out, mut errors) = "b".test_with_errors(label(item('a'), "expected 'a'"));
assert_eq!(out, None);
assert!(errors.take_merged().is_some());
```

Useful tools:

- `label` / `label_with`: add a human-readable expectation
- `LatestSink`: keep the latest merged error information (handy for “best effort” parsing)

## Backtracking and `cut` (important!)

`chasa` is designed around a simple rule:

- **If not cut, the input is rolled back on failure.**
- **If cut, failures become “committed” and callers do not roll back.**

Use `cut` when you want to commit to a branch (e.g. after consuming a keyword) to avoid expensive backtracking and to keep errors local.

Related helpers:

- `cut`: a parser that commits at its position
- `cut_after(p)`: commit after `p` succeeds
- `cut_on_ok(p)`: like `cut_after`, but intended for composing with `then`-style flows

## `sep` and separators

In many grammars, separators (commas, semicolons, etc.) are “structural”: you don’t want their value.

This crate models that by allowing separators to be `SkipParser*` in `sep`/`sep_map*`.
Internally, `sep_map` needs to unify `&mut`/`&` execution, so it uses a small adapter (`RefOrMutSkipParser`).

## “Parsec mindset”: what to watch out for

If you come from Parsec (Haskell) or Parsec-like APIs:

1. **Failure is `None`, diagnostics are out-of-band.**
   - In Parsec you often inspect an `Either/Result` error value.
   - Here you use `ErrorSink` (`test_with_errors`, `label`, etc.).

2. **Think “commit with `cut`” rather than “sprinkle `try`”.**
   - In Parsec, `try` exists because consumption may prevent backtracking.
   - Here, rollback is the default; `cut` is how you stop rollback.

3. **Be careful with zero-width success in loops.**
   - As with most combinator libraries, `many`/`sep` can loop forever if the inner parser succeeds without consuming input.

## Compared to other Rust parser libraries (high-level)

This is not meant to be a strict benchmark; it’s a design summary.

### Compared to `nom`

- `nom` tends to be “byte-slice in / remainder out” with `IResult`.
- `chasa` centers around `In` (checkpoint/rollback + error sink + cut state).
- `cut` exists in both worlds, but `chasa` aims for a consistent “rollback unless cut” story across combinators.

### Compared to `combine` / other classic combinator libraries

- Similar style (combinators as values), but the library is tuned for YuLang’s needs:
  - Separate error sink
  - Strong focus on explicit commit points (`cut`)
  - Very aggressive inlining intent

## Why you might pick this crate

Concrete advantages (especially for language tooling):

- **Explicit backtracking control** (`cut`) that influences rollback across combinators
- **Stateful parsing support** (`ParserMut`, plus env/local patterns via `In`)
- **Inlining-oriented design** for “hand-written parser”-like performance profiles

## Using from another project

This crate currently lives in the YuLang workspace. The easiest way to try it is a path dependency:

```toml
[dependencies]
chasa = { path = "/path/to/yulang/crates/chasa" }
```

## Links

- Repository overview: `README.md` at the workspace root
- API & examples: crate docs and doctests under `src/`
