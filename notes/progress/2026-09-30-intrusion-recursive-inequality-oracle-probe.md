# Recursive bounds and inequality interval: Oracle characterization

Date: 2026-09-30
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: one temporary Rust-path interval probe; not an equi-recursive test

## Fixture and result

A temporary Rust test in an isolated detached worktree constructs an ordinary
scheme with one quantified variable `q`, predicate `q`, and recursive interval

```text
Bottom ≤ q ≤ Arr(Int, q)
```

The function uses bottom argument effect, top result effect, and the same `q`
as result. The focused command was:

```text
CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target \
  cargo test -p infer accepts_bottom_lower_with_recursive_upper_constraint -- --nocapture
```

It passed. The test asserts that scheme use emits no diagnostics, the use value
receives a fresh variable, the trivial `Bottom` lower is absent from that
variable's stored lower-bound list, and it has a stored Function upper bound
with `Int` argument, bottom/top effects, and a result pointing to the same
fresh variable. Oracle code emits the interval as `lower ≤ fresh ≤ upper`
(`crates/infer/src/instantiate.rs:1002–1028`); canonical constraint insertion
drops a `Bot` lower or `Top` upper as trivial
(`crates/infer/src/constraints/machine/entry.rs:1092–1100`).

An independent `compiler_referee` reviewed the fixture. The evidence shows
acceptance of this one self-referential upper inequality after ordinary scheme
instantiation. It is consistent with assigning `Bottom` to the variable under
the ordinary bottom rule, but the test does not actually instantiate that
assignment or assert it as a solver result. The test does not compare two
recursive structures, enforce `q = Arr(Int,q)`, or establish an
equi-recursive/coinductive subtype rule. Such claims would overstate the probe.

A second temporary Rust test builds one ordinary scheme with both bound sides
guarded by the same function shape:

```text
Arr(Int, q) ≤ q ≤ Arr(Int, q)
```

It routes one scheme use and asserts no diagnostics, a fresh use variable, at
least one stored lower Function and one stored upper Function, each with the
expected `Int` argument/effect polarities and a return pointing to that same
fresh variable. Its command was:

```text
CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target \
  cargo test -p infer accepts_guarded_recursive_function_as_two_sided_bounds -- --nocapture
```

An independent `compiler_referee` confirmed this exact scope. The test shows
that the Oracle accepts and retains both matching guarded recursive bound
shapes on one instantiated variable. It does not establish uniqueness of the
bounds, select a concrete solution for `q`, compare two distinct recursive
schemes, or define equi-recursive/coinductive subtyping. Such claims would
require separate comparison and solution fixtures.

## Limits and state

Both test sources exist only in `/tmp/yulang-intrusion-recursive-bound-probe`,
a detached scratch worktree at the frozen Oracle revision; neither the frozen
Oracle worktree nor this research branch was modified. No Python was used. No
compiler implementation code or durable tests were changed. One focused Rust
test ran; it compiled the `infer` test target and emitted existing unused-code
warnings in that frozen checkout. No resource or performance measurement was
run.

This narrows the Oracle evidence for the distinction between an inequality
cycle and a recursive equation. It does not resolve Gate C's recursive subtype
rule, carrier, environment-fiber proof, scheme principality, or the broader
intrusion equivalence theorem.
