# Recursive bounds and inequality interval: Oracle characterization

Date: 2026-09-30
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: focused temporary Rust-path interval/constraint probes; not an equi-recursive test

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

All temporary test sources exist only in
`/tmp/yulang-intrusion-recursive-bound-probe`, a detached scratch worktree at
the frozen Oracle revision. No frozen Oracle source, compiler implementation,
or permanent test changed. No Python was used. Four focused Rust tests ran;
they compiled the `infer` test target and emitted existing unused-code
warnings in that frozen checkout. No resource or performance measurement was
run.

## Independent narrowing/use constraints

Two more temporary Rust tests use independent fresh `AnalysisSession`s from
the same hand-built interval and its ordinary scheme-instantiation path. In
the first, adding `q <: Bottom` emits no diagnostic, and the fresh variable
retains both its `Neg::Bot` and self-referential `Neg::Fun` upper rows. In the
second, without the `q <: Bottom` constraint, adding `String <: q` yields
exactly one `UnsatisfiedSubtypeShape` with actual `Constructor(["string"])`
and expected `Function`. The tests and shared fixture are in the detached
scratch file `crates/infer/src/analysis/tests/case_02.rs`, helper
`recursive_interval_use`, tests
`recursive_upper_interval_accepts_bottom_narrowing` and
`recursive_upper_interval_rejects_incompatible_concrete_lower`.

The focused command was:

```text
CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target \
  cargo test -p infer --lib recursive_upper_interval -- --nocapture
```

Both tests passed. A follow-up `compiler_referee` review confirmed that the
separate sessions remove the earlier sequencing confound and that the exact
diagnostic is asserted. The evidence characterizes this hand-built scheme's
instantiation/constraint path only. It does not compare against an equation
interpretation, establish source-to-SCC generalization behavior, or prove the
proposed intrusion semantics.

All four temporary tests remain confined to the detached scratch worktree. No
Python, resource measurement, or permanent test change was made.

This adds a narrow constraint-path characterization for one recursive
interval. It does not establish a general distinction theorem between
inequality cycles and recursive equations, nor resolve Gate C's recursive
subtype rule, carrier, environment-fiber proof, scheme principality, or the
broader intrusion equivalence theorem.
