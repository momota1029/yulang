# R252 result — contravariant effect rows keep an open tail

Status: implementation result; solo and unreviewed. The R235 higher-order
mismatch premise is superseded. R71/R72, source/native and production gates
remain OPEN.

## Correction

The user clarified that `[io]` in a contravariant position means `[io, 'e]`.
Therefore an actual `[state]` callback does not violate a formal annotated
`int -> [io] int`. The R235 assumption that this row was a closed upper bound
was wrong. The direct positive annotation `my good: int -> [io] int = bad`
remains a valid mismatch control and does not establish the higher-order rule.

## Implementation

Removed the negative formal-effect `EffectRow(port) <: Allowance([io])` edge.
The branch still retains `FormalPermission` with the original source owner,
path, row and concrete families for local handling semantics. The CLI test now
expects a `[state]` callback to infer when the annotated formal is unused,
called, or supplied inline; the direct positive annotation still reports
`IncompatibleEffect`.

R251's new source Tuple form also exposed exhaustive inference and runtime
consumers during the playground build. Candidate source preparation now
returns its existing unavailable result for Tuple, and runtime compilation
rejects it as an invalid source reference. Runtime source-range traversal still
walks all tuple elements. No tuple inference or runtime representation is
claimed.

## Evidence

- The corrected `cli_higher_order_effect_mismatch` test passed: direct positive
  mismatch rejected; unused, called and inline contravariant `[state]`
  callbacks accepted; compatible `[io]` callback accepted.
- `cargo test -p yu-playground` passed, including the CLI regression, runtime
  module expression tests and existing checked-in examples.
- `cargo test -p yu-hir --lib` passed all 139 unit tests.
- The R251 colon application, ordered tuple, singleton tuple, Unit/Group and
  ordinary expression carrier tests passed.
- `rustfmt --check` reports drift on each edited Rust file; checking the
  corresponding `HEAD` files produces the same result. The new and edited
  sections follow the formatter without reformatting unrelated code.
- Static sprint-state check and `git diff --check` passed.
- No independent review or source/native proof was performed.

## Remaining work

The R149 Types and Console samples are still open. The Tuple carrier is not
consumed by inference and cannot be evaluated. Semantic imports, public closed
schemes, host writes, output publication, original theorem closure and
independent review remain open.
