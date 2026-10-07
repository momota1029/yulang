# Default-off shadow evidence for exact self-initialization boundary

Date: 2026-10-07
Baseline: `c6067ef51ba2c9ca6018ea282152e6d52f7f7af7`
Status: focused shadow implementation; independent spec review PASS
Authority: approved q1/d1 as extracted by `notes/design/2026-10-07-recursive-self-init-executable-boundary.md` §§1–5
Production execution enforcement: pending; no production path changed

## Scope

The existing cold initialization inventory now distinguishes the exact
approved source envelope from other structural self-Name candidates. For one
private, parameterless binding whose complete RHS is a resolved Name of its
own binder, with no HIR errors and a singleton SCC, the inventory exposes
`Reject(SelfInitNoValue, original binder, original RHS occurrence)`. Every
other candidate or source shape produces `Unresolved`; unresolved evidence is
not permission to initialize or read the RHS.

The classifier uses retained HIR constructors and branded source identities.
It does not inspect identifier spelling, inferred `Never`, solver success,
endpoint shape, or runtime state. HIR lowering preserves the distinctions
used here: unsupported grouped/annotated binding forms are not lowered as a
plain binding, and parenthesized RHS forms are not erased into the direct Name
constructor.

This is cold, default-off evidence behind the existing
`shadow-f5` + `shadow-scc-observer` feature gate. It can be inspected before or
after solve, preserves the current inference result and solver facts/errors/
counters, and does not change execution acceptance. Production rejection
before initialization/RHS read remains an implementation obligation. Other
recursive initializer classes remain outside the approved q1 decision.

## Review and checks

Independent spec-auditor review passed the frozen two-file diff without
findings, against the approved boundary and exact source-envelope rules. The
focused `shadow_initialization` integration test passed all five tests with
both existing shadow features, `RUSTC_WRAPPER=` and one Cargo job. The ordinary
wrapper invocation could not execute the configured sccache (`Operation not
permitted`); no compiler or test failure was reported by the unwrapped run.
`rustfmt --check --edition 2024` passed for the two changed Rust files.

The tests cover exact rejection evidence and original identities, unchanged
`Bottom` inference/facts/errors/counters, and unresolved outcomes for extra
declarations, parameters, lambda self-use, aliases, unresolved Names,
annotations, parenthesized forms and non-private visibility. They also retain
foreign-collection/source rejection checks. No broad suite or production
execution check ran.

The exact `REC_INIT_SELF` semantic subcase remains CLOSED by the approved
source rule and its proof. This slice advances only HIR_WIRING's default-off
implementation evidence. Aggregate `REC_INIT`, production enforcement,
SOURCE_ADEQUACY and cutover statuses do not change.
