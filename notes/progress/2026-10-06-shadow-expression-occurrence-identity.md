# Shadow expression occurrence identity

Date: 2026-10-06
Status: Implemented and compiler-referee-reviewed; opt-in structural plumbing only
Baseline: `388469ea4dca94be5553b89d0bf6927bd68f0b92`, `research/simple-sub-intrusion`
Scope: exact raw-CST identity for projected shadow expressions
Implementation authority: user's 2026-10-06 shadow/experimental lane decision

## Result

Each expression in the default-off HIR shadow skeleton now retains its exact
raw-CST `PositionId`: integer literals and identifier uses retain their leaf
nodes, groups retain their `ParenthesizedExpression`, and each left-associated
ordinary `Apply` retains its corresponding `MlArgument` or `CallTail` node.
The existing expression range still spans the full projected expression;
the position names the individual source occurrence that formed it.

The adapter checks artifact ownership, position bounds, syntax-node status,
node kind, and equality between a `Use` expression and its pre-existing exact
use position before publishing the skeleton. Missing or ambiguous source
handles fail construction. Projection remains iterative and no partial
skeleton escapes. Positions are syntax identity only: they do not form
`beta`, `Slots(beta)`, a typed path, a role, `Flow`, owner/receiver relation,
profile, or call judgment. Existing pending callable-role, complete-Function
membership and call-view-realization premises remain unresolved. Production
inference is untouched.

## Review and verification

The bounded implementation owns only `crates/yu-hir/src/shadow.rs`.
`compiler_referee` independently reviewed the full diff, exact parser-node
mapping, artifact branding, validation, ambiguity behavior, atomicity and
iterative construction against inferred Function call views §§2,5 and the
nested-block source addendum §§2–4. The reviewer found no blocking, major, or
minor correctness issues. The review did not certify production inference or
measure performance.

Focused checks passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow shadow -- --test-threads=1
rustfmt --edition 2024 --check crates/yu-hir/src/shadow.rs
git diff --check -- crates/yu-hir/src/shadow.rs
```

The test command passed 22 unit tests and one matching integration test. One
initial run exposed an invalid new-test assumption about CST-tail spelling and
traversal order; it was replaced by exact retained-occurrence coverage. Existing
expected behavior was not changed. Two focused runs used at most two Cargo
jobs and one test thread; compile durations were 2.34s and 0.80s. No performance
experiment or broad suite was run.

## Boundary and next work

This closes only expression-to-source-node identity in the shadow artifact.
It does not establish position/profile identity `beta`, annotation-to-port
correspondence, typed incidence, recursive Q/R identity, use-time freshening,
source registration, old/new scheme parity, soundness, principality, or source
adequacy. The next successor slice may consume these retained occurrences only
to add further independently settled structure; unresolved semantics stay
explicit premises until their rules and proofs are supplied.
