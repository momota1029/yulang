# Outcome — EFFECT-PERMISSION-LIVE-CAPTURE-20261028/r1

Status: **CLOSED_INCOMPLETE**. This checkpoint continues the user's unchanged
Yulang inference/executor soundness goal; it closes no parent theorem or
production gate.

Baseline was `88c2fad87`; admission commit was `6dc6de301`. Amendment 01 was
admitted after a source compile failure and selector review; the final evidence
checkpoint is `fd569583f` plus this outcome/current-state update.

## Before and after

Before: a checked finite catalog theorem, but no actual successful-constructor
derivation or live LIFO capture simulation. After: a checked 25-theorem
conditional constructor-history/key-only model and one focused passing Rust
trace from an internal producer fixture. The trace cannot support a claim about
formal-root non-arrival because the fixture captured the wrong row coordinate.
Actual source acceptance and constructor-to-export correspondence remain OPEN.

## Lean evidence

Frozen module:
`notes/theory/lean/YulangClosure/FormalPermissionLiveCapture.lean`, SHA-256
`0e1bd4f2ae95e798561e014595e66ec9b6d9b342dbd2b15d0d5c9d346838c53e`.
Handoff:
`tasks/agent-loop/inbox/effect-permission-live-capture-proof.md`, SHA-256
`6f7b51ae52ed23dc8afbe35e856d054e005965e499554b745edfcc4cd903ee56`.

Pinned Lean 4.35.0 check exited 0; all 25 authored declarations had complete
printed theorem types and transitive axiom audits. Only standard axioms occur:
`propext`, `Classical.choice`, and `Quot.sound`. The module proves its stated
conditional relations; it does not establish successful Rust-call realization.
First unsupported constructor recurrence: symbolic memo miss allocation in
`candidate_formal_effect_variable`, followed by delegated
`candidate_signature_effect` allocation. Canonical transport, stored-node
writes, actual row/bound/evidence/context request recurrence, source preflight,
root arrival and export remain OPEN.

Heavy check: exit 0, 5.21 seconds, 976,396 KiB peak RSS, one CPU. Three
lightweight probes were used; two failed and their diagnostics are retained in
the handoff. No default/root integration ran.

## Rust evidence and review

Final provisional sources:

- `crates/yu-solver/src/candidate_effect.rs`, SHA-256
  `f0b08ea8cee26e372b2a2e0b8076b82e4e6e29fa73618fe9cddfe360df117b8f`
- `crates/yu-solver/src/candidate_scheme.rs`, SHA-256
  `33c066da527c3251d106aa9ca9a4f77d3f54844478ea2f6f2258933a5eb30852`

Initial Rust handoff SHA-256
`3c77c6a39fb100c1cdc4795ba6c89b7ac457109dd620a573c68e43999bf1b44f` records
the first Cargo invocation: exit 101 before tests, 37.32 seconds, 1,159,420 KiB
RSS. It identified four missing `Debug` uses and one private capture method.
Two post-attempt corrections were made and remained unvalidated until
amendment 01.

Amendment 01 SHA-256
`7187d34d7a0fdf5dba92eccadde029da443d7666f9616e027145dd10054b373a` authorized
exactly one additional focused invocation, funded by 240 seconds reallocated
from contingency. It exited 0, 41.49 seconds, 1,656,320 KiB RSS; one test
passed. The run used one CPU and started with 24,068,370,432 bytes available.
Amended Rust handoff SHA-256
`487170dde32a33cb9466d3d2248d9ed3b4730f23707b70a762927dc30d503023` records
the two observed origins and the capture result. The fixture directly calls
`candidate_formal_annotation` and bypasses source preflight.

Fresh independent review:
`tasks/agent-loop/inbox/effect-permission-live-capture-review.md`.
The reviewer accepted the Lean result as conditional and found:

- **MAJOR:** the test passes `parameter` to capture instead of the constructor's
  actual row `parameter_live_base + parameter`. It captures `ValueRow(0)`
  without proving that row is the annotated parameter. Therefore the empty
  `negative_formal_roots` observation does not establish formal-root
  non-arrival. The assertions accept any origin event and any returned graph.
- **BLOCKING for promotion:** no Rust successful-call realization, scoped memo
  and allocation simulation, canonical transport, concrete stored-node walk,
  or full row/bound/context recurrence is established.
- **BLOCKING for a returned port:** numeric `idxOf` agreement does not prove
  endpoint membership or export. The fixture does not call the permission
  export helper.
- **MINOR:** canonical endpoint formatting is eager in test builds even when
  the recorder is disabled; both Rust handoffs overclaim laziness.

The successful Cargo run remains evidence that the submitted fixture executed
within the admitted envelope, not evidence that it observed the intended
formal parameter or export path. The test-only instrumentation is provisional
and needs a new exact packet before correction or another run.

## Changed paths and checks

Changed paths: the sprint contract and amendment, Lean module, Rust source files,
four proof/Rust/review handoffs, current state and this
outcome. No expected-output, source-language, solver-choice, runtime, public
API, or production behavior change is claimed. Reviewer noted the test-build
allocation overhead from eager instrumentation.

`python3 tools/agent_sprint.py check` passed on each synchronized snapshot;
`git diff --check` passed on frozen Rust sources and scheduling records. Static
checker output is not independent review or proof evidence. No parent source
acceptance, effect hygiene/subtraction, Simple-sub A/B, whole soundness,
principality, progress, termination, source/native, or production gate closed.

## Next bounded step

The next-action selector recommends a fresh fixed packet for source-qualified
origin/root/capture correspondence. Correct and authenticate the actual
parameter-row mapping, strengthen the fixture assertions, add a separate
ordinary source-solve entry observation without bypassing preflight, and model
memo hit/miss plus delegated allocation in Lean. Keep the checked 25-theorem
module immutable. Preserve all parent gates OPEN and all runtime-writer
quarantines.

Only Luna stages, commits and pushes. The user’s broad goal remains active.
