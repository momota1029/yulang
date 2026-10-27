# Sprint FORMAL-PERMISSION-PROJECTION-20261028/r1

Status: ACTIVE — exact source/proof outputs leased by Luna
Baseline: `aa33dd79f5166dcd22174ab6403d56c3e5fe2f10`
Original goal: full Yulang inference/executor soundness, with effect hygiene,
principality, termination, original A/B and source/native quantifiers retained.

## Fixed outcome

Establish or falsify that every permission in a successfully completed
formal-construction/capture/export path is projected to the captured image of
the exact open effect port constructed for its original annotation occurrence.
Preserve the original parameter, HIR occurrence, source row, resolved concrete
operands and structural Function/Tuple path. Quantify over represented
permission lists and paths. Missing capture roots and malformed graph paths
must remain explicit failure cases. If a premise cannot be derived from the
pinned owners, freeze the first missing constructor/capture premise and its
owner. This result advances provenance only; the actual effect-hygiene parent,
handler eligibility, residual semantics, source/native correspondence, A/B and
production remain OPEN.

## Authority and frozen baseline

Luna owns authority, `current.json`, this contract, integration and Git.
No permission-activation or language-semantic change is authorized. The Rust
owners are read-only for the source lane. Cargo, tests, compiler probes and
Astra are not authorized. Unknown-writer paths in `machine.rs` and
`receiving.rs` remain quarantined and are outside this sprint.

Direct dependencies:

| Owner | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |

The accepted policy distinguishes annotation permission, actual constraint
inflow and the residual after an actual handler. Concrete negative formal
annotation grants a local subtraction permission; it does not impose a closed
upper bound or itself perform handling. Preserve symbolic tails and independent
same-family contributions in every later application of this result.

## Work lanes and exact leases

### Constructive proof — registered `lean_prover`, 650 seconds

Use a faithful Lean model of the pinned constructor and lookup operations.
Prove the structural path correspondence for Function Argument/Result and
Tuple Element steps, then compose it with graph capture and
`CandidateGraphExport::formal_effect_permissions`. Show the exported node is
the captured image of the constructor's port, not merely a row with an equal
family or canonical coordinate. Cover shared rows, separate occurrences with
equal concrete families, aliases/representatives, polarity changes and
missing captured roots.

Leases:

- `notes/theory/lean/YulangClosure/OriginalFormalPermissionProjection.lean`
- `tasks/agent-loop/inbox/formal-permission-projection-20261028-proof.md`
- `/tmp/yulang-formal-permission-projection-20261028/proof/`

Maximum 10 Lean/Lake calls and 300 seconds; one CPU, 1 GiB, one verifier.
Reserve five calls and the sole verifier invocation for the new module's
skill-required full verification and complete type/transitive axiom audit. Stop
at the bound. A failed derivation is reported with the first missing premise;
do not replace it with a theorem that assumes the desired capture law.

### Source correspondence — `implementer` role, 200 seconds, read-only Rust

Trace only the pinned constructors, captured negative-formal roots and export
lookup. Independently challenge occurrence identity, structural path, shared
port identity, canonical row merging and malformed/missing root behavior. Find
the first actual consumer and state exactly what it does. No edits to Rust,
tests or fixtures; no build or Cargo.

Lease: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source.md`.

### Review and Luna integration

Fresh non-author review receives the frozen proof module, source handoff,
contract and direct dependency hashes. Review budget: 200 seconds. Luna has 100
seconds for intake/adjudication; dispatcher reservation is 50 seconds. Review
must check the complete source simulation and failure cases against original
quantifiers. No author certifies their own work.

## Stop conditions and parent application

Stop on any dependency hash mismatch, unleased path requirement, unclear
constructor authority, resource bound, or required source claim unsupported by
these owners. Do not expand the source read set or change the selected semantics.
The parent application must state whether exact port identity follows for
successful projections, the first source premise left open, and why this result
does not establish permission arrival, actual handling, residual preservation,
whole effect hygiene, A/B, source/native correspondence or production.
