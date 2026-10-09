# Authentic operation producer integration

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `4c3a74356991a7e94e7c49e1c39115bf23557473`
Authority: current complete-inference objective, the
[integration gate](2026-10-10-operation-producer-integration-gate.md), frozen
Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` Act/signature constructors,
and the [active withdrawal policy](../design/2026-10-10-simple-sub-legacy-withdrawal.md)
Mode: M2; two independent semantic/conformance reviewers; measurement budget zero

## Implemented owners

HIR retains actual nullary Act families, bodyless typed function members,
declaration-owned operation identity, visibility, signature/name positions and
qualified-use occurrences. Two-pass family/member indexes resolve forward
signature references without per-use declaration scans. Missing/private and
ambiguous references reject; duplicate errors are not placeholder permissions.
Unsupported/recovered bodies are not silently discarded.

The solver shares structural signature construction with actual annotation
construction, using an explicit operation context instead of fabricating an
annotation wrapper. Each lookup introduces its own younger signature variables
and exact-pure evaluation effects. Omitted rows retain their actual polarity
defaults throughout nested Functions. The owning family is prepended only to
the outer return-effect row, preserving every original member and symbolic tail.

Typed view provenance and borrowed `OperationInterfaceMember` conflicts retain
the actual declaration, signature position, originating lookup and member index.
Centralized view copy transports that data through ordinary freshening and
extrusion. These are interface operands, not emitted execution contributions or
subtraction permissions. No global Call registry, early satisfiability admission
or callee-shape Force was added.

## Review and protected test contract

Initial `operation_producer_semantic_review` and
`operation_producer_conformance_review` reviewed the frozen nine-path artifact.
The primary accepted the exact member-preservation finding and the insufficient
independent-alias regression. `operation_producer_batched_repair` prepends without
deduplication and adds truthful duplicate-member ordinal coverage. It strengthens
alias coverage with restrictive primitive result boundaries and opposite-leaf
absence. A newly unused compatibility wrapper is now explicitly test-only.

The conformance reviewer gave pre-write expected-contract adjudication for
`act E {}`: the old unsupported premise represented the former producer envelope,
not a language prohibition. This gate replaces body rejection, and frozen Oracle
`lower_act_body_contents` has no nonempty condition. That one case moved into
positive empty-family/annotation coverage; remaining unsupported assertions and
existing test names remain unchanged. No rejection was invented to preserve an
obsolete construction restriction.

Fresh `operation_repair_semantic_delta` and `operation_repair_contract_delta`
closed production repairs but identified unsupported top-level effect adornment
in the stronger alias fixture. A separate exact string repair uses supported
whole-binding Unit/Int value annotations without changing any assertion.
`operation_alias_fixture_closure` verified both hashes and the original-body
checking responsibility. All assigned findings are adjudicated and closed.

## Exact verification

All Cargo commands used `RUSTC_WRAPPER=`, `timeout 180`, `--offline`, `-j 2`;
tests also used `-- --test-threads=1`, with one Cargo process at a time.

- `cargo test -p yu-hir --features shadow --test operation_source`: 4 passed.
- `cargo check -p yu-hir --all-targets --features shadow`: passed.
- `cargo test -p yu-solver --features shadow-apply-candidate --test candidate_operation_source --test candidate_effect_annotation --test candidate_unit_source --test simple_sub_local_source_retirement --test candidate_lifecycle_retirement --test shadow_apply_candidate`: 41 passed across six targets.
- Solver same feature, `--lib candidate_effect::tests`: 9 passed, including
  lookup purity, nested defaults, symbolic tail copy and payload rollback.
- Solver same feature, `--lib candidate_intrusion::tests`: 5 passed.
- Solver same feature, `--lib candidate_lifecycle_retirement`: 5 passed.
- Solver same feature, `--lib candidate_graph_call_`: 2 passed.
- `cargo check -p yu-solver --all-targets --all-features`: passed.
- `cargo check --workspace`: passed.
- Scoped whitespace and frozen dependency hash checks passed.

Final evidence covers 66 distinct tests without warnings. Initial runs exposed
the old empty-body fixture and the unsupported strengthened alias input; those
failures are retained in the causal review record above, not counted as passes.
No broad solver/backend suite or semantic proof ran.

## Cost and remaining requirements

HIR indexes are constructed once; operation lookup uses indexed family/member
resolution. Signature construction and payload measurement are linear in the
signature nodes/row members per lookup. Immutable payload size is copied with
provenance so view copies do not rescan the signature. View capacity includes
the added provenance; nested storage conservatively charges shared declaration
payload per view. Existing checkpoint rollback restores views and nested charges,
and operation-local scratch is released. No benchmark decision was needed;
measurement consumption is zero samples and zero processes.

Actual request-carrier execution, designated consumers, emitted contributions,
contravariant subtraction attachments, complete Call, hygiene correspondence,
independent public schemes, soundness/principality and F5/default target cutover
remain required. Lookup support is not an execution supplier. Operation-specific
full capture/intrusion execution and backend behavior remain unverified by this
slice. Records synchronized: `tasks/current.md`, design index, integration gate
and authentic-operation constructor packet. Pending questions remain excluded
from Git.
