# Local-use retention implementation sprint closeout

Sprint: `local-use-retention-implementation-20261017`, revision 1.
Branch baseline: `research/simple-sub-intrusion` at
`9a2c7d80826ae33493f2bcc4786bc06e450ae36a`.
User approval: `採択で構いません`, recorded in the pinned approval receipt.

## Outcome

Implemented the reviewed rows-preserving option in
`crates/yu-solver/src/candidate_scheme.rs`. `FreshUse.rows` still moves to the
existing sole `LocalFreshRoute.rows` owner. The other eight fields move once to
private route-owned `RetainedFreshUseMaps`. `refresh_bytes` accounts those
capacities once; route vector capacity accounts the retained inline header;
commit no longer subtracts storage that remains live. Existing route
reservation, Graph/rows consumer, and rollback/journal ownership remain intact.

The accepted limitation remains: retained maps increase session memory and may
cause earlier resource-limit rejection. Physical overhead and the practical
resource envelope are unmeasured.

## Proof and gate status

Fresh independent reviews were sequential and all CLEAN within their assigned
scope:

1. `/root/local_use_retention_compiler_review` — compiler ownership,
   exact-once transfer, capacity accounting, publication and rollback.
2. `/root/local_use_retention_arch_review_v3` — ownership/lifecycle, route
   sizing, reservation/journal rollback, and retained storage accounting.
3. `/root/local_use_retention_spec_review_v3` — exact approval, corrected M2's
   valid pinned-`v0` boundary, adopted NPAIR limits, and expected-output scope.

The applied correspondence proof establishes the source-grounded structural
map and accounting identity and applies corrected M2 only to valid finite
structural-query evaluations at pinned precommit `v0`, subject to its owner,
non-reuse, relocation and unchanged-read-projection premises. No runtime
validity checker or new semantic consumer is implemented.

Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN. Still
missing: native formal-pair/negative-port emission, authentic derivation-indexed
At and full transport, whole-presentation `rho_u`, actual receive consumer,
subtraction, N-Transport, F1/FK1 and production authority. Structural maps do
not establish Permission, provider lineage, authentic At, future absence or
residual eligibility.

## Checks and limitations

- `git diff --check`: PASS.
- `python3 tools/agent_sprint.py check`: PASS; static consistency only.
- `cargo check -p yu-solver --features shadow-apply-candidate --tests`: PASS in
  9.12s. Test targets compiled; no tests executed.
- No runtime, test, benchmark or physical-memory measurement was performed.

All three reviewers and both authors are STOPPED. Observed model/effort for
reviewers and proof author remained UNKNOWN where the runtime exposed no
metadata. The primary charged the implementation's full 300s cap, proof's full
360s cap, each review's full 120/100/80s cap, 60s coordination, and measured
compile time rounded up; total charged 1029s within the 1200s envelope.

## Frozen outputs

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` |
| `notes/progress/2026-10-17-local-use-retention-implementation-approval.md` | `356231ad001a02c5085119412af26534e56e38082aca747262e8873ffa67f13c` |
| `notes/theory/2026-10-17-local-use-retention-applied-correspondence.md` | `198046b6eb398734cf657ab03f05e171f8be568c1e8feb31115b9adc46d5f1ff` |
| `tasks/agent-loop/inbox/20261017-local-use-retention-implementation.md` | `e78fd6cee9c1afeac740158b45084647dc495b963ddbafaad00f9f8f26b9b009` |
| `tasks/agent-loop/inbox/20261017-local-use-retention-applied-correspondence.md` | `edec4fc3252351f62235ed7caaed6844c720d17e6a3805fb9f9fa9dd310e7fa4` |
| `tasks/agent-loop/sprints/local-use-retention-implementation-20261017.md` | `c6ed05c5ed10e16d97cfe4e367af5f2bc2a8e650f2169ec8e8d81b7df81e9935` |

Luna alone integrates. The unrelated modified
`tasks/agent-loop/sprints/authentic-source-and-forward-handler-20261017.json`,
three historical UNKNOWN reservations and quarantined board lease are preserved.
No force push; commit only the listed sprint artifacts plus compact current
state and this closeout.

Sprint-end `next_action_selector` recommendation: proceed to a separate native
NPAIR formation-contract sprint. Its first proof packet targets
`candidate_effect::candidate_formal_pair`,
`candidate_formal_effect_port`, `candidate_formal_annotation` and the
`candidate_source` registration/preflight boundary. It must derive the shared
negative port, separate permission declaration and both ordinary edges while
preserving symbolic dependencies and J1/J2. A later implementation-readiness
packet may specify exact producer changes and an unapplied patch; this outcome
grants no new compiler-code lease, preflight enabling or subtraction.
