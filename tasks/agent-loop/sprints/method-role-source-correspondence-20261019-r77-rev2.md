# Sprint method-role-source-correspondence-20261019-r77 — versioned verification and error-ownership correction

Status: CANDIDATE — Luna activation pending exact-contract selector delta and current-state receipt
Revision: 2; preserves all rev1 claims and records its exact failed outcome below.
Branch / baseline: research/simple-sub-intrusion / af3ccf2d63ba7f87e0359e183568db548ea53307
Rev1 contract SHA-256: 26735a4d825ecd783856675dadb91b9d97df5f8b71e8f62d1fde06b92d8ce3b1

## Unchanged parent and sprint outcome

Preserve the unchanged Simple-sub inference/evaluator and A/B obligations, source domain, accepted semantics and all original quantifiers. R76 source projection and R77 correspondence remain prerequisites only. Parent/evaluator/A-B remain OPEN 0→0; R50 remains NOT_ADOPTED.

The sprint outcome stays method FieldTail receiver correspondence plus exact same-artifact RoleDeclaration/standalone ImplDeclaration nodes. It adds no method typing, role selection, dispatch, generated inference constraints, evaluator path, or production change. The user priority remains balanced breadth and established proof depth, with method syntax and roles included; effect-storage has no automatic continuation.

## Frozen rev1 outcome and reason for this revision

Preserve rev1 contract and bytes unchanged. Its only authorized command ran exactly once and failed with 2 passed, 1 failed, 132 filtered: the assertion expected receiver source slice `"b"` and observed `" b"`. There was no retry. Failure receipt: `notes/progress/2026-10-19-r77-rev1-verification-failure.md`, SHA-256 `644119a06abfd2b2cc3ddc1448ee5eb948241546dd9d4db4a330441ea242899b`.

Independent pre-write spec review established that the receiver is a constructor-owned syntax node whose full range includes its leading trivia: `value()` retains `range_of(node)`/`node.text_range()`, and `structural_continuation` moves that receiver unchanged into child zero. The fixed R77 claim is correspondence to the actual produced receiver, not an identifier-token-only span. The sole test expectation correction below preserves the exact range behavior and does not trim implementation output. This causal rationale satisfies `rules/testing.md` Expected-output protection. The review verdict is included in the frozen failure receipt; it returned inline because the reviewer role does not permit artifact writes.

## Exact authorized delta

After Luna activates this revision:

1. In `crates/yu-hir/src/tests/shadow_member_receiver_association.rs`, change only the expected source slice in `operator_receiver_comes_from_association_child_zero` from `"b"` to `" b"`. Keep the observed receiver range, test name, successful-path code and other assertions unchanged. Do not trim or alter source ranges.
2. In `crates/yu-hir/src/shadow.rs`, change `visit_associated_member_receivers` from `Result<(), ShadowError>` to `Result<(), HirAvailabilityError>`. Preserve the three existing `AssociationError` distinctions at the association boundary using the existing ordinary-lowering mapping: `ExactOperatorEnvironment` -> `HirAvailabilityError::ExactOperatorEnvironment`; `StructuralInvariant` -> `HirAvailabilityError::StructuralProjection`; `Allocation` -> `HirAvailabilityError::IdentityExhausted`. Map this method's own shadow structure failures to `StructuralProjection` and `ElementLimit` to `IdentityExhausted`. No new `ShadowError` variant is authorized. Preserve successful association, callback order/atomicity, receiver identity/range and role-node behavior. The only callers are the two leased tests.
3. Update the R77 rev2 implementation receipt and handoff with rev1 failure, spec rationale, exact final hashes, and the single rev2 verification result. Do not edit the frozen rev1 note, proof, handoff, implementation source snapshot or failure receipt.

The R77 proof author remains STOPPED. The rev1 proof note stays frozen and retains its original test/source hashes; final reviewers must state which constructor claims still apply after the narrow error-mapping delta. No proof rewriting or second proof lane is authorized in this revision.

## Dependencies and exact paths

Preserve all rev1 design/spec/source pins and revalidate their unchanged bytes. Additional direct evidence pins:
- `rules/testing.md` SHA-256 `829eb0c6b6b10db902f0329e3117351b92dba9ca1480ef5722ccd6d2fabbb524`.
- `crates/yu-hir/src/module.rs` SHA-256 `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` (read authority for `HirAvailabilityError` and the existing error mapping).
- Rev1 frozen implementation: `shadow.rs` `9bf3e046a55206607527d2df3dde42b32afa814bc8d8b82c814583923aefc856`; `lib.rs` `afd9b382d95e2a8d22635eaf6b9bd8f134b80f5ebd35789265e236884b0fa58e`; test `e79889830b28aedcf7f8116d9327ca42c4b29d95e5f462e1f93d8a313c5e7093`.
- Rev1 proof note `edf2ce4b3bb3e0f24d715f7a95a9b4c22fe2cf4c287c04171bbf96d574ca4fc0` and handoff `513724eef84fdde1036c16bb35e0ed959570711621d721942aae0fb6be975125`.

Write leases after activation:
- Luna: `crates/yu-hir/src/shadow.rs`, `crates/yu-hir/src/tests/shadow_member_receiver_association.rs`, `notes/progress/2026-10-19-r77-member-role-implementation-rev2.md`, `tasks/agent-loop/inbox/20261019-r77-implementation-rev2.md`, this rev2 contract, `tasks/agent-loop/current.json`, and `notes/progress/2026-10-19-r77-closeout.md`.
- Luna must first preserve exact rev1 overlay bytes at `tasks/agent-loop/sprints/r77-rev1-shadow.rs`, `tasks/agent-loop/sprints/r77-rev1-lib.rs`, and `tasks/agent-loop/sprints/r77-rev1-test.rs`, each verified against the hashes above. These are immutable recovery snapshots; the working source/test paths above are explicitly authorized new rev2 revisions. The committed baseline and rev1 frozen proof/handoff/failure receipt remain unchanged.
- Fresh compiler delta reviewer: `tasks/agent-loop/inbox/20261019-r77-r2-compiler-review.md` only.
- Fresh spec delta reviewer: `tasks/agent-loop/inbox/20261019-r77-r2-spec-review.md` only.

R76 proof/test files, R77 rev1 proof, all R74/R75 paths and solver files remain frozen/excluded. R75's preserved dirty tree remains untouched.

## Verification, reviews and stop conditions

After the combined source/test delta freezes, run exactly one additional command: `CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_member_receiver_association -- --nocapture`. This is the only extra attempt after rev1. No rerun, repair or expectation edit follows any rev2 timeout/failure. If it fails, preserve both receipts and close this bridge UNFINISHED/OPEN.

Fresh independent compiler and spec delta reviews each have a maximum 120-second grant and distinct output paths above. Compiler review checks the exact error mapping, affected existing error consumers, borrowed receiver/atomic publication and unchanged success path. Spec review checks this contract, expected-output rationale, rev1 proof applicability and unchanged semantic boundaries. Both may be read-only and return inline for Luna to preserve; no extra review panel. All blocking/major findings must close before acceptance.

Request an explicit additional 420-second envelope over rev1: Luna 180s maximum for the two narrow edits, receipts and single 120-second command; fresh compiler review 120s; fresh spec review 120s. The failed rev1 command and stopped proof/review assignments create no refunds; their unknown elapsed amounts are not carried forward. This raises the sprint cap from 2400s to 2820s, below the repository default 7200s. Astra remains 0. If the exact grant, scope or remaining capacity is unavailable, stop rather than imply renewal.

Falsifiers remain wrong receiver, foreign/ambiguous source identity, omitted/duplicate field or declaration joins, mismatched paired tree shapes, repeated association/searches or cloned receiver subtrees. A rev2 verification failure or expansion beyond the exact mapping/test lines above closes unfinished. No language-semantic choice or production permission follows.

On success and independent review, close only this bounded source correspondence prerequisite. Record closeout at `notes/progress/2026-10-19-r77-closeout.md`. Parent/evaluator/A-B stay OPEN 0→0; R50 NOT_ADOPTED.
