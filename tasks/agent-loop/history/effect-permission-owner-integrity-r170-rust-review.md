# R170 frozen Rust compiler review

Reviewer: `/root/r103_rust_referee`, independent of the writer.
Disposition: source review PASS; complete against-HEAD diff and whitespace-check evidence not independently certified under the no-Git review boundary.

## Frozen bytes

- `crates/yu-solver/src/candidate_scheme.rs`: SHA-256 `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e`.
- `crates/yu-solver/src/candidate_receiver.rs`: SHA-256 `5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade`.
- `tasks/agent-loop/inbox/effect-permission-owner-integrity-r170-rust.md`: SHA-256 `dcb6120642cb5dc6524ed38f3e41cc29cefd04a9916b62ff7601adbedc584dca`.

All three hashes were computed from the frozen files and match the source hashes declared in the handoff. The handoff's own hash above identifies the exact explanation reviewed; the explanation is not correctness evidence.

## Findings and source evidence

No BLOCKING, major, or minor compiler-correctness finding in the inspected repair.

- `candidate_scheme.rs:505-589` now obtains the selected route, term arena, registration, context origin, Lambda recipe, source expression, and effect state from one `InferenceSession`. A caller cannot combine a route/store from one session with permissions from another through this API. The added provider/registration-owner comparison uses the resolved definition identity, not spelling.
- The binder independently checks the unique registration-qualified origin and Lambda occurrence, raw negative Effect argument row, unique recipe, exact source Lambda parameter, current captured/raw representative equality, and mapped native negative Effect row. Raw source, captured representative, and FreshUse image remain distinct. The earlier split-input adapter's tautological route-field comparisons are not used as substitutes for those joins.
- `candidate_receiver.rs:1870-1898` searches by the explicit permission registration label and rejects duplicates. The dense permission inventory index is compared only with the Catch-held permission index, not with a formal registration ordinal. This restores the sparse-table invariant.
- `candidate_receiver.rs:225-238`, `:604-620`, `:4866-4878`, and `:5138-5177` retain and rejoin provider view/member/family, selected operation/arm, permission object/member, source owner/occurrence/annotation row, and Catch evidence. Index equality is accompanied by borrowed-object and resolved-identity checks.
- The previously reviewed duplicate-guard removal remains safe: native owner identity is checked in the following condition, and the private owner-derived projection constructors retain that owner's immutable batch/context. No source restriction, new permission, constraint mutation, or consumer is introduced by this repair.

## Evidence limits and integration recommendation

The earlier independent review in this same reviewer context inspected HEAD's session-owned binder and the complete two-file dirty diff. The frozen repair was compared with those independently obtained source excerpts and the current scoped source. This turn did not access Git, so it did not freshly establish the complete current against-HEAD diff. The writer reports a scoped `git diff --check` pass; that report is author-supplied evidence, not an independently observed check receipt. The handoff's statement about a receiver difference relative to HEAD and an already committed guard deletion does not itself establish the current diff.

The ownership repair is suitable for primary integration review. Before staging/pushing, the primary must independently establish the exact intended against-HEAD scope and scoped diff-check result. This review alone does not certify an outbound range, compile/test success, a connected consumer, or any parent theorem/source-native/production gate.

## STOPPED receipt

Inspection was limited to the two assigned Rust files and assigned handoff. The only write was this explicitly requested review receipt. No compiler/source edit, test, build, Cargo, Git operation, scratch/cache creation, unrelated/quarantined-path inspection, or R169 inspection occurred. No descendants were spawned. Reviewer STOPPED.
