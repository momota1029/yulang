# EFFECT-PERMISSION-LAMBDA-INCIDENCE / R41 outcome

Status: CLOSED_BOUNDED_PASS. Parent permission-transport theorem remains OPEN.

## Original outcome

R41 retained computation-formal registration labels through construction of the positive Function's argument-effect child, graph capture and one exact FreshUse row map. The scope did not include provider arrival, Catch selection/residual, subtraction, whole-source hygiene, whole-language safety or production promotion.

## Before / after

Before R41, R40's reviewed READ2 showed that the existing FreshUse code reconstructed Function child 1 and exact module-use routing but did not retain the original computation-formal registration to captured-child association.

After R41, passive constructor metadata records each computation registration, Lambda occurrence, positive Function, child ordinal, actual captured child node and graph-row coordinate. FreshUse checks the same child-node coordinate and maps the row through its ordered row vector while retaining each registration label even when images coincide. It does not add a permission consumer or propagation edge.

Revision 1 independent review found and blocked on a conflated child ordinal/node index and invalid `let-else` initializer. Luna repaired both within the leased `candidate_scheme.rs` owner. Revision 2 independent review passed: it traced a non-node-1 child `(index 1, node 7, graph row 5)` through `rows[5]` and `terms[7]`, checked syntax, and reconstructed the pinned dirty baseline in memory exactly.

## Proof and review

Lean 4.35.0 stdin-only audit accepted all nine theorem declarations in `LambdaArgumentEffectIncidenceR41.lean`; independent review checked complete `#check @` and `#print axioms` output. Axioms: `propext` for `function_child_one`, `lambda_origin`, `capture_preserves`, `freshuse_exact`, `conditional_shared_tail_falsifier`; none for `distinct_registration_images` and `shared_row_distinct_labels`; `propext`, `Quot.sound` for `entry_to_exact_use` and `empty_entry_incidence`. No `sorryAx` or project axiom.

Review receipt: `tasks/agent-loop/inbox/effect-permission-lambda-incidence-r41-review.md`, current SHA-256 `33808a855db179bb7c51cb65f9703a556d05b2dd0445de0b20440ba880d50056`.

## Frozen artifacts

- Rust `lib.rs`: `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce`
- Rust `candidate_context.rs`: `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38`
- Rust `candidate_scheme.rs`: `3cd9dd2d0f55412636dc88bc658d7cfbc23aad6304b90f2ba95247f8d58e1d22`
- Lean module: `af7c2e3def8762287e95827896dc01d982954059bff09c476d1a94df94c0a79e`
- Rust handoff: `484fdb19c8850c4a64af5a2bea2d80453722f1f9969a318ab69ef70e182c9829`
- Proof handoff: `1f33b18d0e60d3f244ccf2843cd7a1e0acd6ef6e1bd3a24727fdcb88a12fac84`

The source file still contains pre-existing dirty tracing changes. R41 was staged as isolated hunks only; the reviewer verified that removing only R41 additions reproduces dirty baseline `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` exactly. Those pre-existing bytes remain outside the commit.

## Git and resource evidence

Reviewed R41 checkpoint: `d2a58b791a1a1823f5cea5663d74d572e768be13`, pushed to `origin/yulang3`. State receipts were committed and pushed in `8375c7092df2e311150e8188beb4302bfa59f0c6`, `e7e5c7488` and `e7729cd06d60892d4803685924bd9d28a74301c4`. Final verified HEAD and `origin/yulang3` were both `e7729cd06d60892d4803685924bd9d28a74301c4` before R42 admission.

No builds, tests, Cargo or Lake runs were performed. No new environment, worktree, target, cache or scratch output was created. The three extra sibling worktrees previously removed remain absent; only the main checkout is listed. The filesystem reported 730G available (24% used); Linux block deletion does not by itself compact a Windows WSL VHDX host file.

## Remaining premises

`R41-NATIVE-INCIDENCE-REALIZATION-1` remains OPEN: the finite model is not a verified Rust interpreter, and a successful actual Rust field-by-field native-term extraction has not been retained. Provider arrival, Catch/residual subtraction, original Simple-sub A/B, whole-language hygiene and production promotion also remain OPEN. The conditional shared-tail witness is not an observed compiler defect.

## Checkpoint

The coherent eight-path R41 checkpoint was committed as `research: retain lambda argument-effect incidence`; all intended R41 source hunks and proof/review artifacts were pushed. The unrelated dirty workspace was not staged. Only primary performed Git operations.
