# R74 — store-owned admitted HIR selection

Status: CANDIDATE until Luna freezes the input manifest and grants exact leases.
Sprint ID: `EFFECT-PERMISSION-STORE-HIR-LOOKUP/20261031-R74`
Branch / baseline: `yulang3`; pushed baseline `21cf99c051dbca3450ef184396e43a01f8dae323`.
Authority: continuing `research/simple-sub-intrusion` goal; repair only the R73 independently reviewed blocking Rust source defect. No semantic or production authority changes.
Contract revision 1. SHA-256 recorded in the R74 manifest and admission.

## Original outcome and success evidence

Parent: effect-permission owner-exact completed-instance bridge under the original R66 A/B and source domain. R73's finite Lean result remains accepted within its explicitly stated conditional model; this sprint does not alter R73 Lean or claim parent closure.

Blocking R73 finding: `candidate_receiver.rs:1058` and `:1573` call `hir_for_occurrence` on `ConstraintStore`, which does not define that method. The method exists on `FrozenInferenceData` and `InferenceSession`; source inspection confirms Rust method-resolution failure with `shadow-apply-candidate`.

Fixed outcome: implement the selected-artifact lookup at the `ConstraintStore` owner and route both receiver call sites through that accessor. It returns `Option<(usize, &Arc<HirModule>)>` from this exact store's `hirs` inventory. Try `occurrence_hir_positions`, validate the indexed artifact by full `owns_occurrence`, then fall back to the first matching artifact in the same inventory. Leave `require_owned` behavior unchanged. Store and validate the returned artifact index directly; do not derive it by an unrelated scan or switch to an `InferenceSession` lookup.

Success evidence: frozen source exposes the method on `ConstraintStore`; both call sites have type-correct receivers and retain the exact index/borrowed artifact; source-level path trace covers indexed success, invalid/missing-index fallback, foreign artifact rejection, and equal local ordinals from different artifact brands. Independent delta review finds no blocking/major issue and no changed semantics. Rust compilation/runtime remain unverified; source inspection must not be reported as compiler success.

Non-goals: no Lean source change or new Lean execution; no change to inference, constraints, propagation, routing, execution, or `require_owned`; no repair to physical pointer/slice/map modeling; no Root construction, A/B closure, or production promotion.

## Two continuing lanes

**Rust implementation — Luna/high, 450 seconds:** one writer owns only `crates/yu-solver/src/lib.rs` (new store-owned accessor), `crates/yu-solver/src/candidate_receiver.rs` (two call sites and necessary coordinate checks), and `tasks/agent-loop/inbox/effect-permission-store-hir-lookup-r74-rust.md`. Preserve exact R73 input bytes before editing. No adjacent cleanup.

**Source/proof correspondence — Sol, 450 seconds:** read-only source audit; exact output `tasks/agent-loop/inbox/effect-permission-store-hir-lookup-r74-proof.md`. Trace the returned inventory coordinate and artifact through R73's `Readbacks`, `requireOwned`, and `decodeOwner` obligations. Confirm full artifact identity and fallback semantics. Do not edit Lean or run Lean.

**Independent reviewer — compiler_referee / Sol-medium, 750 seconds:** after both authors stop, exact output `tasks/agent-loop/inbox/effect-permission-store-hir-lookup-r74-review.md`. Review frozen changed source and both handoffs. Check receiver/type ownership, same-store inventory, indexed path, invalid-index and missing-index fallback, full artifact equality, foreign-session rejection, coordinate retention, unchanged `require_owned`, and exact diff. Fresh reviewer only.

## Permissions and resources

Fresh envelope: Rust 450; source/proof correspondence 450; independent review 750; primary 750 including at least 500 closeout; Astra 0. Same checkout and existing disk only. No new environment/worktree, dependency/config changes, cache, target, or scratch. No Lean/Lake/Cargo/build/test/formatter/compiler command. Maximum probes: zero. Static source inspection and `git diff --check` only.

Luna grants only the exact paths above. Any need to change another source file, alter semantics, exceed a lane budget, use a compiler/build/test, or repair broader owner correspondence returns to Luna and requires a new decision/contract. Preserve 32 pending items, unrelated UNKNOWN/quarantines, R24 capacity override, and R72 attempt-1 UNKNOWN/unrefunded time.

## Frozen seam and stop conditions

Inputs and baseline are pinned in `effect-permission-store-hir-lookup-20261031-r74-inputs.json`. The receiver and Lean artifact are R73 frozen outputs; the receiver's baseline Git blob is separately recorded. R73 is closed `CLOSED_INCOMPLETE_FIXED_GATE_REJECTED` and is not reopened. Do not overlap the new Rust writer with proof/review. The reviewer starts only after both authors return STOPPED / WRITES STOPPED. Stop on missing owner evidence, counterexample, unleased path, or resource boundary.

This packet closes only the source-level owner lookup defect. Native compilation/runtime, actual Rust-to-Lean identity extraction, pointer/slice/map and allocator correspondence, genuine R66 `Root`, original A/B, whole-language hygiene/soundness/principality/termination and production remain OPEN.
