# Sprint EFFECT-PERMISSION-RESIDUAL-JOIN/20261031-R38 — authenticate permission at the selected residual

Status: CANDIDATE until Luna's live admission receipt and current-state update.
Branch / baseline: `yulang3` / `c6e37750f8b454da95afe0f712710e38b4c94b85`.
Authority: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2, 3–4; user-approved permission/inflow/subtraction clarification.
Contract revision: 1. Primary: Luna.

## Original outcome and success evidence

Parent obligation: for the unchanged annotation-permission semantics, a declared effect permission alone contributes nothing to an outward residual; a selected Catch removes only an actually arriving, matching operation contribution at that boundary; every unmatched contribution remains, including the same family arriving from another boundary; empty inflow stays empty. Permission, inflow and residual are distinct. The original source domain and quantifiers remain those of the governing decision; this packet covers only the existing bounded private receiving experiment and does not close source-to-runtime or whole-language soundness.

Accepted semantics: §1.2 of the authority above. No closed upper-bound reinterpretation, family-only authorization, supplied eligibility Boolean, or partial result when symbolic/unavailable evidence remains.

Implementation goal: connect the source formal/annotation action and retained `FormalPermission` to the exact provider contribution, selected Catch arm and residual edge in `candidate_receiver.rs`, then consume only the authenticated join in the bounded experiment. If identities cannot be authenticated from the permitted owners, stop source edits and report `NO_SAFE_CODE_SLICE` with the first missing transition.

Success predicates: (1) exact identity join is constructed from retained source and graph evidence, or a source-grounded `NO_SAFE_CODE_SLICE` names the first missing transition; (2) a Lean development states and proves guard soundness, empty-inflow preservation, unmatched-contribution preservation (including same-family/different-boundary), and forwarding/subtraction correspondence for the bounded fold, with complete theorem types and axiom audits; (3) fresh independent review passes the frozen Rust/Lean correspondence. No Rust compile, test, runtime, whole-language or production claim is implied.

Falsifier: suppression succeeds through another formal or boundary, through equal-family unrelated provenance, or from annotation permission without an actual lower contribution; or forwarding loses an unmatched/symbolic contribution. On any such case, preserve the counterexample and keep the dependent gate open.

Open parent premises: source `FormalPermission` to arriving provider contribution (candidate_effect/candidate_call/candidate_source owners); selected arm to exact residual lower/upper edge (candidate_receiver/candidate_source owners); native/runtime consumption (excluded/quarantined owners); original A/B and whole-language proof (Luna). A missing authenticated transition blocks only this bounded implementation join.

Non-goals: no changes to ordinary compiler behavior, semantics, provisional effect/scheme/shadow-apply bytes, `machine.rs`, `receiving.rs`, tests, runtime, exports, production cutover or original A/B claims.

## Two continuing lanes

Rust owner: Luna/high implementer. Exact source lease: `crates/yu-solver/src/candidate_receiver.rs`. Handoff: `tasks/agent-loop/inbox/effect-permission-residual-join-r38-rust.md`. Inspect the permitted source owners before editing; stop with `NO_SAFE_CODE_SLICE` if the exact join cannot be authenticated. Keep unavailable evidence from producing partial subtraction. Preserve unrelated operands and symbolic tails.

Proof owner: constructive `prover` on Sol/high. Exact outputs: `notes/theory/lean/YulangClosure/EffectPermissionResidualR38.lean` and `tasks/agent-loop/inbox/effect-permission-residual-join-r38-proof.md`. Prove the four success predicates against the unchanged finite source/graph model; apply each result to the source correspondence seam. Use pinned Lean 4.35.0 via stdin under read-only `bwrap`; capture all complete theorem types, axiom sets and diagnostics. No `sorryAx`, project axioms, native evaluation or checker bypass.

Independent fresh reviewer: `tasks/agent-loop/inbox/effect-permission-residual-join-r38-review.md`; review exact source identities, residual refinement, proof types/axioms, dependency hashes and unchanged source envelope. No producer or coauthor may self-review.

Continuation within this contract: Rust may complete the identity trace and bounded join or freeze the exact first missing transition. Proof may construct and audit all related lemmas and their bounded consumer correspondence. Any new source owner, semantic choice, lease, production path or dependency outside the pinned inputs returns to Luna before use.

## Permissions and resources

Exact Rust write lease: `crates/yu-solver/src/candidate_receiver.rs`; Rust handoff above. Exact proof write leases: Lean module and proof handoff above. Exact reviewer write lease: review handoff above. Primary-only paths: this contract, its `-inputs-r1.json`, R38 admission, stage ledger, outcome and `current.json`. No other writes.

Permitted source reads: pinned `candidate_receiver.rs`, `candidate_effect.rs`, `candidate_call.rs`, `candidate_source.rs`; the authority document above and `notes/design/INDEX.md`; R35 `SourceCallbackPermissionR35.lean`, R36 `SourceCallbackUseR36.lean` and its final review; R37 `SourceUseInventoryR37.lean` and its final review; the pinned Lean toolchain file. Read only exact declarations/sections needed. `tools/inference-playground/src/runtime/machine.rs` and `receiving.rs` remain excluded from reads and writes; do not search them. All other unlisted files are excluded.

Immutable baseline/dependency hashes are recorded in `effect-permission-residual-join-20261031-r38-inputs-r1.json`. Pin R37 code/review and the four solver source owners before dispatch.

Resources: total 6,000 seconds: Rust 1,600; Lean 1,600; independent review 1,200; Luna primary/integration 1,600 (includes 500 closeout); Astra 0. No transfers or renewal. Missing actual runtime/model/effort is UNKNOWN. No more than four assignments including Luna; reserve review/integration capacity.

Stop conditions: `NO_SAFE_CODE_SLICE`; exact counterexample; budget exhaustion; required authority or dependency change; user STOP; inability to keep current state within 16 KiB. Unknown writers keep their path quarantined. No new worktree, checkout, copy, environment, build, Cargo, test, Lake, formatter, target, cache, extraction file or scratch. The only verification command is the static `python3 tools/agent_sprint.py check` after state synchronization; Lean proof audit follows the pinned stdin exception above.

## Frozen seams and handoff

Review target is frozen Rust plus Lean and handoffs with exact byte hashes. Review PASS requires independent reconstruction of all four identities and all preserving/rejecting cases, complete theorem types/axioms, no prohibited source access, and no finding that changes behavior outside the bounded experiment.

Proof application: a proved bounded fold transfers only to the exact authenticated identity join. It does not establish invocation, runtime consumption, Grant/Catch propagation, original A/B, whole-language hygiene, soundness, principality, progress, termination or production readiness.

Checkpoint only after review and Luna adjudication. Stage explicit R38 paths only; inspect the complete outbound range; push coherent non-forced range to `origin/yulang3`. Keep all 32 pending items, UNKNOWN workers and quarantined leases unchanged. Archive resolved R37 scheduling entries only after verifying existing immutable outcome/stage-ledger hashes.
