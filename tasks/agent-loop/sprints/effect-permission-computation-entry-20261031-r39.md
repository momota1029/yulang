# R39 — retain computation-formal permission at its source entry

Status: ADMITTED revision 1 by Luna.  
Sprint ID: `EFFECT-PERMISSION-COMPUTATION-ENTRY/20261031-R39`  
Branch / baseline: `yulang3` / `06f1ce59eac7a953af18f27558ad0dd8b2a97237`  
Authority: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.1–1.2; `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5; unchanged original Yulang soundness/Call obligations.  
Input manifest: `tasks/agent-loop/sprints/effect-permission-computation-entry-20261031-r39-inputs-r1.json`.

## Parent outcome and bounded success

Continue the original effect-hygiene/soundness goal without narrowing its source domain or quantifiers. Advance the first R38 source gap for the admitted outer computation formal `[E] int`: retain a source-authenticated concrete permission witness at the actual `FormalEntry` owner.

A successful implementation retains the complete concrete annotation row, in source order and with multiplicity, tied to the actual formal registration, source owner, Lambda/action occurrence, annotation scope/position, and computation-entry port. It leaves the existing entry inflow open and preserves symbolic-row equality. A permission record alone adds no inflow and performs no subtraction. The callback/nested Function path remains behaviorally unchanged.

Success evidence is a reviewed source delta whose construction is derived from exact admitted inputs; a Lean model with complete theorem types and axiom audits establishing exact row retention, owner/registration rejection, no inflow injection, and preservation of the existing symbolic link; and an independent review of the source-to-model correspondence. If source identities or a coherent safe update cannot be established, stop with the first missing transition and keep the lane OPEN.

## Source gate and exact owners

The pinned R38 finding is that `candidate_source` schedules `FormalEntry` and `FormalAnnotation` for `[E] int`; `candidate_formal_entry_annotation` connects only an optional symbolic outer row, and `candidate_formal_annotation` reaches root `Int`, not a nested Function port. No concrete computation-permission witness is retained. R39 starts at that constructor and ends when the witness is retained in the private candidate state.

Rust owner: `candidate_formal_entry_annotation` and its current owner-local state/accounting in `crates/yu-solver/src/candidate_effect.rs`. Only that file and the Rust handoff below are writable by the implementer. Keep the exact pre-admission dirty bytes as the immutable base; preserve every pre-existing diff and do not claim or stage it. Do not edit `candidate_source.rs`, `candidate_call.rs`, `candidate_receiver.rs`, `candidate_scheme.rs`, or `shadow_apply.rs`.

Proof owner: new standalone module `notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean`, importing only pinned `Std`, and its proof handoff. Define only the finite owner/registration/annotation/row data needed to model the audited constructor; derive the retained witness from those inputs. Do not assume a source-construction law or import project axioms.

## Non-goals and invariant boundaries

Do not add concrete effects to the entry inflow, impose a closed upper bound, filter residuals, connect a provider, select a Catch, or claim execution. The later witness → actual provider contribution → selected Catch/residual join remains OPEN for a later packet. Do not change approved semantics, source constructors, the effect alphabet, call behavior, or whole-language soundness claims.

The top-level inference principles do not make complete rollback a goal. Prepare and validate the new record and accounting before publishing it; on resource failure, safely terminate/discard the affected private attempt as allowed by those principles. Prove atomicity only for publication of this new retained record if needed; do not demand restoration of prior capacities or unrelated candidate state.

## Continuing lanes, review, and resources

Rust implementation: registered `implementer`, Luna/high, up to 1,600 seconds. Exact leases: `crates/yu-solver/src/candidate_effect.rs` and `tasks/agent-loop/inbox/effect-permission-computation-entry-r39-rust.md`.

Constructive proof: registered `lean_prover`, up to 1,600 seconds. Exact leases: `notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean` and `tasks/agent-loop/inbox/effect-permission-computation-entry-r39-proof.md`. Use the pinned Lean 4.35.0 read-only stdin procedure; report every theorem type and full `#print axioms` result.

Independent reviewer: fresh `compiler_referee` after both lanes freeze, up to 1,200 seconds; Luna owns `tasks/agent-loop/inbox/effect-permission-computation-entry-r39-review.md`. Check source construction, witness identity, proof/model relation, unchanged dirty base, exact semantics and open downstream gates. Authors do not review their own work.

Luna integration/closeout: 1,600 seconds including 500 seconds reserved for closeout. Total envelope 6,000 seconds; no transfer or renewal. Astra: 0. No new environment, worktree, copy, scratch file, build target/cache, Cargo, Lake, build, test or formatter. Use same checkout only. Static path-limited diff checks are allowed. User storage constraint remains binding.

## Stop conditions and checkpoint

Stop before changing behavior if registration, source row or entry-port identity cannot be tied to the actual `[E] int` source action. Preserve the existing dirty worktree and quarantined UNKNOWN leases. Freeze both handoffs; Luna synchronizes actual roster, reviews the independent verdict, updates current state and outcome, and stages only the reviewed R39-owned delta. Before every push inspect the complete outbound range and push non-forced only when coherent.

Original source-wide permission/subtraction hygiene, actual provider arrival, Catch residual behavior, Simple-sub A/B, whole-language inference soundness/principality/progress/termination and production remain OPEN. Next consultation trigger: R39 material obstruction, integration seam, review adjudication, sprint close, or new source evidence—not each lemma.

## Revision 1 — source-owned Lambda identity correction

The first independent review found that `FormalRegistrationInput.lambda` indexes the owning `LocalSource.expressions()` collection. It must never index `candidate_source.expressions`, which stores only expression-root schedules. `candidate_formal_entry_annotation` must retrieve the HIR for `registered.owner`, resolve that owner's LocalSource, index its expressions by `registered.lambda`, require a Lambda whose parameter identity equals `registered.parameter`, and compare that Lambda occurrence with the current FormalAnnotation action occurrence. Preserve all other admission conditions. The Lean model must represent this owner-local lookup and derived Lambda identity instead of assuming the schedule-array lookup. The reviewer supplied a definition-backed counterexample; preserve the original proof/source revision and its bounded claims as history.
