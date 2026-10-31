# Sprint R72 — construct and replay the completed native instance

Status: CANDIDATE pending pinned-input verification and Luna admission
Sprint ID: `EFFECT-PERMISSION-COMPLETED-INSTANCE/20261031-R72`
Branch / baseline: `yulang3` / `ce5842b0823e6febcc64b496c18e71d4438ad915`
Authority: active user goal for Rust implementation, Lean proofs, effect hygiene and soundness; 2026-10-16 goal-driven sprint decision
Contract revision: 1

## Original outcome and success evidence

The parent goal remains Yulang inference/executor soundness, effects, principality and termination. Preserve the original Simple-sub A/B claims, quantifiers, source domain, R66 Root and approved effect-permission semantics. This sprint advances the effect-hygiene consumer by connecting R71's successful-return refinement to the exact owner-borrowed Rust result. It does not close the parent theorem or authorize production promotion.

The precise gap is that R71's Lean `Package` is mathematically checked but is not yet built from the actual `InventoryCompletedReificationView`. R72 must make progress on that exact source/native seam.

### Fixed outcome

1. In `candidate_receiver.rs`, add one private, fallible, owner-scoped primitive projection constructed solely from `InventoryCompletedReificationView`. Reuse its existing encoded identity tables and completed rows; do not serialize them, clone whole project inventories, or independently reconstruct facts from a second source. Keep the owner borrow and table/resource boundaries visible.
2. Preserve the complete identity namespaces and coordinates: branded Term and ComponentId identity through their existing distinct tables; every indexed fact with identity and all four raw/canonical endpoints; every provenance edge, occurrence, owner and original index; exact current Value/Effect representative tables and complete competitor lists used by the reader.
3. In `CompletedNativeInstanceR72.lean`, decode the primitive projection by executable finite checks into a constructed R71 `Package`. Do not accept a supplied Package, `completed`/`Valid`/success flag, assumed faithfulness/correspondence predicate, or a premise that merely states the desired decode equations. Rejected foreign owners, bad coordinates, omitted or reordered rows, changed endpoints or representatives must fail explicitly.
4. Prove that each accepted decoded Package runs R71's actual modeled `reify` branch successfully and returns the exact ordered projected records. Apply R71's R67/R65 qualified-read equations to the same R66 slot-0 and slot-2 witnesses, retaining the original Root, source/native/request, use and lambda-coordinate premises unchanged.
5. Fresh independent review traces every Lean Package field to the concrete Rust owner and checks the attack cases above before Luna adjudicates and checkpoints.

This establishes a checked finite projection/replay bridge at the source boundary. Source correspondence review and a mathematical replay theorem do not establish compiled Rust execution, runtime behavior or allocator equivalence; those remain separately OPEN.

### Falsifiers

- A foreign owner or same local ordinal from another Term/ComponentId namespace decodes as the owner in the completed view.
- A source fact, endpoint, provenance occurrence, edge, original index, current representative, competitor or ordering can be changed/omitted while decode and replay still succeed.
- A successful projection publishes partial local vectors or erases `SearchLimit` into `BoundMismatch`/success.
- Lean accepts a supplied R71 Package, success equation or blanket faithfulness law instead of constructing and checking it from primitive rows.
- A returned R71 row or qualified read differs from the exact projected row/selected owner-qualified fact.

## Two continuing lanes

### Rust owner projection — Luna/high

Owner: `/root/r72_rust`

Exact write leases:

- `crates/yu-solver/src/candidate_receiver.rs`
- `tasks/agent-loop/inbox/effect-permission-completed-instance-r72-rust.md`

Inspect `InventoryCompletedReificationView`, its owner, `EncodedInventoryEndpointObservations`, current representative tables, and the existing semantic/provenance owners. Implement only the bounded projection and checks above. Retain borrow identity and the exact `SearchLimit` / `BoundMismatch` split. No inference, permission-consumption, propagation or execution semantics change.

### Constructive Lean projection and replay — Sol/high

Owner: `/root/r72_proof`

Exact write leases:

- `notes/theory/lean/YulangClosure/CompletedNativeInstanceR72.lean`
- `tasks/agent-loop/inbox/effect-permission-completed-instance-r72-proof.md`

Build the Package from checked primitive tables; prove coordinate/namespace decoding, all-field and order preservation, finite acceptance implies R71 successful replay, and same-witness qualified-read application. Use the pinned Lean 4.35.0 `-j1 -M1024 --stdin` audit. Do not use an assumed bridge or broaden R71's premises. Retain full theorem types and transitive axiom reports. R71's R66 Root remains a genuine premise.

### Independent review — fresh Sol/medium

Owner: `/root/r72_review`; start only after both authors report STOPPED / WRITES STOPPED.

Exact write lease: `tasks/agent-loop/inbox/effect-permission-completed-instance-r72-review.md`.

The reviewer inspects the Rust owner and Lean artifact before handoffs, traces every Package field to the actual completed view, attacks foreign identity/coordinate/order/endpoint/representative/competitor cases, checks failure distinctions, hashes, full theorem types and axiom audits, and confirms same-R66-witness application. No build, test, formatter, Lake, Lean rerun, scratch, cache, worktree, environment, author contact or source write.

## Dependencies, permissions and resources

Baseline is pushed HEAD `ce5842b0823e6febcc64b496c18e71d4438ad915`. The R72 inputs manifest pins the R71 contract and all reused R69-R71 definitions/dependencies, plus the current R71 Rust receiver, Lean module, handoffs, independent review, outcome and authenticated state archive. Verify every hash before launch; stop if any pin differs.

Use the existing checkout only. No additional checkout, worktree, environment, dependency/configuration change, build, Cargo, test, formatter, Lake, cache, target or scratch output. Read-only source inspection and bounded in-memory Lean stdin audits only. No post-session work.

Fresh bounded envelope: 6,000 seconds total: Rust 1,400; proof 2,200; independent review 1,200; primary 1,200 including at least 500 seconds closeout; Astra 0. Review remains a reserved slot. At most two substantive author assignments. Respect the global 6 active/reserved/unknown assignment ceiling and existing 13-slot user-authorized capacity release; do not apply it again or count its identities twice. The remaining un-released UNKNOWN assignment and all UNKNOWN worker observations/quarantined paths remain unavailable and unchanged. The root synchronizes its live session truthfully. Preserve all 32 pending items. No path lease is released by capacity accounting.

Bound resource accounting; no more than four lightweight single-process probes, one active Lean process, 1 CPU and 1 GiB per probe, each at most 120 seconds unless the pinned audit contract specifies the single audited Lean invocation. The proof lane owns Lean processes and records peak RSS/runtime. Do not raise `-M1024` after a failure; retain exact failed receipt and adapt only within the contract.

Stop at a missing retained constructor input, a required additional owner/lease, a material semantic decision, a proved falsifier, a genuine budget/no-progress bound, or user STOP. Keep native resource/runtime equivalence, actual R66 source Root construction, original A/B, whole-language effect hygiene/soundness/principality/termination and production OPEN.

## Frozen seam and integration

Authors own only their exact paths. They do not stage, commit, push, contact each other or create descendants. Freeze exact artifact and handoff hashes before review. Reviewer owns only the review handoff. Luna alone adjudicates and stages exact intended paths, updates current/archive/outcome, checks the complete outbound range and performs non-forced commits/pushes.

The next continuation remains inside the user's active Rust/Lean soundness-and-effects goal. Consult the dispatcher at the next sprint end, material counterexample/blocker, authority/dependency/lease/resource change or integration seam, not after each lemma or routine result.
