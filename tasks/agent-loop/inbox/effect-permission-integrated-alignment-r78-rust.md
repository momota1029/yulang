# R78 Rust source lane handoff

Sprint: `EFFECT-PERMISSION-INTEGRATED-ALIGNMENT/20261031-R78`, contract revision 1
Contract SHA-256: `42455496150e76635d364fb72d20142583d30ac0cedec239d17520609be95148`
Assignment: R78-RUST, handoff revision 1
Parent: integrated source alignment from complete source call inventory through `internal_root_view_from`
Baseline: `68976bad8d44fd5586ac9b06ee2389743bfa4c8f`; dependency manifest `tasks/agent-loop/sprints/effect-permission-integrated-alignment-20261031-r78-inputs-r1.json`
Role / worker: Rust implementation lane / `/root/r78_rust`
Session and launch receipt: active worker context; runtime receipt details unavailable here
Requested model and effort: Luna/high (assignment contract)
Observed model and effort: UNKNOWN in this worker context
Exact leases: `crates/yu-solver/src/candidate_receiver.rs`; this handoff only
Outcome class: implementation candidate with an OPEN source identity bridge

## Changed consumer path

`InventoryPackage::capture` still retains every `source.calls` row and checks its owner-local expression index, Apply occurrence/checking coordinate, HIR occurrence ownership, local source root, Apply callee/argument indices, and cause/checking relation. It now stores the borrowed Apply expression and derives an optional alignment by peeling supported Group wrappers from that call's callee. Only a peeled module-definition Name receives an alignment; unrelated and non-module calls remain in `source_calls` with no alignment.

The capture selector now selects by owner-local Name occurrence and exact HIR target identity instead of comparing the Apply occurrence with `DefinitionUse::occurrence()`. `internal_root_view_from` separately checks the selected call index and input pointer, owner, expression index, Apply occurrence/checking/expression coordinates, and alignment Name occurrence against the request/use. It also checks the alignment target against the retained use target, while retaining all existing fact, permission, parameter, relation, ancestry, root, and failure checks.

This is not yet a complete source/native correspondence result. The two consumers reuse the same retained alignment object, and pointer/index/owner links are checked. However, the pinned source path exposes a target-key mismatch described below, so the target join is not established as type-correct evidence.

## Source evidence and blocking bridge

The exact existing HIR constructor is `yu_hir::shadow::LocalSourceResolution::ModuleDef(DefId)` in `crates/yu-hir/src/module/local_source.rs` (R78 pin `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`). The receiving source's `DefinitionUse::target()` is the solver-branded `DefinitionOrderId` in `crates/yu-solver/src/lib.rs` (pin `15e7b131a65f8476eec575d978dc629d15d49e72149325ef35a8c08acc8fc745`). These types have no cross-type `PartialEq` implementation in the pinned owner paths. The only existing conversion in `lib.rs` is a temporary borrowed `DefId -> DefinitionOrderId` map during collection; it is not retained or exposed to this consumer. `CollectedDefinition` also has no root accessor available here.

R77's `internal_owner_choice` at `candidate_receiver.rs` around line 2430 directly compares the `ModuleDef(DefId)` payload to the solver `DefinitionUse::target()` key. R77's handoff (`effect-permission-source-alignment-r77-rust.md`, SHA-256 `e3f7944c322ac2c909c97d95f0df3e814dea670c2e9c7a9d718f3061fb0eab68`) states the intended exact target join, but does not name a bridge; its independent review is bounded source review, not compilation evidence. I did not alter that helper or invent a comparison/coercion. The analogous R78 alignment-to-use comparisons therefore remain an explicit type-level blocker pending the source owner’s exact retained bridge or a Luna-approved owner-path change.

R78 source owner TODO: expose/reuse the exact existing HIR `DefId` to native `DefinitionOrderId` identity mapping at the owning collection boundary, or identify an already retained equivalent proof. Inputs: source call HIR Name resolution, exact `DefinitionUse::target`, and candidate definition records. Output: one checked borrowed correspondence reused by capture and root view. Falsifier: two distinct HIR definitions map to the same retained native key, or a Name resolving to a different HIR definition passes the join.

## Pins, checks, and boundaries

All R78 direct dependency pins in `inputs-r1` still match: `candidate_source.rs` `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`; `lib.rs` `15e7b131a65f8476eec575d978dc629d15d49e72149325ef35a8c08acc8fc745`; local-source owner `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`; R77 Lean/source/review inputs and toolchain also match their manifest hashes.

`git diff --check -- crates/yu-solver/src/candidate_receiver.rs`: passed. No compiler, Cargo, test, build, formatter, Lake, cache, target, scratch, environment, or worktree command was run. No generated/scratch paths were created. No execution result or theorem closure is claimed.

The code delta is limited to `candidate_receiver.rs`: one optional per-call alignment carrier, its capture construction and selector use, and distinct root-view coordinate checks. It preserves the full call inventory and all existing downstream guards. The parent/source/native correspondence and compiler/runtime behavior remain OPEN; the source/native target mapping above blocks treating this as a completed integration.

## Frozen artifact and stop receipt

Artifact SHA-256: `5e99035a94e1d3f618e03e932e59933fb3d5eb9f501455779bcb52e65e7c7a3a`.
Handoff ID/revision: `R78-RUST` / 1.
Worker state: STOPPED writing after this submission; no descendants, scratch files, or generated outputs.
Next related step inside the envelope: Luna adjudicates the exact DefId/DefinitionOrderId bridge; do not accept these target checks as established until that mapping is evidenced. The independent reviewer must inspect the frozen source bytes and target bridge separately.
Resource budget: the 900-second assignment cap was not exceeded; exact active seconds unavailable in this worker context.
