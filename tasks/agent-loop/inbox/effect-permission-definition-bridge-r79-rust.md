# R79 Rust source bridge handoff

Sprint: `EFFECT-PERMISSION-DEFINITION-BRIDGE/20261031-R79`, contract revision 1  
Contract SHA-256: `38f6b80a6466f51cc68b7c7e155313730d353357ec47ad2464680babe9656189`  
Assignment: `R79-RUST`, handoff revision 1  
Parent: checked HIR `DefId` to batch `DefinitionOrderId` bridge for R77/R78 source alignment  
Baseline: `7b9573c98cb29c594ece49f4268c887998176f76`; dependency manifest `tasks/agent-loop/sprints/effect-permission-definition-bridge-20261031-r79-inputs-r1.json`  
Role / worker: Rust implementation / `/root/r79_rust`; current session and launch receipt unavailable in worker context  
Requested model and effort: Luna/high  
Observed model and effort: UNKNOWN  
Exact leases: `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/candidate_receiver.rs`, this handoff only

## Outcome and behavior

Implemented private borrowed lookup `ConstraintBatch::definition_order_for_hir_id` over retained `hirs`, `root_definition_positions`, `root_hir_positions`, and `definitions`. It does not retain a map or add HIR/collection storage. For each exact `DefId` match in the batch HIR bindings, it checks HIR ownership of the binding root, exact root-to-definition record and HIR-position alignment, definition ordinal against vector position, collection artifact identity, and the existing definition-position index. A second exact HIR ID match fails closed. Missing or malformed matching rows fail closed. Unrelated rows are not globally rejected by a query.

R77 `internal_owner_choice` now translates the Name's `ModuleDef(DefId)` through the batch lookup before comparing it to `DefinitionUse::target()`. R78 capture stores the translated borrowed `DefinitionOrderId` in each optional Name alignment; `internal_root_view_from` continues to compare that identity against the use record. Name/use occurrence and enclosing Apply/checking occurrence remain separate. All calls remain in the source inventory, and the existing duplicate selection and downstream failure checks remain in place.

The nominal identity types remain distinct; no cast, spelling-only comparison, same-name-ordinal comparison, cross-type equality, persistent map, or HIR field was added. The bridge uses exact derived `DefId` equality only to locate an actual retained HIR binding, then validates that binding's exact branded root and batch record.

## Source and prior evidence

Reused the R78 source handoff and independent review: R78 had established the retained HIR/root/record inventories but correctly left the `DefId` / `DefinitionOrderId` join blocked. Reused the collection-time temporary `definition_by_hir_id` behavior only as prior evidence of the intended relationship; this implementation reconstructs a checked borrowed result from retained ordered records and does not preserve that temporary index.

Reviewed the R77/R78 source consumers, collection insertion and total-map checks, `HirBinding::{id, definition_root}`, `HirModule::{items, owns_definition_root}`, and the R77/R78 Lean source models. Existing duplicate definition/root insertion checks and root/definition-position queries provide related owner-path evidence. Relevant Rust tests in `lib.rs` cover definition identity/root behavior and malformed use maps, but no tests were run under the fixed R79 boundary.

The exact source-to-constraints-to-propagation-to-execution path remains experimental and outside this bridge's closure: no compiler/runtime path was executed, and this does not prove the original A/B obligations or authorize production cutover.

## Checks, exclusions, and limits

- `git diff --check -- crates/yu-solver/src/lib.rs crates/yu-solver/src/candidate_receiver.rs`: passed.
- No Rust compiler, Cargo, tests, builds, formatter, Lake, cache, target, scratch, environment, or worktree command was run; no generated or disposable paths were created.
- No owner-path or test expectation was changed. No source domain or inference semantics changed.
- Not independently reviewed. Lean/source extraction is not authenticated by this handoff. Rust compilation and runtime remain unverified.
- Resource cap: 1000 seconds. Exact active seconds are unavailable in this worker context; no known descendant assignments.

## Frozen bytes and stop receipt

`crates/yu-solver/src/lib.rs` SHA-256: `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`  
`crates/yu-solver/src/candidate_receiver.rs` SHA-256: `c570bc01cc7536a617ac3c65beab153dc71d7d0981dcfa8c01b77593385774f2`  
This handoff SHA-256: recorded in the submission receipt after this final write  

Outcome class: implementation candidate / typed identity bridge, awaiting independent review and Luna adjudication.  
Worker state: STOPPED writing after this submission; no descendants, scratch, or generated outputs.  
Next in-envelope step: independent review of the frozen Rust lookup and both consumers, including foreign batch, duplicate ID, foreign root, and wrong aligned HIR-position falsifiers. Keep Rust/native correspondence, original A/B, production and runtime gates OPEN.
