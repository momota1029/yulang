# R71 contract — successful Rust reification to Lean success evidence

Status: admitted bounded research only. Parent objective remains OPEN.

## Objective and fixed outcome

Starting from the pushed R70 checkpoint, refine the successful return of the actual owner-borrowed `InventoryPackage::reify_qualified_facts` path into Lean evidence. Show that a completed source-aligned return entails the R70 finite observation construction and endpoint decoding results, preserves complete ordered fact/provenance rows and per-fact endpoints, and commutes with the existing R67/R65 qualified readers. Apply the result to the same original R66 slot-0/slot-2 witnesses while retaining every genuine Root/use/lambda premise.

The return-value evidence must follow the existing successful branch structure. Do not rename `Valid`, `construct = some`, or `decodeRows = some` as an assumption, and do not claim a theorem about compiled Rust execution without an actual bridge. Successful-call refinement is the target; universal decoder totality is out of scope because admission checks do not establish every decoder polarity condition.

## Source behavior to preserve

`InventoryPackage::reify_qualified_facts` first constructs endpoint observations, then validates and appends every semantic fact, provenance occurrence, and edge in source order, returning `InventoryQualifiedReification` only after the entire path succeeds. Checked reservations and coordinate conversions preserve `SearchLimit`; malformed/stale rows and lookup mismatches preserve `BoundMismatch`. `internal_root_view` consumes that completed result and keeps reification failures distinct from later root-structure mismatch.

A source-aligned view may expose the completed reification only after the existing method returns `Ok`. It must retain borrowed owner identity, full ordered inventories, the already-produced encoded observations, and exact raw/canonical endpoint results. It must not publish partial vectors on error. Do not change inference, propagation, permission consumption, or execution behavior.

## Constructive Lean obligations

Create `YulangClosure.SuccessfulReificationDecodeR71` and prove from the modeled successful return branch, without assumed faithfulness or success flags:

1. Successful return entails R70's checked finite construction and exact endpoint decode equations.
2. The decoded fact sequence is exactly the ordered source fact sequence, including repeated identities and all four raw/canonical endpoints; provenance occurrences and edge references retain their original order and coordinates.
3. Owner-qualified lookup and complete competitor-list selection commute through R67/R65.
4. The result applies to the same original R66 Root and slot-0/slot-2 witnesses, retaining genuine root, use, lambda, exact-coordinate, construction and interpretation premises.

Failure branches stay explicit and distinguish `SearchLimit` from `BoundMismatch`. A theorem may not convert either error into semantic success.

## Falsifiers

- Any successful returned view omits/reorders a source fact, occurrence, provenance edge or nested endpoint.
- An endpoint returned by Rust differs from the corresponding R70 decoded endpoint.
- A successful partial result is observable before all checks finish.
- A `SearchLimit` path is collapsed into `BoundMismatch` or success.
- A repeated FactId or foreign owner coordinate is silently quotiented.
- The Lean proof requires assuming construction, decoding, faithfulness, or the success-return equation instead of deriving them from the modeled branch.

## Lanes and exact leases

- Rust author `/root/r71_rust`: only `crates/yu-solver/src/candidate_receiver.rs` and `tasks/agent-loop/inbox/effect-permission-successful-reification-r71-rust.md`.
- Constructive proof author `/root/r71_proof`: only `notes/theory/lean/YulangClosure/SuccessfulReificationDecodeR71.lean` and `tasks/agent-loop/inbox/effect-permission-successful-reification-r71-proof.md`.
- Independent reviewer `/root/r71_review`: only `tasks/agent-loop/inbox/effect-permission-successful-reification-r71-review.md`; start after both authors report STOPPED / WRITES STOPPED.

Authors do not stage, commit, push, contact one another, or create descendants. Primary owns integration, review assignment/adjudication, current-state synchronization, explicit staging, commits and pushes. No overlapping writers.

## Pins, verification and resources

Baseline is the pushed R70 closeout commit recorded in the R71 input manifest. Rehash all pinned source, Lean, outcome, review, archive, and R65–R70 dependencies before work. If a pin differs, stop before editing.

Fresh bounded envelope: 6,000 seconds total: Rust 1,200; proof 2,400; independent review 1,200; primary 1,200 including 500 closeout; Astra 0. Use the existing checkout and installed Lean 4.35.0 via `-j1 -M1024 --stdin`. No Rust build, Cargo, test, formatter, Lake, cache, target, scratch, worktree, environment, dependency, or configuration changes. Do not create another checkout. Preserve all 32 pending items and unrelated UNKNOWN/quarantined rows and paths.

A bounded PASS closes only this return-refinement checkpoint. Rust compilation/runtime, actual native source-instance construction and execution correspondence, native failure/resource equivalence, original A/B, whole-language hygiene/soundness/principality/termination, and production remain OPEN unless separately proved under their own gates.
