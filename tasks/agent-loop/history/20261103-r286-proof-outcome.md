# R286 producer outcome — conditional caller closure; full preservation open

Producer `/root/sol_r286_caller_closure` STOPPED / WRITES_STOPPED, no descendants. Charge the full 2,400s reservation. The Lean module and handoff are frozen pending fresh independent Sol review. The exclusive `.lake/build` lease is returned to Luna after live-roster synchronization.

## Frozen artifacts and verification

- Contract `tasks/agent-loop/sprints/extrusion-caller-closure-r286.md`, SHA-256 `3d21c214ede8a82eceac2ddea3c9e85c6e41e48a1a6565ca45545bc5be1bd068`.
- Exact 33-input producer manifest `tasks/agent-loop/sprints/extrusion-caller-closure-r286-inputs.json`, SHA-256 `d61df1fdbb3ea46e34cc680a70bd4fdc8d6f26129680cc2b0423e86077efa814`; all 33 pins matched on final recheck.
- Lean module `notes/theory/lean/YulangClosure/OriginalExtrusionCallerClosureR286.lean`, SHA-256 `06ee5e756eae0b863993af6aacef677701db91e00329cef7da44149195fb2e97`.
- Handoff `tasks/agent-loop/inbox/extrusion-caller-closure-r286.md`, revision 1, SHA-256 `2e5b54143ee5d2c5512085c6bb2de4813f21b4328b45c8d4e84266139c39ba6a`.
- Pinned Lean 4.35.0 focused Lake build and direct Lean check exited 0. Bundled checker audited all 68 declarations: 68 PASS, 0 FAIL, with complete printed types and per-theorem axioms. Axioms are limited to `propext`, `Quot.sound`, and `Classical.choice`; `internCell_preserves_caller_store_fields` reports none. Source-cone scan found no `sorry`, `admit`, project axiom, `unsafe`, or kernel-skip declaration.
- No Rust/source/Cargo/tests/probes, dependencies, root imports, Git, or scratch files were touched. CPU/RSS were not measured. Commands completed within the 2,400s bound.

## Checked conditional results

`ValueRefValid` requires both raw and qv-canonical validity for row endpoints, and a stored term for structural endpoints. `RequestValid` checks both caller endpoints. `CallerClosure` combines R285 `StorageClosed`, current caller validity and validity of both caller endpoints in every saved Parent against the current stores and qv map.

The module proves the exact computed initialization equivalence under `RequestValid`, preserves the arbitrary-caller impossibility result, and checks caller frames through allocation, physical insertion, interning, operation/local initialization, Parent retention, queue removal, partial Parent publication gates, no-selected-work finish/failure, and selected Bound, IncomingAllowance, and EffectView processing. It proves returned-state validity for the emitted Bound request and directly proves the computed three-step prefix under the explicit caller premise.

## Open universal transition obligation

The arbitrary-Funding `step_preserves_caller_closure` and arbitrary-fuel `runPrefix_preserves_caller_closure` are not delivered. The exact remaining goal after `select s = some (task, popped)` is:

```lean
CallerClosure (resultState (perform funds popped task))
```

under `CallerClosure s`. New Visit, nonempty Function rebuilding and successful Tuple/Record/Variant processing remain open, including mutation publication, `.next`/`.external`/`.failed` outcomes and partial failure. No kernel-checked falsifier was found. Proof-state diagnostics are not counterexamples.

## Parent application

The conditional initialization and computed-prefix results do not establish that production entries satisfy caller validity. Full model preservation and the independent production constructor/session plus `candidate_source`/`candidate_intrusion` bridge remain open. Original R70, Simple-sub A/B, source/native correspondence and production remain OPEN; Parent/A/B stays 0->0; `NO_SAFE_CODE_SLICE` remains. Independent review is pending.
