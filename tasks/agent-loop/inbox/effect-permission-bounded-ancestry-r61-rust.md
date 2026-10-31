# R61 Rust source handoff — bounded ancestry

Sprint: EFFECT-PERMISSION-BOUNDED-ANCESTRY/20261031-R61  
Contract SHA-256: `4ee44b5aae475fefaa185249681f1631f43f33d8cf6c4d498d1cc94879e9d435`  
Admission SHA-256: `4cf7bdbd57fc0d5c869799e77b11ac73c37e3d25fd15ee4a01a3e41a3f6c66b2`  
Assignment: R61 Rust lane; handoff revision 1  
Parent: Yulang inference/executor soundness, effects, principality and termination; unchanged Simple-sub A/B scope.  
Worker: `/root/r52_rust`; requested Luna/high; observed model, effort, exact wall-time and runtime session telemetry: UNKNOWN.

## Frozen source and dependencies

- `crates/yu-solver/src/candidate_context.rs`: `cf73489b771067c2cd01d738a29e74f8a180c8fece782b5829871f02db36d106`; R60 baseline `8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89` matched before edits.
- `crates/yu-solver/src/candidate_receiver.rs`: `3b60a58a1dba75b908607d91a76f49403314d3667a07987e29fc30fc4a7907e5`; R60 baseline `0b25ddde51ee77cfdc558ad4384ce827e9f48880bd598f1640f5323a102672de` matched before edits.
- `crates/yu-solver/src/candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.
- R61 contract: `4ee44b5aae475fefaa185249681f1631f43f33d8cf6c4d498d1cc94879e9d435`.
- R61 admission: `4cf7bdbd57fc0d5c869799e77b11ac73c37e3d25fd15ee4a01a3e41a3f6c66b2`.
- R60 reviewed module `NativeLocalDecodeR60.lean`: `3eccc41902a8a8768a55cac020efd4936517da3feb2d91a7ec158994a133ca20`.
- R60 Rust handoff: `744014a3ec186e16e82cca0ba3497f53a08d2eb5bd5f60fe7f41ae8461b46730`.
- R60 placed review summary: `tasks/agent-loop/inbox/effect-permission-local-decoding-r60-review.md`, `e360556fbb37cc98f53ad0b82bd0daaafa7454bac275401a8c3c097dd155541f`.
- R60 returned review report hash, distinct from the placed summary: `8d80bf7049829d0d713d2a67d072cf2cf8be9f415538100d847ab7e815f08d5d`.
- R60 outcome: `tasks/agent-loop/history/effect-permission-local-decoding-20261031-r60-outcome.md`, `d172514ed1c743a9f697b1444f2c4414ab1c7d616be16cb8f51a93597f29cce1`.
- R57 native model: `ProviderNativeContextR57.lean`, `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63`.
- R58 search model: `ReachedSlotSearchR58.lean`, `431d3b4cb031fd86ad4a0537c1c8a42adecb8433f3ef775b3371eb37611b3079`.
- R59 completeness model: `ReachedSlotCompletenessR59.lean`, `d0d1a33e416a13ed29e5ba018f5adf1e0a71b6b5886d2d04f74956522836bfab`.
- R59 proof handoff: `tasks/agent-loop/inbox/effect-permission-search-completeness-r59-proof.md`, `830b01128716055f4b3b54e2c650e865af97bc2ff1f5d54efcd34a78e07501e9`.
- R55 source/Internal model: `SourceInternalContextR55.lean`, `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`.
- R39/R45/R47/R48/R49 model hashes: `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`, `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`, `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c`, `b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575`, `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2`.

Every corrected R61 contract/admission pin and transitive source/model input matched before source edits. The R60 returned-report and placed-summary hashes remain distinct as the corrected contract records them.

## Source change and correspondence

R60's `LocalDecodeReader` already verifies that its `OwnedResidualProjection` retains the exact session State, complete indexed relation table, and complete indexed dependency table. Added `OrderedAncestryReader`, constructible only from that reader. It borrows the exact ordered tables without copying or filtering them. `ordered_parents(child)` reports each matching dependency index, its original `Dependency`, parent ordinal and directed parent; Replay retains lower at ordinal 0 and upper at ordinal 1. Parent IDs are returned raw, including invalid IDs; validation remains at the visitor point where that dependency is reached.

`successful_call(descendant, ancestor)` invokes the existing `State::require_relation_ancestry` exactly once and returns the query plus the same State and full ordered tables only on `Ok(())`. It returns the native `CurrentEmissionGap` unchanged on failure. The read result is a successful-call refinement input, not a reconstructed traversal trace and not a pure success predicate that can stand in for repeated native calls.

In `candidate_context.rs`, factored the visitor's dependency-to-parent match into `relation_ancestry_dependency_parents`. The existing loop calls this pure helper, then retains its same order and control: query-index validation; unconditional 65,536 relation-count guard; pending then seen reservations; initial push; pop and per-call visit charge; equality success before visited suppression; relation validation; each ordered dependency scan and charge; parent validation before visited check; unseen-parent reservation and push; exhaustion as `MissingUseAncestry`. Replay still enqueues lower then upper, so the upper parent remains at the LIFO top. No work counter, allocation, control branch, or propagation behavior moved.

The helper makes the Rust's selected directed parents available to the R61 correspondence. The native visitor itself still supplies the success/failure result; no alternate walk is used to authenticate it.

## Evidence, checks and limits

- Inspected the R60 source and review, `ProviderNativeContextProjection`, `OwnedResidualProjection::verify_owner_round_trips`, `LocalDecodeReader`, `State::observed_dependencies`, `owned_projection_relations`, and the full `require_relation_ancestry` implementation.
- No build, test, typecheck, Cargo, formatter, Lake, compiler, cache, scratch, target, environment, worktree, service, persistent process or Git mutation was used.
- `git diff --check`: passed.
- `python3 tools/agent_sprint.py check`: `STATIC CHECK PASS (not independent review or live execution)`.
- Final source hashes are recorded above. No Rust build, test, or typecheck was run.

The successful query record supplies the same-state indexed tables and source-order parent selection needed by the proof lane. It does not record the actual visited path. It does not claim that repeated calls have identical allocations or failure traces: each call can encounter different allocator outcomes. It also does not make malformed, unvisited dependency parents globally invalid. The source visitor checks descendant and ancestor first, then the size guard before allocation; invalid parents fail only when a reached child scans that parent. A valid reflexive query can therefore succeed before scanning dependencies, after the same guard/reservations/first visit as the original code. These cases remain governed by the exact native call order.

Internal-root extraction, actual Rust-to-Run correspondence, general allocation/work/exhaustion trace simulation, pointer/Nat state-tag interpretation, complete Context/R50 extraction, runtime, original A/B, inference soundness, principality, termination, complete hygiene and production remain OPEN.

## Lease and STOP

Written paths: `candidate_context.rs`, `candidate_receiver.rs`, and this exact handoff only. No other path or scratch output was written. Final hashes and checks are to be inserted after freezing the code; no post-freeze source edits are planned.

Worker state: STOPPED; **WRITES STOPPED**. Final source hashes and checks are recorded above. No descendants or persistent subprocesses were started.

Next related step: the R61 proof lane proves that a successful call over these exact ordered records establishes directed retained ancestry, then applies R60's policy. A fresh independent review should inspect the frozen source and theorem together. General repeated-call resource/failure equivalence stays open.
