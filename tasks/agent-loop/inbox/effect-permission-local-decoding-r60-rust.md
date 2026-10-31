# R60 Rust source handoff — local decoding

Sprint: EFFECT-PERMISSION-LOCAL-DECODING/20261031-R60  
Contract SHA-256: `167dfbe6cef3ea963397623331788a98ec54487386dbab0401e5b805386f5f39`  
Admission SHA-256: `2e93af2a694d02214c6c53c1493b9bd6fd0a0472d7ec232101ffff9013bedebe`  
Assignment: R60 Rust lane; handoff revision 1  
Parent: Yulang inference/executor soundness, effects, principality and termination; unchanged Simple-sub A/B scope.  
Worker: `/root/r52_rust`; requested Luna/high; observed model, effort, wall-time telemetry and runtime session metadata: UNKNOWN.

## Frozen source and dependencies

- `crates/yu-solver/src/candidate_receiver.rs`: `0b25ddde51ee77cfdc558ad4384ce827e9f48880bd598f1640f5323a102672de`
- `crates/yu-solver/src/candidate_context.rs` (read-only): `8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89`
- `crates/yu-solver/src/candidate_source.rs` (read-only): `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `tasks/agent-loop/inbox/effect-permission-search-completeness-r59-proof.md`: `830b01128716055f4b3b54e2c650e865af97bc2ff1f5d54efcd34a78e07501e9`
- `tasks/agent-loop/history/effect-permission-search-completeness-20261031-r59-outcome.md`: `a60e7aade5fef31efde21cdb4a94ad05435e185e6164b47c0d69dcf32c0eeb58`
- `tasks/agent-loop/inbox/effect-permission-search-completeness-r59-review.md`: `59658c916da9d5cf6f766568045b1de7f1dc3348fec0076118ab81d3c9a694b3`
- R59 model `ReachedSlotCompletenessR59.lean`: `d0d1a33e416a13ed29e5ba018f5adf1e0a71b6b5886d2d04f74956522836bfab`
- R58 model `ReachedSlotSearchR58.lean`: `431d3b4cb031fd86ad4a0537c1c8a42adecb8433f3ef775b3371eb37611b3079`
- R57 model `ProviderNativeContextR57.lean`: `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63`
- R55 model `SourceInternalContextR55.lean`: `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`
- R39 `ComputationPermissionEntryR39.lean`: `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`
- R45 `InternalPermissionIncidenceR45.lean`: `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`
- R47 `CurrentEmissionOwnershipR47.lean`: `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c`
- R48 `ProviderEntryArrivalR48.lean`: `b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575`
- R49 `AuthenticatedResidualConsumerR49.lean`: `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2`

All contract pins and the R59 proof-handoff R39/R45/R47/R48/R49 hashes matched at inspection. The R59 review is the reused independent source audit; no new independent review is claimed here.

## Source change

Added a private `LocalDecodeReader` created only from `ProviderNativeContextProjection`. Its constructor rechecks the complete borrowed effect-row inventory against the exact session rows, the complete view inventory against the exact graph view table, `SourceInternalProjection::verify_owner_round_trips`, provider path owner round-trips, and pointer identity between `native.live_state` and `graph.intrusion.effect_algebra.context`. The reader keeps the same retained session and State references and allocates no copies or identifiers.

The reader exposes:

- complete borrowed row and view inventories;
- indexed `BorrowedEffectRowRead`, retaining original row index, canonical representative, raw `EffectBounds`, and the same State reference;
- indexed `BorrowedEffectViewRead`, retaining the original view and same State reference;
- `physical_lower(row, lane, index)`, which reads the exact target from that indexed current row vector, forms the positive raw `BoundKey` and `PhysicalBoundSlot`, and calls `State::checked_physical_lower_edge`.

The checked native helper authenticates a unique emission at the exact slot, emission/current/readback bound and slot equality, admission presence and bound equality, relation presence, and live `relation_pair == bound_pair`. The returned `BorrowedPhysicalLowerRead` retains the original row, its index, the State reference and the helper's borrowed checked emission/admission/relation. This reader does not call `require_relation_ancestry`; Entry/Catch ancestry policy stays in its original search path and order.

Malformed atom-lane `EffectRow` endpoints return unavailable (`BoundMismatch`). This is necessary for R47/R58 correspondence: R47 maps an effect atom-vector element through `effectAtom`, whereas native current-bound construction interprets an `EffectRow` constructor as an `effectRow`. The ordinary `certified_lower_paths` search and forwarding behavior are unchanged. No producer change is needed.

## Checks and evidence

- Read and matched the exact R60 contract, admission and pinned R55–R59 source/model cone above.
- Inspected `ProviderNativeContextProjection::capture`, `OwnedResidualProjection::verify_owner_round_trips`, `SourceInternalProjection::verify_owner_round_trips`, `ProviderNativeContextProjection::verify_path_owners`, `State::checked_physical_lower_edge`, and R47/R48/R49 reader definitions.
- `git diff --check`: passed.
- No build, test, typecheck, Cargo, formatter, Lake, compiler, cache, scratch, target, environment, worktree, service or nested CLI was run or created. No Git mutation occurred.

## Parent application and open premises

This supplies concrete borrowed source constructors for R60's rows, views and physical positive effect-lower read. It gives the Lean lane exact field sources and an atom-row falsifier guard. It does not itself prove Lean `LocalDecode`, successful R58 execution, arbitrary Rust-to-Run simulation, inner ancestry visitor/resource correspondence, source execution, full Context/R50 interpretation, complete hygiene, original A/B, inference soundness, principality, termination or production authority.

The source State has object identity, while the Lean R57 representation uses a `Nat` state tag. This Rust change anchors reads by pointer equality to the same retained `State`; a theorem connecting that pointer-anchored owner to the model's common state tag remains a source-to-model interpretation premise. The returned records preserve raw and canonical row data separately. Allocation/error behavior of the R58 search and exact inner ancestry/resource behavior remain outside this reader.

## Lease and STOP

Written paths: `crates/yu-solver/src/candidate_receiver.rs` and this exact handoff only. `candidate_context.rs`, all Lean files, contracts, state/board files, and other inboxes were not written. No disposable scratch path was created.

Worker state: STOPPED; **WRITES STOPPED**. Exact frozen source SHA-256 is recorded above. No descendants or persistent subprocesses were started.

Next related step: the R60 proof lane constructs all three Lean readers from these borrowed records, proves each `LocalDecode` field, and applies R59 on the same inputs. Fresh independent review must audit the frozen code and proof together. The Rust-to-Run and ancestry/resource gaps stay open.
