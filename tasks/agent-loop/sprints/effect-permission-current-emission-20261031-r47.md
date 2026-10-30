# Sprint EFFECT-PERMISSION-CURRENT-EMISSION / R47

Status: ADMITTED by Luna under unchanged ongoing `research/simple-sub-intrusion` goal. Branch `yulang3`; single existing checkout; baseline `8017b53f5`.
Authority: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2 and current goal-driven sprint rules. R46 is CLOSED_INCOMPLETE; its concrete source arrival and first absent owner transition remain unresolved.

## Fixed outcome

Authenticate the owning-record join needed before another arrival theorem: an actual retained `BoundEmission` must name its unique owning admission; that admission's bound must reconstruct from the emission's physical owner/lane/index as a **current** slot read; its relation ancestry must be connected by exact retained dependency evidence to R45's complete Internal `DefinitionUseId` and same raw entry. The query is private, borrowed and partial; unavailable on ambiguity, stale slot, rollback, missing/foreign ancestry or source mismatch.

Success is a source-derived positive construction for this join, or a source-qualified exact missing owner field/constructor transition. A theorem assuming the whole join, historical emission, graph reachability, canonical-row equality or equal endpoint is not success. This packet does not itself claim provider-arrival meaning, Catch selection, residual subtraction or parent A/B/hygiene closure.

## Exact lanes and leases

### Rust implementation, Luna/high, ≤1,200s

Implement only a private read-only query/wrapper around existing records. Verify: (1) R45's actual Internal certificate; (2) emission→owning admission identity and uniqueness; (3) physical owner/lane/index→exact reconstructed bound from a current physical read; (4) admission relation→retained ancestry rooted in that complete Internal use. Return explicit unavailable reason where a link is missing. No propagation, routing, producer retention, consumer, subtraction or semantic changes. If an owned producer change is necessary, stop and report; no authority for a producer repair in this packet.

Write only:
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_receiver.rs` (private experiment wrapper only)
- `tasks/agent-loop/inbox/effect-permission-current-emission-r47-rust.md`

### Lean constructive proof, ≤1,200s

Write only:
- `notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean`
- `tasks/agent-loop/inbox/effect-permission-current-emission-r47-proof.md`

Use pinned Lean 4.35.0 stdin, one CPU, `-M1024`, ≤120s/invocation. No Lake/build/tests/extraction/scratch/cache/.olean/target/environment. Model the actual owner records and checked query; prove accepted current-slot consistency, same-use ownership, and stale/foreign rejection. Apply R45 using the same permission witness, with source extraction equations explicit. Keep provider arrival and Catch separate. Include every complete theorem type and transitive axiom audit, failed diagnostics and resource receipts; STOP/freeze before review.

### Fresh independent review, ≤900s

Primary assigns `/root/r37_inventory_review` only after authors STOP and hashes freeze. Review exact path/rollback/current-read semantics, same-use ancestry, swapped-slot/emission and foreign/stale falsifiers, R45 application, every theorem/type/axiom receipt and dirty-delta isolation. Write only `tasks/agent-loop/inbox/effect-permission-current-emission-r47-review.md` or return complete frozen review for primary placement. No reruns/builds/tests.

## Frozen dependencies (rehash before dispatch)

- `candidate_context.rs` `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38`
- `candidate_receiver.rs` `f5bff0d8aa7a20551fb2c5ad60b7b2b41907f471a55068a9ec1ae61ceba02911`
- dirty read-only `candidate_effect.rs` `2a86befde95581decef8fe01698961062bd22388cff2459e9611570a20b9fba3`
- dirty read-only `candidate_scheme.rs` `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`
- `lib.rs` `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`
- read-only copied-bound owner `candidate_extrusion.rs` `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- R45 Lean `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`, Rust handoff `5ca8058e79015b4896260c19aa2b389449324e223c169419fd873177910c4341`, review `a4e40d0b5ced25574e821047727cdcba21c35bb7d6701e6641ed0869b6647c6b`
- R46 Lean `3429aef705d2c059c23c8ec0a33dd1e4a6dcb75c9461e90f4380df679146f3c3`, Rust handoff `5874c13e7332037c1884e63c35966d5f237a9fa1bb09d4696084eb2a32b44831`, proof `f88845dfc5f7e62683e820546f3467c9ce598e786107f5ceee608025bcbf8bf7`, review `7fbaed174bee5cae7a92874ddd795b9b80ec1bc8cd7f18acc30e6dedfde7c56e`, outcome `512e2afbe9f5f6ac12279b587fb6c2453f78bed1254ba4eff33fd69ea3395f14`
- governing parent, Lean pin and audit helper as pinned in R46.

## Resources, review and Git

Total ≤4,200s: Rust1,200; Lean1,200; independent review900; primary900 including ≤500 closeout; Astra0. Same checkout and already installed toolchain only. No new worktree/environment/cache/target/scratch, background service, nested CLI, build/tests/Cargo/Lake/formatter. No overlapping writers or descendants. Stop on any required producer change, unmatched edge, stale readback, pin mismatch or unresolved authority. Unknown writers retain quarantined leases.

Only Luna stages explicit paths and pushes coherent reviewed checkpoints. Preserve all unrelated dirty/deleted paths; no blanket staging, clean, reset or stash. Preserve all 32 pending, UNKNOWN assignments and quarantines. User disk constraint remains active: do not add any environment or build/cache growth.
