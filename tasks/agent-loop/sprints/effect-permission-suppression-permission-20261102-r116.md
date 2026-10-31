# EFFECT-PERMISSION-SUPPRESSION-PERMISSION/20261102-R116

Status: admitted continuation of the active Rust/Lean soundness and effect-hygiene goal after R115 closeout. Preserve original source claims, quantifiers, semantics and parent gates.

## Fixed outcome

For a successful `Suppress` decision only, establish whether the selected provider operation member belongs to the retained concrete permission of the same registered formal annotation. Trace the actual source-row constructor, registration/owner/Lambda links, permission producer, selected Catch arm, provider operation match and suppression consumer. Derive membership from those constructor equalities and identity links; do not assume membership. Or find an exact owner/occurrence mismatch and propose the minimum owner-local repair. Do not claim that every incoming member is concrete: annotations authorize local subtraction on an open input, so additional `write` inflow remains possible.

## Immutable Rust pins

Baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`:

- `crates/yu-solver/src/candidate_receiver.rs`: `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`
- `crates/yu-solver/src/candidate_effect.rs`: `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`
- `crates/yu-solver/src/candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `crates/yu-solver/src/lib.rs`: `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`
- R115 reviewed handoff: `tasks/agent-loop/inbox/effect-permission-rust-consumer-path-r115.md`, `4996881f23dd0982b11aea64d37d0771cc1151864be6154f9d898b35ff4d3700`.

## Lean pins

- `ComputationPermissionEntryR39.lean`: `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`.
- `InternalPermissionIncidenceR45.lean`: `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`.
- `OwnedResidualProjectionR54.lean`: `cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9`.
- `InternalRootPolicyR62.lean`: `e76e41a853673e75555cc5e603f1f84c456332794980613c554a2d69af8d976e`.
- `FormalPermissionSourceAllocation.lean`: `795e63e850f73d75f18f721224d3e0723c187a57c7437ffe3ef08a4dbd80648a`.
- `FormalPermissionAnnotatedRelay.lean`: `0ef1272595c766206d8d9c7232f8799937706dbf292b94483621ceabe2159c2e`.
- `OriginalSourceGeneration.lean`: `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.

Only these modules and their exact transitive import dependencies may support the proof lane. Record any direct transitive pins actually relied upon in the proof handoff; do not read dirty Rust worktree bytes.

## Lanes and limits

1. Luna/high source lane, ≤480 seconds: write only `tasks/agent-loop/inbox/effect-permission-suppression-permission-r116-source.md`. Read only the four exact pinned Rust blobs. Trace `assemble` concrete singleton/family guard → selected arm/provider identity → source formal annotation row → `candidate_formal_entry_annotation` permission copy → exact registration/owner/Lambda identities → successful Suppress. Report source-derived membership or a precise counterexample/owner mismatch. No source edits.
2. Registered `lean_prover`, ≤300 seconds: write only `notes/theory/lean/YulangClosure/SuppressionPermissionR116.lean` and `tasks/agent-loop/inbox/effect-permission-suppression-permission-r116-proof.md`. Build a named record path in which same registration/source occurrence/owner, producer-copy equality, singleton selected arm and provider identity imply membership. Do not postulate the membership relation or hide it in a LocalLaw. State explicitly what is a Rust source premise and what is not yet source/native authenticated. Preserve the open-input inflow and same-spelling/different-operation distinction. No Lean/Lake/checker execution; all declarations remain CONSTRUCTED/UNCHECKED.
3. Fresh independent `compiler_referee`, ≤180 seconds, attacks same spelling/different operation, different formal, provider/handler mismatch, empty concrete and extra `write` inflow; review source and Lean scopes separately. Static only.
4. Primary reconciles, records, adjudicates and checkpoints ≤180 seconds. Total ≤1,140 seconds; Astra 0; no descendants.

No Rust edits, compiler/Cargo/build/test, Lean/Lake/checker, installation, cache, worktree, mount or environment experiment. Do not repeat R111 feasibility research. A defect may justify a later exact source-fix lease but does not waive R111's closed compile gate. Only independently reviewed research artifacts may be committed/pushed. Original source soundness, complete effect hygiene, principality, termination, source/native and production remain OPEN; R114 App/Lambda admission transport remains OPEN.
