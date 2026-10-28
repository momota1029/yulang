# Frozen handoff — selected module freshening prefix repair

Sprint/contract: `SELECTED-MODULE-ENTRY-AND-FRESHENING/r1`, amendment 04.
Assignment: restore the protected publication trace prefix; this is a candidate repair only.
Parent gate/scope: selected source occurrence's typed module entry and whole freshening image; no parent, source/native, effect-hygiene, or production gate closes.

## Evidence and change

Leased artifact: `isolated/selected-module-entry-freshening-repair-r1/crates/yu-solver/src/candidate_scheme.rs`
- Initial SHA-256: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`
- Final SHA-256: `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e`
- Exact one-line diff at line 2865:
  - `negative-root-publish id={:?} term={term:?} node={index} endpoint={endpoint:?}`
  + `negative-root-publish term={term:?} node={index} id={:?} endpoint={endpoint:?}`

This restores `negative-root-publish term=... node=...` as the event prefix and retains capture identity only after the original term and node fields. The protected assertion owner `candidate_effect.rs` was not edited; its observed SHA-256 remains `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6`.

Checks: source SHA and edited line readback only. No build, Cargo, tests, Lean, runtime, or Git operations were run, as required. The broader three-file candidate remains REJECTED and this repair does not admit its baseline or authorize verification.

Requested model/effort: Luna/high. Observed model/effort: UNKNOWN in this worker interface. Active-work budget: bounded by the assigned 150-second maximum; no renewal requested.

Writer state: STOPPED; both leased outputs are frozen. No generated or scratch paths created. No deviation from the lease or amendment.
