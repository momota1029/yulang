# R48 implementation receipt: actual-route temporal transport

Status: implementation candidate frozen for independent review; no test has run.
Sprint: `actual-route-temporal-transport-20261019-r48`, revision 1,
contract SHA-256 `e17bd3f602cb00cb600d6647432a18cc6df5d5ce8d5eb59a78eba52eb8dfbc5a`.
Parent inference/evaluator theorem and original Simple-sub A/B remain
**OPEN, 0 -> 0**.

## Implemented evidence

The `#[cfg(test)]` overlay records forest identity births, merge and compression
parent writes, rollback parent restores, and rollback truncation at the actual
`candidate_intrusion` owners. A failed event reservation permanently marks the
ledger incomplete; validators reject incomplete history. Each captured graph
retains one full forest snapshot and its event cursor. Capture and reconstruction
observations retain their own cursors. The consumer replays the ordered events,
checks every old link and resulting parent, and compares replay at inspection
with both live forest arrays.

The signed-pair join uses the indexed owner `Parent`, verifies the trigger
comparison and source event, and selects each signed copy and parent through its
representative at that graph's capture cut. It checks q's positive argument C
and negative result D independently, and checks both retained helper-use routes
against their owner route indices and row maps. Reconstruction still asserts
R47's actual-helper no-hit invariant; it does not require an unreachable hit.
Negative controls remain for a wrong Apply occurrence, missing event, wrong
coordinate/polarity, sibling route/map, wrong structural comparison, and a
forged same-kind Parent.

The fixture-facing assertion identifies the nested `loop y` Apply by exact
occurrence, Candidate recipe, scheduled source action and checking event. It
then demands both C/D parents with one triggering comparison and separately
rechecks each coordinate on both actual retained routes. These are test
assertions only. Until the gated test runs, q reachability and successful
inspection are not execution receipts.

## Static audit and limits

A source search found the complete private forest mutation set in
`candidate_intrusion.rs`: identity extension in `retain_extrusion_parent`,
parent assignment in `merge_candidate_rows`, compression assignments in
`compress_candidate_forests`, and restore/truncation in `State::rollback`.
`State::rep` is read-only. The monotone test log remains outside the rollback
checkpoint. Route and image survival use the existing retained `local_routes`
owner relation and source transaction rollback/commit length argument in the
R48 proof; this overlay does not add hooks to `lib.rs`.

`git diff --check` passed on the two implementation files and the compact state
file. `python3 tools/agent_sprint.py check` passed (static state validation
only). No Rust compiler, Cargo, test, or runtime probe has run. The next permitted
execution is the single focused Cargo command in the contract, only after both
fresh independent reviews report no BLOCKING or major issue.

The proof packet is conditional on exhaustive source coverage and the actual
retained owner lineage. The implementation candidate has not yet been reviewed
or executed. It establishes no source `Desc`, ordered `D_q`, complete Call rule,
evaluator theorem, production authority, or parent claim.

## Frozen inputs

- Contract: `e17bd3f602cb00cb600d6647432a18cc6df5d5ce8d5eb59a78eba52eb8dfbc5a`
- Conditional proof: `50f70a8a47faaac1cff670044faf4faafbf2a495d0a437bcab6bee1983095e13`
- Proof handoff: `8b56a60b157411d2ab53ce2b35073d5fd23ee73a3fec0fad59422d9eddb72d13`
- `candidate_scheme.rs`: `d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278`
- `candidate_intrusion.rs`: `8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4`

This receipt is a producer handoff, not independent review or test evidence.
