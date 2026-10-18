# R47 Luna implementation lane — helper map-hit obstruction

Sprint: `temporal-copy-evidence-20261019-r47`, revision 1  
Contract SHA-256: `aba8009c8ec658af48ed2844e6a9c9b4554b4343ada19f8a7aae85b978574131`  
Branch baseline in contract: `3860c5d2bac12efde6fb543ba68a637ef47a9ab2`  
Subsequent primary checkpoint: `e39d3c8d5`  
Original inference/evaluator parent: **OPEN, 0 → 0**.

## Bounded result

The required later canonical-row hit cannot occur in the current helper route.
`route_candidate_local_run` calls `capture_candidate_graph_owned` and then
immediately calls `prepare_candidate_fresh_use` at
`crates/yu-solver/src/candidate_scheme.rs:2022–2024`. Capture's `Capture::row`
first replaces each requested key with the current intrusion representative and
uses that representative as the unique key in `Capture.rows`. Thus the captured
graph has at most one row per representative at the capture boundary.

During `prepare_candidate_fresh_use`, the `canonical_rows` map is initially
empty and is populated while iterating those graph rows. The path performs no
union of existing intrusion rows before the lookups. `begin_use` and scope
inventory creation prepare use metadata; fresh value/effect allocation extends
the corresponding arenas and does not merge old keys. The first bound
restoration and any later candidate drain/settlement occur only after the full
row map and observations have been built. Therefore each row's
`canonical_rows_hit` is false on this construction path. Later merges cannot
retroactively make an earlier lookup hit.

This is a constructor-specific execution obstruction, not an inference
counterexample and not a global claim that no candidate route can ever hit the
map. Adding test-only event fields cannot create the absent event. I made no
source change, test, build or runtime probe in this lane. The existing dirty
candidate remains an unaccepted R37 overlay; its final-class selector and
current-representative comparison still carry the previously reviewed R37
findings.

## Separate temporal-evidence gap

Even if another valid construction later supplies a map hit, the current
`ReconstructedRowObservation.source_representative` records only the value at
reconstruction. Comparing it during later validation to the then-current
`state.intrusion.rep(...)` does not prove that identity survived merges or
rollback. The transition owner is `candidate_intrusion::merge_candidate_rows`
and its `State::rollback` journal path; no historical edge is retained in the
existing observation. This gap is distinct from the helper route's inability to
produce the required map hit.

## Source-owner map and falsifier

- Capture dedup owner: `Capture::row` in `candidate_scheme.rs`.
- Uninterrupted constructor: `route_candidate_local_run` capture followed by
  `prepare_candidate_fresh_use`.
- Map-hit owner: the `canonical_rows.get(&source)` lookup and subsequent insert
  in `prepare_candidate_fresh_use`.
- First possible later mutation: candidate bound restoration after preparation;
  subsequent intrusion union is `merge_candidate_rows` in
  `candidate_intrusion.rs`.
- Rollback owner: `State::rollback` in `candidate_intrusion.rs`.

The no-hit argument would be falsified by a real forest mutation between
capture's representative lookup and completion of reconstruction, duplicate
representatives in the captured graph, or evidence that the exercised helper
uses a different constructor. None appears in the inspected pinned path.

## Handoff

The positive-witness requirement and its gated Cargo invocation are unmet, so no
focused test was run. The contract's earlier concrete execution-obstruction
stop applies. Request fresh review of the frozen source-owner argument and
proof-lane handoff; do not change source admission, fabricate a graph, substitute
another route, or weaken the witness. Any alternate route needs a versioned
contract revision and a separately justified source owner.

No production behavior, accepted source domain, expected output or test fixture
was changed in R47. Source/native evidence here is only a bounded native
transport prerequisite. Parent claims, quantifiers, source domain and semantics
remain unchanged and open.
