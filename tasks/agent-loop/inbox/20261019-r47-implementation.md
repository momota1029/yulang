# Luna implementation handoff — R47

Task: `R47-LUNA-TEMPORAL-IMPLEMENTATION`  
Sprint contract: `tasks/agent-loop/sprints/temporal-copy-evidence-20261019-r47.md`, rev 1  
Original parent: full inference/evaluator theorem and Simple-sub A/B, unchanged quantifiers, source domain and accepted semantics; **OPEN 0 → 0**.  
Outcome class: source-native-evidence / bounded implementation obstruction.

## Result

The exact helper construction does not execute the required later
`canonical_rows` map hit. `Capture::row` deduplicates rows by their current
intrusion representative. `route_candidate_local_run` calls graph capture and
then immediately starts `prepare_candidate_fresh_use`. Preparation builds its
local canonical map in one pass; it has no existing-row union before each
lookup. The first later restoration and solver drain occur after all row
observations have been recorded. So every `canonical_rows_hit` is false in
this constructor, and later merges cannot make a past lookup hit.

The separate temporal gap remains: a reconstruction-time `source_representative`
does not establish its relationship to the later representative after merges
or rollback. Its actual mutation owners are `merge_candidate_rows` and
`State::rollback` in `candidate_intrusion.rs`; the current row observation
retains no transition chain or historical snapshot.

Exact source-owner report:
`notes/progress/2026-10-19-r47-temporal-copy.md`.
SHA-256: `cfcd2c910c1f74221a654954d99c02c0bea05f940c20adae3f66bcf4a4b15b3b`.
The independent proof lane is preparing the corresponding call-path and
no-hit derivation at:
`notes/theory/2026-10-19-r47-temporal-copy-refinement.md`.

## Before / after and exclusions

- Before: R37 rev3's existing test-only candidate had a vacuous final-class
  selector and no temporal edge. The contract requested an authentic later hit
  reusing a fresh image.
- After: the exercised helper construction is statically shown not to reach
  that event under its pinned owners. This is a bounded obstruction, not a
  counterexample to the original theorem.
- No source, test, build or runtime modification was made in this lane. No
  expected-output, source-domain, public API or production behavior change.
- No Cargo/test command ran. The positive-witness gate is unmet.
- No theorem condition was discharged; parent remains OPEN 0 → 0.

## Review seam and falsifier

Request fresh compiler and spec review of the frozen helper call path, capture
deduplication, preparation's map construction, and the first restoration/merge
boundary. The argument is false if a real forest mutation occurs before map
construction finishes, if the graph contains two rows with the same captured
representative, or if the actual tested helper follows a different constructor.
Do not create a synthetic graph or weaken the requested witness to make the
predicate pass.

## Mutual TODO, ownership and resources

- Sol: finish the exact no-hit proof, separately name the temporal edge missing
  after reconstruction, apply both facts to the original native transport
  premise, then stop writes.
- Luna: intake the frozen proof; obtain the reserved fresh reviews; adjudicate
  the constructor-specific obstruction. No test is authorized unless a reviewed
  reachable witness is first established under an approved contract revision.
- Existing dirty `candidate_scheme.rs`, `shadow_apply.rs`,
  `candidate_local_self_recursion.rs`, and historical untracked records remain
  preserved. No candidate source code was edited in R47.
- R47 cap remains 3000 seconds; no renewal/carryover. Reviews retain their
  300-second reservations; no Cargo process was started. Astra allocation is
  zero. Runtime CPU/RSS and effective model/effort are UNKNOWN.

Worker state: Luna implementation write set frozen. This handoff is a primary
artifact; Git remains primary-only. Parent, source semantics and production
gates are unchanged.
