# R33 native active-capture join — stopped at FreshUse image comparison

## Outcome

The exact two-helper source fixture and private source-action records are in the
leased tests. The focused Cargo command compiled, but its only selected unit
test failed before reaching the intrusion-observer event/parent/group assertions.
The failure is in the new claim that every row in the two helper FreshUse maps
has a distinct identity. A FreshUse map can retain shared rows as well as its
per-use local images, so all-row disjointness is unsupported. No observer join,
signed pair incidence, or source/native success predicate is claimed. Original
parent conditions remain OPEN, `0 -> 0`.

## Source and native evidence reached

The fixture is `outer` with one active recursive `loop` initializer, a nested
`helper`, and two independent `helper x` calls. Before the failing assertion,
the test established two `helper` source occurrences, one exact `Action::Link`
for a `loop` occurrence, two matching `Action::Local` helper routes, successful
candidate inference, two retrievable nonempty FreshUse maps, and no FreshUse for
the active Link. The failure occurred while comparing every row in those maps.
The observer event, signed parent/copy, representative, and group assertions
were not reached. The external integration target was not run because the
focused unit test failed first.

## Prior evidence reused and rejected

- Reused R32's source/action and observer boundary from
  `notes/progress/2026-10-18-active-capture-native-path-r32.md`, and the exact
  accepted-source owners in `candidate_source.rs` and `shadow_apply.rs`.
- Reused the existing external regression pattern that filters to local rows
  before requiring disjoint FreshUse identities. Rejected applying that
  disjointness claim to every row in each map; the focused failure demonstrates
  that this stronger assertion does not hold.
- Did not infer any pair identity from a canonical representative or from
  candidate success. No observer result was reached in this run.

## Check and limits

Ran exactly once:

```text
cargo test -p yu-solver --features shadow-apply-candidate active_outer_root_two_helper_uses
```

Compilation completed with existing warnings. Result: failed at
`candidate_source.rs:1804`, assertion `the two helper FreshUse images are
independent`; 0 passed, 1 failed, 729 filtered out. The contract's sole Cargo
process is spent; no further Cargo/build/test/probe was run. The test made no
production or observer/API change. The finding is candidate-native evidence,
not source-theorem closure or production authorization.

## Exact remaining premise and next related step

`R33-NATIVE-MAP-ROW-SCOPE-1`: determine whether the already authenticated
FreshUse records identify each use's local image subset without relying on
canonical equality alone; then compare those per-use images while retaining
shared rows as shared. Source owner: `CandidateGraphFreshUse` row observation
and the existing local-row classification. Required evidence: actual row
records for both helper maps, the exact active-Link occurrence, and the
intrusion event/source-set/pair/group incidences. Falsifier: no authentic
existing row field distinguishes the per-use local images. This task stopped
on the first focused test failure; any repair/re-run requires Luna's decision
on the consumed one-process check budget.

No provisional instrumentation was added. Cleanup owner: none. Known generated
build scratch from the authorized Cargo invocation is under `target/`; primary
hygiene should treat it as disposable build output. No other new scratch path
was created by this lane.

Requested model/effort: Luna/high. Observed model/effort: UNKNOWN (runtime did
not expose effective routing metadata). Contract cap: 420 seconds; actual
assignment work duration: UNKNOWN. Cargo process elapsed about 29 seconds.
Writes stopped after this report and its paired frozen handoff.
