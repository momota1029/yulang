# Native retained-bound evidence and stopped-capture probe

Date: 2026-10-26. Assigned baseline: `eb3eef2f6a29d9c2a6132d648866c60900db276c`, branch `yulang3`.
Producer: `/root/native_evidence`. Parent: `/root`, sole integrator.

## Exact proposed slice and authorization

The first read phase inspected actual owning algorithms, including
`candidate_extrusion.rs::candidate_extrude` and
`candidate_insert_bound_with_evidence`,
`candidate_intrusion.rs::merge_candidate_rows`,
`candidate_scheme.rs::Capture::{row,expand_row}` and
`prepare_candidate_fresh_use`,
`candidate_source.rs::execute_candidate_action`,
`candidate_call.rs::{NativeInterface,PendingCallConstruction}`, and
`lib.rs::{run_candidate,finish_candidate}`.

The concrete next action was proposed to the primary before code writes:
test whether an authentic source-generated qualified merge leaves a younger
structural dependency below a shared row, and whether an actual later capture
and fresh use independently freshens that dependency. The primary granted
only a new `crates/yu-solver/src/candidate_native_evidence_tests.rs` and the
test-module declaration at the end of `crates/yu-solver/src/lib.rs`, plus this
receipt and the assigned scratch directory. No production edit is authorized.

## Native facts controlling the experiment

- `candidate_extrude` memoizes fresh rows before selected-bound descent and
  follows one bound polarity. Its opposite-side source link is an actual
  retained bound. It is not the legacy in-place level-lowering algorithm.
- `merge_candidate_rows` copies both physical bound sides, changes the chosen
  representative, takes the minimum of the two row levels and the OR of their
  non-generic flags, canonicalizes provenance and replays lower/upper pairs.
  No recursive dependency metadata propagation appears in this merge owner.
- `Capture::row` uses `level > boundary && !non_generic` for `local`.
  `Capture::expand_row` immediately returns at `!local`, leaving that row's
  mutable bounds in the session. Fresh use rechecks the same representative
  metadata and uses one canonical-row map.
- `finish_candidate` returns a `CandidateSolvedResult` after observation
  finalization and rejects unresolved active field-tail selection. Its result
  still contains diagnostics; `Ok` alone does not state that diagnostics are
  empty, that every original Call supplier exists, or that a finite regular
  certificate has been constructed.
- `PendingCallConstruction::suppliers` still requests original GenCall0,
  whole-argument reification, and complete receiver/result/future interfaces.
  The retained scalar `NativeInterface` does not supply these certificates.

## Falsifier and scope

The falsifier is a complete source execution with an authenticated qualified
extrusion pair, a merged shared representative P, an actual retained bound
whose finite structural term contains younger Y, and an actual use which
shares P but allocates a different image for Y. The experiment does not insert
fresh rows, override levels, fabricate source-event incidence, or rewrite
expected results. Function traversal includes argument, argument effect,
result effect and result; tuple order, record fields and variant payloads are
traversed from their native terms. Both row kinds and both bound sides are
observed.

Even this falsifier would refute only an unrestricted native dependency-level
or stopped-capture invariant. It would not by itself prove accepted source
unsoundness. `SimpleSubScopedPublication.StoppedClosed` is a sufficient
condition for clause-image reconstruction, not a theorem that every sound
native implementation must satisfy. Polar links, replayed consequences or
other retained bounds may still entail a supposedly omitted clause. A source
soundness counterexample requires a legal original source witness and a
concrete native/client result violating its source conclusion; a necessary
natural-generalization claim requires a lawful source typing excluded by the
native algorithm. Neither follows merely from a row-level inequality.

## Bounded results and disposition

Two individually authorized focused Cargo runs used pinned Rust/Cargo 1.99.1,
`--locked`, one build job and test thread, a 120-second timeout, and a 4 GiB
per-process address-space limit. Both exited 0 without timeout. The first ran
the four initial source fixtures in 53.941468 seconds including compilation.
The second ran those four and three targeted mutual-recursion variants in
84.431741 seconds, including 28.27 seconds in the test body. This is seven
distinct sources, not eleven independent examples. No broader tests ran.

Command suffix:

```text
test --locked -p yu-solver --features shadow-apply-candidate --lib candidate_native_evidence_tests::real_source_history_native_dependency_probe -- --test-threads=1 --nocapture
```

Every listed source reached `finish_candidate().unwrap()` and returned zero
diagnostics. Every pre-finish worklist and typed-drain count was zero.

| Source case | Calls / source events | Actual parent-copy records | Value / effect rows | Originally qualified merge predicate |
| --- | ---: | ---: | ---: | ---: |
| `recur x = recur x`, then module Name use | 1 / 1 | 0 | 12 / 13 | 0 |
| `recur x = (recur x, x)`, then module Name use | 1 / 1 | 0 | 15 / 16 | 0 |
| nested `recur x = (f x, recur x)`, returning `(recur,f)` | 2 / 2 | 4 | 36 / 37 | 0 |
| reversed tuple order, two outer module Name uses | 2 / 2 | 4 | 48 / 47 | 0 |
| mutually recursive `left/right`, passing local identity `deep` | 2 / 2 | 0 | 28 / 34 | 0 |
| same mutual recursion, `deep y = y x` | 3 / 3 | 0 | 32 / 42 | 0 |
| same mutual recursion, `deep y = { my temp = deep deep; y x }` | 4 / 4 | 13 | 49 / 66 | 0 |

The deeper source therefore exercises real type copying; an idle candidate
path does not explain all these counts. However, no pair passed the precise
merge predicate used by the experiment: qualification in the original
`Parent.sources` set **and** equality of final parent/copy representatives.
This predicate does not enumerate later recapture/reuse activations. The
`recapture_candidate_extrusion` owner may activate an originally unqualified
group without replacing the original `Parent.sources`. The experiment did not
record `intrusion.generation` or enumerate that activation history. It does
**not** establish that no qualified reuse or merge occurred. The preliminary
short report was corrected to this exact scope before cessation.

No stopped-shared/independently-freshened dependency split was observed in the
actual retained routes. The candidate merged-owner dependency test did not
receive an owner passing its predicate, so its empty result is vacuous for
that invariant. No all-history closure, counterexample, or source bug was
established. Repeating more source scans is not the next action.

The exploratory test did not establish a durable invariant or counterexample.
Its exact source is preserved in the assigned scratch directory. The new Rust
file was removed, and `lib.rs` is restored byte-for-byte to SHA-256
`ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.
The final filesystem readback confirms the leased test file is absent and the
module declaration is absent. The second compile emitted 20 warnings; the
previous native baseline recorded 19. The exploratory source, including its
extra warning, is not retained in the compiler. No dependency, toolchain,
existing test expectation or Git operation changed.

## Exact remaining producer seam

The new finite decision result can construct a certificate for a supplied
regular graph. The native owner still must construct that graph and establish
that its demanded clauses represent the actual computation. The following
existing data should be consumed directly in the next constructive packet:

1. `candidate_insert_bound_with_evidence` (702) already returns a
   `BoundEmissionId` and retains an exact `PhysicalBoundSlot` plus immediate
   readback (850-874). `candidate_opposite_count` and
   `candidate_opposite_bound` (877-935) enumerate the selected row side in the
   same direct-row/structural-endpoint order. These are the authentic owners
   for a complete finite physical-bound inventory, not scheme snapshots.
2. `candidate_replay_bound` (1070-1111) records ordered lower and upper bound
   inputs for every generated comparison. The resumable restoration path
   (1000-1068) additionally owns saved opposite count, live canonical read,
   replay receipt and completion. A native history adapter must preserve
   those actual operation IDs and completion states; an empty queue alone
   does not replace them.
3. `merge_candidate_rows` (599) records copied-bound transport with the
   actual `parent_index`, preserves both sides and changes the row forest.
   Source qualification for that equality must include original activation
   **and later reuse activation**, not only `Parent.sources`.
4. `Capture::expand_row` (2137) intentionally omits bounds below stopped
   owners. Its `Graph` cannot be substituted for the whole native store.
   `prepare_candidate_fresh_use` (4199) owns the actual single canonical-row
   map; use that map and the retained bound-restoration records rather than
   an arbitrary renaming assumed to describe native use.

The minimal missing semantic datum is a **constructed interpretation of each
canonical native row as a node of the finite regular graph**, with every
retained bound and original demanded comparison represented. A raw row ID is
not such a node: `Regular.Node` has guarded constructors and no bare variable
alias; the actual candidate store still has row variables and may require
unions/intersections, native row width/presence semantics and contextual
effect operands absent from the current finite graph fragment. The existing
capture graph and scalar Call interface do not supply this assignment.

A useful next packet should start at the exercised physical-bound and replay
owners, export their exact finite inventory/representative/history data, and
construct the row interpretation for one explicitly supported native
structural fragment. It should then apply the finite decision theorem to the
generated graph, with an executable falsifier that omits a physical slot,
swaps a Function port, or drops a replay child. This removes concrete
representation and history premises for the covered native slice. It must
still state how that slice extends to all native constructors; a successful
bounded example does not close the original theorem. No production checker,
search requirement or changed inference rule follows from this recommendation.

The full original source obligation additionally requires complete Call
suppliers and source-scoped joint witness/publication correspondence. Native
no-error completion does not remove those requirements. Numeric metadata
closure remains a sufficient proof condition whose necessity for backward
soundness or natural generalization has not been established here.

## Frozen evidence and cessation

All evidence files are in
`/workspace/scratch/f98087c7ac1a/inference-native-evidence/`.

| Evidence | SHA-256 |
| --- | --- |
| `candidate_native_evidence_tests.rs` (scratch only) | `957f3f0f39c218e7da4118993fcebb64241fc5de2e396722b62ea6c814db5c9d` |
| `native-probe-01.log` | `ad3e69ac25c99bf328dd614e5b7bf2e2c3bd27e67cddbd9f79586e038bfffd86` |
| `native-probe-01.json` | `abe350916dcac4522ae15a39d3e31c5e2c8e53c7e584439ba1a2b1b7acb75d7a` |
| `native-probe-02.log` | `b15a83356791b59b8226a3e9f5f123e79d71de7ac636c1b9ee99c43cee8daff1` |
| `native-probe-02.json` | `e7174310a07a6cc94890452b65133bcf0a13bfa6ef3330ea03df37284ffb2231` |

`native-evidence-hashes.json` also records the exact inspected owner-source
hashes. No Lean file was written or checked; no theorem or axiom audit is
claimed. Both Cargo process groups completed normally. No descendants were
started. The only retained repository write is this receipt. All writes stop
with its final hash receipt to the primary. Original inference A/B, native
success correspondence, full Call and production/cutover gates remain OPEN.
