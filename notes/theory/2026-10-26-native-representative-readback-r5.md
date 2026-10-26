# Construct representative readback for the shared driver

`NativeRepresentativeReadback.lean` discharges the two representative-map
absorption premises of `NativeContextReadback.Step.merge` from the generated
raw forests established by `NativeRowRepresentative`. This is a concrete
application to the existing shared driver, with no new driver relation.
Original inference soundness remains OPEN.

## What is constructed

`Readback forest map` says that the raw parent-pointer lookup loop returns
`map row` for every row, including native identity lookup outside the vector.
It contains no idempotence, monotonicity or absorption law. An `Interval`
records only a generated prefix and successful birth/link/compression events.
Certificates and maps are constructed from these events, and deterministic
lookup proves that they agree with the observations.

`construct_merge_event` produces both final maps and the actual existing
`Step.merge` event without a final-map or absorption premise.
`construct_merge_history` appends it to the same reachable Context/drain Run;
the owner/memo/processed-work invariant and actual settlement frame follow
from that Run. Control, relation/task tables, memo and owners are retained.
The settling guard is preserved.

The general interval theorem is a discharge of the existing driver's coarse
map-update premise. It does not count concrete native generation changes:
one coarse event increments the model generation once, even when an interval
records several raw pointer operations. The two single-link theorems avoid
that aggregation when checking the native one-merge case:

- `single_effect_merge_event` reads both Effect representatives, writes the
  copy root to the parent root, and retains the Value map.
- `single_value_merge_event` does the corresponding Value write and retains
  the Effect map.

Both preserve inside guards, same-kind separation and unequal-root guards.
Equal roots are the existing native no-op, not a generation-advancing link.
`compression_keeps_readback` executes the native-style compression with a
constructed ghost fuel and proves every observed representative unchanged;
it introduces no merge event or generation increment. The proof-side fuel
does not impose a runtime cutoff or change the native union policy.

## Exact source and proof owners

The actual Rust source is `crates/yu-solver/src/candidate_intrusion.rs`:
`representative` (line 119), `value_rep`/`effect_rep` (165/168),
`compress_candidate_forests` (507), and `merge_candidate_rows` (599).
The latter checks equal representatives before checked generation increment,
rejects mixed row kinds, writes the directed root pointer and canonicalizes
bounds before publishing its generation. This new component authenticates
only its parent-pointer/readback portion. Checked integer/reservation failure,
capture incidence, bound canonicalization and replay are not inferred from
the pointer event.

Consumed proofs are the reviewed row construction and the published shared
Context readback at `ee61ba0b68789e2dea9eac024130f21c5a4e6453`. The exact
Rust/dependency/module hashes and full named types are in the paired handoff.

## Verification

Official Lean 4.35.0 / Lake 5.0.0-src+eb6cafb, `-j1 -M1024`,
`LEAN_NUM_THREADS=1`, one checker at a time, isolated scratch/cache and
120-second deadlines. Four focused checks were used out of ten:

1. Actual module build and `construct_merge_history`: exit 0.
2. Both single-link roots and compression: exit 0.
3. All ten authored theorem roots, full types and transitive axioms: exit 0.
4. All originating declarations, including generated/private names: exit 0.

The complete census has **32 declarations / 16 theorem constants**: four
theorem constants have no axioms; one uses only `propext`; one only
`Quot.sound`; eight use `propext` plus `Quot.sound`; two also use
`Classical.choice`. There are no custom axioms, proof holes or bypasses.
All 32 unique blocks, complete axiom lists and the EOF trailer were reconciled
independently of Lean's exit status. Census SHA256:
`b64e4e62ec5f2397bb0bfe8dceda4aca17afee1473dee7b74be62eba8cdd5502`.
No failed proof check occurred in this component's four checks.

## Remaining original bridge

The shared driver's state does not itself store the native parent vectors.
Before-map readback and extraction of the raw forest histories from the same
whole Rust run therefore remain explicit inputs. Whole combined table/history
authentication, the exact native generation history, journal/rollback cuts,
successful bound/replay mutation, semantic completion and source-scoped
reconstruction remain at their original owners. A raw forward interval cannot
be used across a cancellation that undoes an equivalence. This local
connection proves neither termination of inference nor principality and
does not close `MERGE-EXPANSION-COVER-1` or `SourceProblem.InferenceSoundness`.
