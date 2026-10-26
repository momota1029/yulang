# Constructed evidence through growing regular histories

Producer: primary `/root`. Original baseline `eb3eef2f6a29d9c2a6132d648866c60900db276c`.
Source: `notes/theory/lean/YulangClosure/SimpleSubGrowingInference.lean`.
SHA256: `865b9eb4a64962182a22a9e507b98b1e7ab92ac143e4cbfea0b8570e39bb58ce`.
The original full `SourceProblem.InferenceSoundness` is unchanged and OPEN.

## Decisive connection

The previous structural history fixed one graph throughout. `GrowingHistory`
now interleaves the actual existing `ConstraintStep` constructors with literal
per-kind table-prefix growth. Its constructors assume neither a semantic
preservation law nor a satisfying model. `GrowingHistory.extension` derives
the accumulated prefix extension. `GrowingHistory.flatten` lifts each earlier
step into the final graph using the proved extension transport and constructs
one actual original `ConstraintHistory` there. No allocation overwrites an
existing node or numeric reference; this is not arbitrary mutable-row simulation.

`completed_growing_store_sound` first runs the executable graph completion,
derives successful original decoding, lifts that decoding along the accumulated
extension, and reflects the computed terminal decision through the flattened
history. `completed_growing_publication_with_clients` additionally derives
every original publication image using the existing scoped-publication theorem.
The conclusions use exactly one final graph and the same reference pullback for
all original publications and clients.

No external terminal certificate, decoder-success equation or pre-flattened
final-graph history is an input. Remaining inputs are explicit initial graph
validity, lookup/shape/label legality, finite target coverage, captured/current
guard and stopped-dependency conditions, an actual locally indexed growing
history, and success of the computed terminal decision. Actual native inference
success producing these data is not assumed to have been proved.

The example decomposes a cyclic Function in the old graph, allocates a fresh
tuple node, adds and discharges a constraint on that fresh node, and computes
the terminal evidence. The original comparison is recovered in the final
graph. Both effect ports and the original cycle identities are retained.

## Frozen dependencies and independent review seam

The eight earlier inference modules are unchanged from the original baseline.
New direct modules, already independently accepted by separate nonauthors:

| Dependency | SHA256 |
| --- | --- |
| `SimpleSubRegularDecision.lean` | `6b6e5e6f1c45140d935e1aa29fba4c1303ae89cd91fd6e1cde0d37387148db8d` |
| `SimpleSubRegularGraphExtension.lean` | `0b45d0e6d58701cba9f7df00d2a63897327e357ed3047b36e96d8fb6c49893d8` |
| `SimpleSubRegularCompletion.lean` | `d7231d0a3695dba7f3102e5fe235d4d26e34cad78870dbdbae9b7633c42787aa` |

The review should check local-to-final history lifting and exact reference
identity, the two newly eliminated construction inputs, and honest remaining
native/source boundaries. It need not repeat already accepted unchanged
dependency proofs or rerun the checker without a concrete new concern.

## Verification

Own isolated project/cache: `/workspace/scratch/f98087c7ac1a/inference-decision`.
Pinned native Lake/Lean 4.35.0 at the same verified path as the Decision packet.
One thread, `-j1 -M1024`, 120-second timeout per call.

- `growing-check-01.log`: requested module plus dependencies, exit 0,
  13 jobs, 4.940 seconds. No failed construction check or new warning.
- `growing-audit-02.log`: every originating theorem, exit 0, 1.021 seconds.
  **11 constants = 10 authored theorems + 1 generated recursor theorem**.
  All complete printed types and axiom lists were inspected: 7 only `propext`,
  4 `propext, Quot.sound`. No additional axiom or unchecked evaluation.
- Audit SHA256:
  `83ec5f4630b6f6ad9dc95e04eaa98edaff80c7083d62cb1da2a5bc23b686e4b3`.

No compiler, old proof source, dependency, global configuration or other worker
output was changed. Source is frozen and no owned process remains running.
The primary retains integration/status duties on separately owned paths.

## Exact remaining scope

This theorem interprets the represented structural fragment. Lattice/alias and
native open-row/ordinary-coalescing behavior, native physical-bound and activation
trace correspondence, actual canonical-row interpretation and whole source
Call/effect reconstruction are not discharged. Literal append-only growth does
not justify arbitrary mutation or overwriting old graph nodes. The separate
lattice certificate extension is not silently consumed by these regular roots.
