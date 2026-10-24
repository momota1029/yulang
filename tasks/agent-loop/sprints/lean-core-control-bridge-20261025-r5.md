# LEAN-CORE-CONTROL-BRIDGE-20261025/r5

Continuation after r4's primary Lean check advanced from `ControlTyping` to
`ControlComposition`. The unchanged full Yulang semantics/type-inference,
source/native and original A/B parent remains OPEN.

## Frozen r4 checker result and snapshot

The pinned command `timeout 60s lake build YulangClosure.CoreControlBridge`
accepted `ControlTyping.lean` and failed in `ControlComposition.lean`. Actual
diagnostics identify three repair points: (1) the `request_progress` mapper
case projects `.source` from a `MapperTyped` proof instead of the indexed
mapper value; (2) `segment_progress` still rewrites head/stack projections
into a target containing the whole state record; (3) `progress` refers to
request packet and failure-reason identifiers that are not in scope after
dependent cases. These are elaboration/proof-structure blockers, not source
counterexamples. The bridge module itself has not yet been checked.

Before r5 edits, the exact r4 bytes were preserved read-only at
`/tmp/yulang-lean-core-control-r4-20261025/`:

| Artifact | SHA-256 |
|---|---|
| `ControlTyping.lean` | `67e0d5d8840090ad7adf06b33c65725dc0901488c16f9dcc235c5c0372ae0135` |
| `ControlComposition.lean` | `a6c7402204bb54db9f074b59b609b74e2f0f7d7d10f5fb33fe2b406a6979929a` |
| `CoreControlBridge.lean` | `95cad83ee84e767aecd6314f84e983db40a9efba1e8322c6f54ee79d45c3cfad` |
| `ControlSyntax.lean` | `801f5ff354d0546aaca6fbd353cf261d3e49c915f78687d76167eab7b9aa8bc9` |
| `YulangClosure.lean` | `5af826a59689a21294b36f361df95cceae8dc78b674c523e789a0e7e7bc1614d` |
| r4 repair handoff | `7dd2f3af2e484b7d2cedaed7624496699add3ae5ff99ac081089e285b9e8af1d` |

The r4 writer STOPPED with no descendants. Its full 90-second grant remains
charged because actual elapsed time is UNKNOWN. The next bounded work is
primary-owned; no old writer lease is active.

## Exact primary repair and integration scope

Luna receives the sole write lease for:

- `notes/theory/lean/YulangClosure/ControlComposition.lean`
- `notes/theory/lean/YulangClosure/CoreControlBridge.lean`, only if the newly
  checked proof directly requires an elaboration repair preserving its
  statements, transitions and quantifiers
- `notes/theory/lean/YulangClosure.lean`, for the bridge import and requested
  axiom receipts after the module builds
- `tasks/agent-loop/current.json` and the r3 outcome receipt

`ControlTyping.lean` and `ControlSyntax.lean` are frozen r4 dependencies. Repair
the mapper case by separating the actual mapper value from its typing proof;
normalize/substitute the state-field equalities before constructing each
`segment_progress` successor; and name the packet/reason across dependent cases
in ordinary `progress`. Preserve the existing ordinary theorem statements and
domains, the four frozen source transitions, source syntax/substitution, all
suffix quantifiers and the finite source/exit/foreign trace split. No new
transitions, source constructors, safety assumptions, tags, holes, unsafe proofs,
project axioms or native decision escapes.

## Reallocated resource envelope

Prior grants reserve 3,400 seconds. Recorded checks used 4.7 seconds and about
3.5 seconds; the r4 writer's 90-second grant is fully charged. This leaves
101.8 seconds under the frozen 3,600-second cap. Reallocate that remainder
without resetting or reclaiming earlier grants:

| Work | Owner | Maximum |
|---|---|---:|
| Mechanical repair and root integration | Luna | 35 s |
| Serialized pinned check and axiom receipts | Luna | 20 s |
| Fresh independent compiler referee | nonauthor reviewer | 40 s |
| Unallocated reserve | — | 6.8 s |

Only one Lean/Lake process runs at a time. Use pinned Lean 4.35.0 with
`-j1 -M1024`. Within 20 seconds, build the bridge target and the root target
after importing the bridge. Record `#print axioms` for
`successor_coverage`, `machine_finite_coverage` and `finite_closed_safety`,
then scan the reviewed dependency component for proof holes, unsafe proofs,
project axioms and native decision escapes. No tests, Cargo or native probes.
If a mathematical obstruction appears or the allocation expires, stop and
record exact diagnostics; do not spend review time on more construction.

Freeze the repaired hashes and checker receipts before assigning a fresh
nonauthor `compiler_referee`. The reviewer checks theorem domains, typed
segment witnesses, all embedded successors, suffix retention, actual
substitution, finite trace decomposition, axiom output and proof-hole scan.
Any blocker leaves bridge acceptance OPEN. All source initialization, other
constructors, native correspondence, source-scoped inference, coverage,
principality, termination and original A/B obligations remain OPEN.

Luna owns scheduling records, primary adjudication, exact Git staging, commits
and ordinary non-forced pushes. Preserve the three unrelated
UNKNOWN_QUARANTINED reservations. The next dispatcher consultation is a new
proof/interface obstruction, the frozen review seam, or the resource boundary.
