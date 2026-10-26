# Native physical inventory construction — frozen handoff r1

Assignment: `/root/native_inventory_construction`
Parent/integrator: `/root`; baseline supplied `bf81a1bd444b3bcbecca6b754ea6fb603262f368`, branch `yulang3`
Outcome: source/native evidence plus paper extraction proof; independent review pending
Requested role: generic prover/native correspondence leaf. Observed worker ID as above; actual model/effort not exposed by task tools, UNKNOWN.
No descendants, Git operations, shared status/import edits, semantic changes or expectation changes.

## Result applied to the original parent

The original source inference A/B claim remains that of
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1 with the
2026-10-24 birth-level SCC correction. Source scope, one joint witness,
original complete Call, effects, publication, required coverage and ordinary
inference behavior are unchanged.

The new concrete adapter reads every native physical row and all eight actual
bound lanes, retaining `(raw owner, lane, index)` and exact original endpoint
separately from the current canonical endpoints. It normalizes lower lanes to
`item ≤ owner` and upper lanes to `owner ≤ item`; thus both native one-sided
row-storage choices contribute to one comparison universe. It joins actual
emission IDs by physical address and preserves all retained admissions,
coverage gaps, snapshots, transports, recipes, dependencies, live replay and
restoration frontiers, original parent indices, groups, all later reuses and
source qualification identities. It borrows actual module/local/operator/member
FreshUse route records, preserving their common row maps and use IDs. It reads
all reachable native TermViews from physical and retained relation endpoints;
Function value/effect ports, tuple order, record labels/optional bits and
variant payloads remain explicit. Effect view/contribution/capture identities
remain attached to their native records.

The paper proves the finite address bijection by the concrete nested loops and
proves the lower/upper normalization equation. It follows the actual append,
readback, copied-bound transport and activation branches. This removes a
representation/reconstruction premise; it does not construct the semantic
canonical-row assignment or show final computed decision acceptance.

Completed operation records may be reclaimed. That only blocks an inverse
from a final snapshot: a finite actual execution supports a ghost event list
with append/read/child/acknowledgment/commit/rollback events. No new runtime
history storage is proposed. Establishing that trace's semantic history and
full original source publication remains a distinct original owner.

## Exact writes and grants

Original exact leases were the new paper and this inbox, optional new
`NativeBoundInventory.lean`, and isolated scratch. After a precise proposal,
the primary granted only the new
`crates/yu-solver/src/candidate_native_inventory_tests.rs` plus the appended
`cfg(test)` path-module declaration in `candidate_context.rs`. No accessor was
widened and `lib.rs` was unchanged. Readback proves the existing context file
is its saved initial bytes plus exactly the new five-line test declaration.

The primary initially granted two focused Cargo runs at 120 seconds/4 GiB.
After both compilation timeouts, it explicitly granted one final identical
source/target/profile run outside the sandbox with a 240-second bound. This
was a measured validation-bound revision, not permission to expand tests.

The proposed extra saved-count/live-index fixture was canceled by the primary
before any write/run. The paper reuses the reviewed
`2026-10-13-restoration-live-index-pair-audit.md` and
`2026-10-13-restoration-temporal-coverage-proof.md` under their actual scopes.
It neither reports that known selected behavior as a new bug nor changes the
restoration implementation.

## Actual checks, including failures

Toolchain readback:

```text
rustc 1.99.1 (58cf8f9c3 2026-10-13)
cargo 1.99.1 (5f94df478 2026-08-27)
```

All three focused commands had this argument vector after the pinned binary:

```text
test --locked -p yu-solver --features shadow-apply-candidate --lib candidate_context::native_inventory_tests:: -- --test-threads=1 --nocapture
```

Owned target:
`/workspace/scratch/f98087c7ac1a/inference-native-inventory/target`.
One build job and one test thread; offline cached dependencies; 4 GiB
per-process address-space bound; process-group termination on timeout.

| Run | Timeout | Actual elapsed | Result |
| --- | ---: | ---: | --- |
| 01 | 120 s | 120.061273 s | timeout; process group killed; no test executed |
| 02 | 120 s | 120.017975 s | timeout; process group killed; no test executed |
| 03 | 240 s | 52.956683 s | exit 0; 1 test passed, 815 filtered, 0.01 s test body |

Run 01 used the default profile and rebuilt dependencies. Runs 02/03 used
`CARGO_PROFILE_TEST_DEBUG=0`, `CARGO_PROFILE_DEV_DEBUG=0`, `CARGO_INCREMENTAL=0`.
Run 03 used `require_escalated` under the explicit primary grant and the same
343-line adapter/context bytes as run 02. No compiler errors were reported in
the timed-out runs, but they are not accepted checks. No timeout cause is
asserted. All logs and JSON receipts remain separate.

The passing fixture uses actual native insertion, replay, extrusion,
source-event qualification and merge owners. It constructs its typed inputs;
it is not an entire original source-generated acceptance path. It checks:

- all eight lane kinds are nonempty;
- exact physical cardinality, unique slot addresses and independent native-vector readback;
- actual `candidate_opposite_count` and `candidate_opposite_bound` ordering, before and after aliasing;
- exact emission/readback/admission joins;
- four distinct Function ports, including the two effect ports;
- mutant rejection after missing slot, swapped value ports, swapped effect ports, and missing Replay dependency;
- raw versus canonical row distinction and actual `ParentCopy` transport.

Exact final fixture census:

```text
NATIVE-INVENTORY slots=18 emissions=18 terms=10 dependencies=76 parents=6 groups=1 reuses=0 generation=6
```

Zero reuses establishes no all-history qualification claim. Live replay records
are exercised; complete restoration and all captured use families are not
claimed to be exercised. The final compiler output has 19 yu-solver warnings,
all on existing source locations; the new module adds none.

## Type/theorem inventory and proof boundary

No Lean file was created, no Lean command was run, and no Lean theorem/axiom
closure is claimed. All-origin Lean declaration inventory for this packet,
including private/generated constants, is therefore empty. No root import,
`.olean`, Lean dependency or checker configuration was changed.

The 343-line Rust module has these named declarations (all inside the new
`candidate_context::native_inventory_tests` test module):

| Declaration | Exact role/type |
| --- | --- |
| `PhysicalEntry` | raw addressed bound, canonical bound, typed comparison, emission IDs |
| `Provenance<'a>` | borrowed native evidence slices and live replay/restoration records |
| `RowEntry` | raw row, representative, level, non-generic flag |
| `Inventory<'a>` | finite physical/structural/provenance/use snapshot |
| `context` | `(&InferenceSession) -> &State` |
| `row_endpoint` | `(RowKey) -> ExtrusionEndpoint` |
| `comparison` | `(BoundKey) -> TypedPairKey` |
| `physical_read` | `(&InferenceSession, PhysicalBoundSlot) -> Option<BoundKey>` |
| `endpoint_term` | `(ExtrusionEndpoint) -> Option<Term>` |
| `inventory` | `(&InferenceSession) -> Inventory<'_>` |
| `validate` | `(&InferenceSession, &Inventory<'_>) -> Result<(), &'static str>` |
| `session` | `() -> InferenceSession`, fixture constructor |
| `physical_inventory_preserves_lanes_ports_replays_and_aliases` | one native correspondence/falsification test |

Derived Rust traits are compiler-generated equality/debug/clone plumbing, not
proof constants. The finite-map/address proof is explicitly paper-only and tied
to the actual eight loops; it is not a generic Lean list theorem relabeled as
native correctness.

## Exact remaining boundary and owners

1. Model lane: construct one interpretation of canonical rows and native
   structural endpoints in the semantic graph, consuming both physical sides.
   Raw IDs and normalized inequalities are not semantic nodes.
2. Saturation/history lane: apply established whole-block temporal coverage
   under its exact premises, then discharge shared-row, effect, contextual,
   alias/merge and full physical-incidence cases. The adapter retains actual
   reads/frontiers and does not equate saved count with old-slot coverage.
3. Source/publication lane: prove complete constructor/clause/metadata coverage,
   actual live/capture stopping, one common FreshUse map, and lawful original
   scope transport. Source completion observation may be omitted on allocation
   pressure; absent records are not silently reconstructed as successful ones.
4. Original Call/source owner: construct the full original witness and its
   binding to the native interpretation, preserving all child/primitive/arm
   quantifiers. `finish_candidate` availability is not this witness.

No source-domain narrowing, new semantic rule, runtime checking pass, durable
history architecture, native Ok proof, principality, termination or production
promotion is proposed.

## Frozen artifacts, hashes and cessation

The final hash manifest is
`/workspace/scratch/f98087c7ac1a/inference-native-inventory/final-hashes.json`.
It includes every output, all consulted direct source hashes, preserved before
context bytes, all three full logs and their JSON receipts, and both runner
scripts. The input manifest records baseline `candidate_context.rs` SHA-256
`33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5`;
its expected final test-module-only hash is
`57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`.
The adapter hash is
`6b3670e5548ad0000c4717949476a3a3038b2e06490f7f58ed4c6a1ac522d638`.
All other original owner inputs were rehashed unchanged.

Scratch directory contains the owned build cache, runners, logs/receipts,
`candidate_context.before.rs`, input/pre-freeze/final hash manifests. No scratch
file is a production artifact. No descendants or checker process remain.
All repository and scratch writes stop after the final hash readback. Primary
owns fresh independent review, final status, integration, commits and pushes.
