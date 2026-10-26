# Independent review: original extrusion keys and captured fiber transfer

## Verdict

**PASS within the stated physical-key and first-fiber-loop boundary.** No
concrete source-correspondence, theorem-statement, proof, or axiom blocker was
found. Both actual imported targets passed independent direct checking. A
separate complete-origin audit checked all private and generated declarations,
all 25 authored theorem signatures, and every transitive axiom inventory.
This receipt does not claim complete native execution extraction, the direct
Work-step composition, whole-operation termination, or any of the four
original whole-language closure obligations.

The reviewer is the independent soundness/hygiene lane; the root authored
these two modules. The reviewer changed no proof source, dependency, Rust
source, shared status, import root, or Git state. The exact write lease was
this review and `/tmp/yulang-extrusion-fibers-review/` only. No child, shared
build, cache write, or `.olean` output was used. Parent-reported input HEAD:
`e7551b9`.

## Frozen inputs

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalExtrusionFibers.lean` | `15bb4ebc67a22f4bd3af584e8377dec210963f7cbba43e6072c82b5f2d5a8800` |
| `notes/theory/lean/YulangClosure/OriginalFiberTransfer.lean` | `2d368cfe99240d7c4a5cb7618acd7bedd3a569978735b27a1b3b23a1626566ba` |
| Final paired note `notes/theory/2026-10-27-original-extrusion-fibers.md` | `6b7178225ac1b299545c116d471c32338f5ad3aaf8574c800c0c8f1b75bd21b5` |
| Actual imported `OriginalExtrusionWork.lean` producer | `c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58` |

The original note hash was
`0f332d1cfd6b3e5e360e6e8faaf7ecb2cb363162d9fb1c76328844e36fee8e23`.
Initial and final copies plus their exact delta are retained in the scratch
review directory. Native-source and frozen dependency hashes are in
`input-manifest.json` and were reverified before this receipt was frozen;
`checks.json` records the final input hashes. Work's full operational machine
is a separate review target, not included in this audit's originating modules.

## Scope and source correspondence

The reviewer read all 253 lines of `OriginalExtrusionFibers.lean`, all 461 lines
of `OriginalFiberTransfer.lean`, all 202 lines of the original frozen note, and
the stable Work prelude through `BoundRequest`. The original prelude hash was
`4f807fe4e2b1d2a7c28672e2a219b1175daab2c0227d16f0bb4c16d17a28ca3b`;
the actual frozen producer prelude is
`943144668d3521d7b32d8ed9a2ae55aa333fd9129f96ac5ae760daa316ad5c86`.
The reviewer verified that only its top documentation comment changed and
that all remaining declaration bytes are identical. The initial note delta
updated actual verification metadata and the availability of the frozen Work
producer. A separately authorized correction then fixed one native-order
sentence, as recorded below. Both deltas were read; the two proof-source hashes
did not change. No provisional concatenation check is counted as imported-target
verification.

Native comparison covered `bound_pair`, `candidate_context_pair`,
`post_check_context`, `transported_scoped`,
`candidate_context_transport_witness_with_evidence`, `bound_cursor`,
`bound_entry`, and `candidate_transfer_bound_origins`. The snapshot,
dependency, evidence-transform, and edge/bundle publication bodies were also
read to confirm which state components their physical projection erases.
The relevant frozen `OriginalBoundFibers`, `NativeRelationInterner`,
`NativeValuePorts`, and `NativeContextExpansion` definitions and theorem
interfaces were checked. Those dependencies already have their own reviews;
this receipt does not replace them or audit the full Work machine.

## Complete key and original raw identities

`RawBound` retains both the owner and endpoint, their Value/Effect tags, and
polarity. `boundPair` implements positive `(endpoint,owner)` and negative
`(owner,endpoint)` for both kinds. A cross-kind input is an explicit
`kindViolation`; the note correctly identifies this as the native invariant
trap, not a new normal Rust availability error.

Pair canonicalization only changes row representatives. Structural Function,
Tuple, Record, Variant, atom, and non-row Effect identities are retained by the
existing endpoint-renaming definitions. The destination fiber key is the full
raw `request.destination`; it is not replaced by a canonical endpoint-pair
quotient. The computed child relation key has the complete pair, post-check
Context, original source-set ID, and scoped Flow.

`remapRoot` matches the actual owner-first two-position loop and its break.
If the original owner matches the old negative Function root, a wrong-kind
destination owner fails immediately; the matching endpoint cannot rescue it.
Only when the owner did not match is the endpoint considered. `remapFlow`
retains a missing demand as missing. For a present demand, all five fields
remain accounted for: the root follows that exact computation; original Call,
use instance, output scope, and input route are retained. The transformer is
also retained. The metadata lemma is not incorrectly presented as proof that
the root never changes.

The same raw parent RelationId selects its stored source key, discharged flag,
and discharge residual. A discharged parent without a residual uses native
IDENTITY=0. The source-set identifier is copied from that exact parent's key;
the theorem does not reconstruct it from endpoints or authenticate the
contents of an unrelated source set.

`Readout` contains raw representative/discharge observations. Authenticity of
those observations at a Rust cut remains an explicit source-extraction
obligation. The target/witness destination equality is satisfied by using the
same request destination in both roles. Transport reason, zero use-origin,
snapshot identity, and semantic provenance are outside the physical key/fiber
state and are not deduced from successful interning.

## Preparation and partial-error order

`prepare` evaluates the destination `bound_pair` before the snapshot gate.
This agrees with the native order: target/witness check, pure pair
canonicalization, evidence snapshot interning, scoped-flow transport, complete
relation interning, dependency publication, evidence transform, attachment,
and final sampling. Canonicalization uses fixed representative readbacks;
evidence snapshot interning changes neither the native relation store nor the
physical fiber vector, so recomputing the same pure pair in the suffix does
not move a state-changing operation across the snapshot gate.

Snapshot failure is distinct from a malformed-kind trap. Missing old parent
readback and root-remap mismatch remain key failures. `Store.Valid` proves
linked-table formation, not that every fiber's relation ID exists in the
native interner; a missing parent therefore cannot be silently converted
into a successful source key.

The existing physical suffix preserves native partial allocation when the
interner fails. Dependency or evidence failure retains the interner result;
attachment failure retains its actual physical state; sampling failure occurs
after attachment and retains the new fiber. Duplicate raw IDs follow the
existing exact-key interner and attachment scan. No rollback is invented
inside these forward runs.

The native snapshot/dependency/evidence methods do mutate their own metadata,
including counters and potentially partially prepared storage. Those fields
are deliberately absent from `Physical`; returning an unchanged physical
projection is not a claim that the entire Rust session was unchanged. Errors
or cancellation outside this call remain outside the forward suffix proof.

## Captured source head and saved-next loop

`transferBound` reads `state.fibers.heads request.original` once in the actual
computation. At each `some index`, `loop` reads the full stored entry, saves
`entry.previous`, obtains the current observations, and performs preparation
and transfer at that entry's exact raw relation ID. Recursion uses the saved
pointer. It never reads a new live source head, even if publication attaches
back to the source bound.

The recursive measure is the actual old pointer rank: None has rank zero and
Some index has rank index+1. Its decrease follows from `Valid.backward` at the
before-state lookup. The source is not a supplied completed list, and table
growth does not become a global identifier bound. All old entries and links
remain unchanged through the derived attachment runs.

`loop_complete_entries` requires the computed normal first-loop outcome and
then derives exact ordered equality with the initial captured list of
`(index,full entry)` pairs. `bound_complete` additionally derives the original
complete source-bound key on each entry. `loop_addressed` and
`bound_cursor_formed` rule out malformed cursor lookup from a formed native
head and its links without assuming normal completion. The explicit malformed
branch is not a claim that Rust indexed access returns an availability error;
its inaccessibility for the formed source is proved.

## Derived calls and the same physical child

The loop itself never receives `CallFacts`. Its recorded calls contain the
actual entry, before-state, observations, and child returned by the computed
native suffix. `loop_call_facts` derives the entry lookup, parameter equality,
snapshot success, computed successful child result, and both actual forward
suffixes. `call_delivered` consumes that derived certificate; `loop_delivers`
and `bound_complete` discharge it from the loop rather than moving delivery
into a caller premise.

The output key is witnessed by the same computation that interned it.
`transferred_fiber_exact` keeps the exact returned raw child ID both in native
readback and destination-fiber membership. Later iterations use forward native
and attachment runs to retain that same ID, key, and fiber. No independent
interner history or semantically equivalent child is selected at the end.

Delivery is proved for every recorded successful call even when a later call
fails. The failing call is not falsely recorded as complete; its partial
physical state remains in the result. Full initial-list coverage is concluded
only for the explicit normal first-loop outcome.

## Exact remaining application boundary

This packet proves the complete physical key and the first executable-fiber
loop. Its None-cursor completion is the cut before the native origin-metadata
loop. That later loop's missing origin-to-fiber association is preserved; it
is not used to manufacture extra executable fibers or coverage.

The direct `Work::Bound` / `External.bound` application remains separate.
These two modules consume the full `BoundRequest` data, but do not themselves
prove that it was produced by the selected native Work step. The frozen
`selected_bound_dispatch` and `bound_dispatch_from_pending` producer theorems
are now available, but composition must still retain physical insertion,
capture registration, evidence emission and insertion sampling before this
fiber loop, followed by the later origin-metadata loop. Starting the fiber
loop from an unrelated supplied physical state would not discharge that
application. Authentic
representative/discharge functions, snapshot/evidence and dependency records,
allocation/resource observations, and extraction from one real Rust history
also remain external owners. The native Context range, scoped-mode guards,
and allocation limits remain in the existing physical interner/resources
interface; this review does not replace those readbacks with semantic laws.

Totality of the Lean linked-control function is local. Its external operations
are represented by returned observations; the proof does not show that the
corresponding real calls terminate or succeed. It establishes neither a whole
native extrusion operation nor a first empty drain boundary, complete NQ,
Replay/dedup successor production, or growing inference accessibility. All
four original whole-language obligations remain open. No source restriction,
principal-instance order change, compiler edit, or source-level divergence
claim is introduced.

## Source-order correction after the first freeze

The first accepted note and this review's boundary paragraph incorrectly put
capture after the first fiber loop. The parent identified that documentation
error during the Work join. The reviewer rechecked the actual owners:
`candidate_extrusion.rs`'s `Work::Bound` calls
`candidate_insert_copied_bound` before `candidate_transfer_bound_origins`;
`candidate_insert_bound_with_evidence` performs the physical append, optional
`candidate_register_capture_bound`, evidence emission and sampling before its
return. The executable-fiber loop follows that return. The later
origin-metadata loop follows the fiber loop and is a separate owner.

Only the paired note's one ordering sentence changed. No target proof bytes,
theorem types, premises, or dependencies changed. The reviewed corrected note
hash is `6b7178225ac1b299545c116d471c32338f5ad3aaf8574c800c0c8f1b75bd21b5`.
The earlier note hash was
`8715cad8d34e6c48938a1661878b9a92efae2a4f1b4fb4eec27a0eb87993ba15`,
and the first review hash was
`1da0b93e0a183c55e990711701c8f865e101f83238cbb99fd00ac08c3d17c2c2`.
Their exact bytes, prior checks/freeze receipts, and the correction delta are
retained in scratch. This correction used **zero additional Lean invocations**;
the three actual check results below remain unchanged. The scoped PASS remains
valid after the documentation fix; the same-history native join remains open.

## Independent verification

The parent first supplied actual imports after a successful 15-job focused
build of Work and these two clients, with zero warnings or errors in
`/tmp/yulang-extrusion-client-build.log`. The checks below then used the real
frozen imports. Provisional concatenated-prelude checks were not counted.

Pinned executable:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake `5.0.0-src+eb6cafb`. Working directory for all checks:
`/workspace/scratch/dd0ca2ec982a/yulang/notes/theory/lean`.
Each invocation had a 120-second limit, used one worker, and wrote no `.olean`.

| Invocation | Arguments after the pinned executable | Exit | Seconds | Diagnostics |
| --- | --- | ---: | ---: | ---: |
| 1, direct key target | `env lean -j1 -M1024 YulangClosure/OriginalExtrusionFibers.lean` | 0 | 0.920 | 0 |
| 2, direct loop target | `env lean -j1 -M1024 YulangClosure/OriginalFiberTransfer.lean` | 0 | 1.929 | 0 |
| 3, full-origin audit | `env lean -j1 -M2048 --root=/tmp/yulang-extrusion-fibers-review /tmp/yulang-extrusion-fibers-review/Audit.lean` | 0 | 1.972 | 0 |

All three actual exits were directly observed and retained. There was no
failed compiler invocation in this packet. Three of four authorized checker
invocations were used; no additional optional check was performed. Default
target integration remains parent-owned and is not asserted by this receipt.

The audit selected constants by their actual imported module origin using
`getModuleIdx?` and `getModuleIdxFor?`, rather than by public namespace or
source-text name matching. Complete explicit types and transitive axiom sets
were emitted for every originating constant, including private, generated,
recursive, and constructor-related constants. The 25 authored roots also had
explicit `#check @...` and `#print axioms ...` checks. All authored theorem
types were read; the complete census has no elided type or placeholder. No
originating axiom declaration, `sorryAx`, project axiom, or additional axiom
outside Lean's listed standard axioms was accepted.

| Module | All originating declarations | Theorem constants | Authored roots |
| --- | ---: | ---: | ---: |
| `OriginalExtrusionFibers` | 113 | 35 | 10 |
| `OriginalFiberTransfer` | 240 | 101 | 15 |
| Total | 353 | 136 | 25 |

| Transitive axiom set | All declarations | Theorem constants | Authored roots |
| --- | ---: | ---: | ---: |
| None | 207 | 64 | 1 |
| `propext` | 98 | 36 | 4 |
| `propext`, `Quot.sound` | 42 | 30 | 14 |
| `propext`, `Classical.choice`, `Quot.sound` | 6 | 6 | 6 |

The 10 key-module roots cover metadata retention, complete transported-key
formation, physical validity, same-child publication, captured source,
forward native/fiber/history preservation, old readback, and existing fibers.
The 15 loop roots cover preparation, computed completion, forward-run
composition, footprints, old readback, preserved and captured fibers, exact
normal entry coverage, derived call facts, same-child delivery, complete bound
application, addressed cursors, and formed initial heads. Full exact types and
per-root axiom groups are in `authored-theorem-types.json` and
`axiom-groups.json`; the all-origin inventory is `complete-census.json`.

## Evidence and stop receipt

All evidence below is in `/tmp/yulang-extrusion-fibers-review/`.

| Evidence | SHA-256 |
| --- | --- |
| `direct-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `direct-02.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Audit.lean` | `f3e39aabd32ff32da141fa86283760a96240717c7a795bbb16c07abc19eb8bd3` |
| `audit-03.log` | `48be25e1b4ea03ee228ef36b1cd866f602b2f636ab9cce5a7357cd5f65da198f` |
| `audit-03.json` | `34299bc650b8eac32980f4a513bc5b1297ca1225d3148430f6c8d224a931de4c` |
| `complete-census.json` | `7fe8ac6fd821fef5d4eae5e6dbc8d3d6a39c4d65876613b49b29196d2f947c6b` |
| `authored-theorem-types.json` | `09a62547ddb5fe93064acda122411dcd6f6596e6185064966aa7d322c97efb75` |
| `axiom-groups.json` | `58c489670207f715cc88a61c1aab7b076d3fef1b4fde0570d8698921baa5881e` |

`direct-01.json`, `direct-02.json`, and `audit-03.json` record the actual
commands, exits, and durations. `checks.json` consolidates the final input
hashes, census, axiom groups, command evidence, and remaining scope.
`freeze.json` records the final receipt hash and completed-stop metadata.
No checker remains active. Proof-source bytes and all previous leases remain
frozen. **WRITES_STOPPED** after the timestamp below; further work requires a
new parent assignment.

First freeze: 2026-10-26T22:51:25.978820+00:00.

Ordering-correction freeze: 2026-10-26T22:59:37.193533+00:00.
