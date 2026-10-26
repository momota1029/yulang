# Original extrusion fibers: complete keys and the captured-source loop

Date: 2026-10-27. Producer: `/root`. Branch: `yulang3`.
Parent: the selected-copy step of the original native first-empty obstruction
and, ultimately, the unchanged original inference-accessibility obligation.
Both parents and all four original whole-language goals remain OPEN.

The two modules compute the physical relation key and the first executable
fiber loop in `candidate_transfer_bound_origins`. They use the complete
`OriginalExtrusionWork.BoundRequest` and the already reviewed
`OriginalBoundFibers` native interner/attachment suffix. No semantic
equivalence class replaces a raw relation ID, and no source-list coverage or
post-call fiber membership is supplied by a caller.

## Frozen proof surface

| Module | SHA-256 |
| --- | --- |
| `lean/YulangClosure/OriginalExtrusionFibers.lean` | `15bb4ebc67a22f4bd3af584e8377dec210963f7cbba43e6072c82b5f2d5a8800` |
| `lean/YulangClosure/OriginalFiberTransfer.lean` | `2d368cfe99240d7c4a5cb7618acd7bedd3a569978735b27a1b3b23a1626566ba` |

Proof bytes are frozen. Verification is currently a successful provisional
check against the producer's exact saved data declarations. Real imported
target checks, full audits and independent acceptance are pending the
extrusion Work producer's final build. This distinction must remain visible
until those gates complete; the provisional file is not a completed Work
audit or default integration result.

## Native source owners

The source files are `crates/yu-solver/src/candidate_context.rs`, SHA-256
`57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`,
and `crates/yu-solver/src/candidate_effect.rs`, SHA-256
`70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f`.

| Owner | Computed content |
| --- | --- |
| `bound_pair`, around 3311 | Both endpoint kinds, the positive/negative swap, and the malformed cross-kind case. |
| `candidate_context_pair`, around 3349 | Canonical row representatives on both endpoints; non-row terms retain their raw identities. |
| `post_check_context`, around 3297 | The same raw parent's original Context, or its discharge residual with the actual IDENTITY=0 fallback. |
| `transported_scoped`, around 2867 | Owner-first, then endpoint, negative-Function root replacement. A malformed first match fails immediately instead of trying the second position. |
| `candidate_context_transport_witness_with_evidence`, around 4320 | Complete-key construction, actual native interning, dependency/evidence publication, linked attachment and resource sampling, with partial-error order. |
| `candidate_transfer_bound_origins`, around 685 | Capture one source head, read `(parent,next)`, save `next` before the body, and continue from that pointer rather than a new live head. |

The native witness's destination check is an equality for this constructed
request: the same `request.destination` is used as the target and the witness
destination. Transport reason, zero use-origin, snapshot identities,
dependency/evidence records and accounting remain outside the physical
interner/fiber state. They are not inferred merely from complete key equality.

## Complete relation key

`OriginalExtrusionFibers.boundPair` preserves the full owner, polarity and
endpoint of Value and Effect bounds. Positive bounds produce `(item,owner)`;
negative bounds produce `(owner,item)`. A cross-kind raw key is represented
as `kindViolation`, corresponding to the native invariant trap. This does
not claim that Rust returns a normal availability error for malformed kinds.

`remapRoot` implements the native two-position loop, including its `break`.
If the original owner is the old negative-Function root, the destination
owner must be a negative Function; a mismatched owner cannot be bypassed by
finding a later matching endpoint. Otherwise the endpoint is checked, and
otherwise the original root remains. `remapFlow` preserves the absence of a
deferred demand. For a present demand it changes only that computed root.

`remap_flow_metadata` preserves the transformer and all four other demand
fields: original Call, use instance, output scope and input route. Thus the
complete five-field deferred demand is retained with the one explicitly
computed root replacement. The source-set field is read unchanged from the
same parent relation, not reconstructed from endpoints.

`Readout` contains the actual Value/Effect representative functions and the
discharged/residual maps. Their authentic correspondence to a Rust cut is
still external. `postContext` uses the **same raw parent ID** to select both
discharged status and residual. No separate Context witness may be selected
for the child.

`transportKey` reads the parent's complete native key, computes the pair,
Context, source set and scoped Flow, and returns the entire `NativeValuePorts.Key`.
`transport_key_exact` inverts that computation. `transfer` then invokes the
already reviewed physical suffix with that very key and destination.
`transferred_fiber_exact` derives all of the following from its computed
normal outcome and the existing native history:

1. the actual source key read at the parent ID;
2. the computed bound pair, root remapping, post-check Context and complete
   resulting key;
3. the existing native `Allowed` guard for that whole key;
4. readback of the returned raw child ID equal to that key;
5. membership of the same child in the actual destination's linked fibers.

`transfer_native_run` and `transfer_fiber_run` derive forward footprints for
**every** outcome. `transfer_history`, `transfer_old_readback` and
`transfer_preserves_fiber` retain earlier keys and fibers through later calls.
Partial interner allocation, attachment followed by sampling failure, and
duplicate reuse follow the existing suffix; no rollback is invented.

## Actual captured-fiber loop

`OriginalFiberTransfer.State` packages the physical state with its existing
linked-table formation proof and native interner history. These are physical
starting-state invariants, not source typing, Replay completion, or a whole
drain certificate. Every body result constructs the corresponding after-state
invariants using the actual `transfer` theorems.

`Parameters` contains the observed snapshot-interning outcome, fixed raw
readouts and the suffix resources. `Inputs` supplies those observations for
the current physical state, captured index and parent ID. It does not supply
a child ID, completed call, target membership or semantic safety predicate.
The snapshot operation's internal evidence table is not represented.

`prepare` checks the actual `bound_pair` kind case before the snapshot gate,
matching the native order. Canonicalization is a pure operation on the fixed
representative readout; the snapshot's projected evidence operation does not
write the native/fiber fields. The suffix computes that same canonical pair.
An unsuccessful preparation stops before interning. The mismatch/trap and
snapshot-failure cases remain distinct from normal completion.

`loop` performs the actual linked control:

1. `none` returns at the first loop's own cut, before origin metadata.
2. `some index` reads the entry from the current physical vector.
3. It saves `entry.previous` before preparation or publication.
4. It performs preparation and the complete physical transfer at
   `entry.relation`.
5. On success it records that actual index/entry/child and continues from the
   saved pointer. On failure it returns the actual partial physical state.

The recursive decrease is `cursorRank none = 0`,
`cursorRank (some index) = index + 1`. It follows from the existing stored
older-pointer invariant at the **before** state. Body attachments may add
arbitrarily many new entries, including entries at the same source bound;
they do not change the saved next pointer. No fuel, global identifier cap or
preselected finite sequence replaces the native chain.

`loop_footprints` derives the actual finite native-call and attachment suffixes.
`loop_captured_cursor` preserves the complete old linked readout;
`loop_old_readback` and `loop_preserves_fiber` retain earlier raw children.
`loop_addressed` and `bound_cursor_formed` prove that the explicit malformed
index case is unreachable from an actual formed source head and its links,
without assuming normal completion of the loop.

`loop_complete_entries` proves that normal completion records exactly the
initial captured `(index,full entry)` list, in order. `CallFacts` is a derived
certificate of a computed call: actual entry read, exact parameters,
successful snapshot and native call, and the actual forward suffix. The
executable loop never receives a `CallFacts` premise. `loop_call_facts`
constructs it for every recorded call, including calls preceding a later
failure. `call_delivered`/`loop_delivers` then retain the child's full computed
key and target fiber membership through that suffix.

`transferBound` captures `state.fibers.heads request.original` in the
computation itself. `bound_complete` combines exact initial-list coverage,
the original complete source bound key on every entry, all computed call
facts, and every delivered full child key. It does not assume source-list
coverage or successful child membership separately. This is the first loop
only: the native later origin loop explicitly has no origin-to-fiber
association and is not turned into an executable fiber source here.

## Remaining original applications

The direct Work-step composition must apply this computation to the exact
`External.bound` request produced by the selected native `Work::Bound`.
The producer's `selected_bound_dispatch` and `bound_dispatch_from_pending`
are now frozen and checked in `OriginalExtrusionWork`; these two modules
currently take its complete `BoundRequest` as data. The remaining composition
must retain the physical insertion, capture registration, evidence emission
and insertion sampling before this fiber loop, and the later origin-metadata
loop after it. A loop from an unrelated supplied physical state would not
establish that native Work execution.

Authentic raw representative/discharge readouts, snapshot/evidence and
dependency machinery, real allocation identities, resource observations,
and extraction of all these projected operations from the same Rust history
remain separate owners. `Store.Valid` alone does not make every old fiber ID
a valid native relation. A missing old parent causes the explicit key failure;
normal complete coverage therefore cannot manufacture a source key.

The recursive definition proves totality of this projected linked control
with returned observations for the external body operations. It does not
prove that all real external operations return, that all selected extrusion
work succeeds, or that a first empty drain boundary exists. Replay/dedup
publication, the exact NQ successor step and whole growing inference `Acc`
remain open. No original SourceProblem instance, language restriction,
semantic principal order, or runtime termination assertion is introduced.

## Verification at the current freeze

The exact provisional producer prelude was copied from the real
`OriginalExtrusionWork.lean` through `BoundRequest`, before `inductive Work`.
Its SHA-256 is
`4f807fe4e2b1d2a7c28672e2a219b1175daab2c0227d16f0bb4c16d17a28ca3b`.
No replacement data semantics or checked conclusion was added. The isolated
scratch check concatenates that prelude with these exact two source bodies
and imports the compiled frozen `OriginalBoundFibers`.

All checks use pinned Lean 4.35.0, `timeout 120`, `-j1 -M1024`, no `-o`, under
`/tmp/yulang-extrusion-fibers-interface/`. Key checks 1–3 retained real
monadic-reduction/dependent-match failures and the final successful extension.
Loop checks 1–11 retained syntax/dependent-case repairs, the preparation-order
correction, and removal of constructor-like local variable lint. The frozen
final `loop-check-11.log` is empty, exit 0. This is a kernel check of the exact
client definitions/proofs, not of the producer's full Work machine.

The real frozen producer has SHA-256
`c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58`.
Its prelude through `BoundRequest` has SHA-256
`943144668d3521d7b32d8ed9a2ae55aa333fd9129f96ac5ae760daa316ad5c86`;
only the top documentation comment differs from the provisional prelude.
The data declarations are byte-identical. The actual three-module build
completed successfully, **15 jobs, zero warnings or errors**, in
`/tmp/yulang-extrusion-client-build.log`.

Independent direct checks against those real imports accepted both frozen
clients with empty diagnostics. The separate full-origin audit accepted
**all 353 originating declarations**, including **136 theorem constants**:

| Module | All declarations | Theorem constants | Authored theorems |
| --- | ---: | ---: | ---: |
| `OriginalExtrusionFibers` | 113 | 35 | 10 |
| `OriginalFiberTransfer` | 240 | 101 | 15 |

Every declaration, including private and generated constants, has a complete
printed type and transitive axiom inventory. The 25 authored roots use no
axioms (1), `propext` (4), `propext` plus `Quot.sound` (14), or those two plus
`Classical.choice` (6). No additional axiom, elided type, checker bypass or
project axiom was accepted. The audit command used `-j1 -M2048`, the same
pinned Lean, and a 120-second bound; it exited 0 in 1.972 seconds.

The independent evidence is under `/tmp/yulang-extrusion-fibers-review/`:
`direct-01.log`, `direct-02.log`, `Audit.lean`, `audit-03.log`, complete census
and axiom manifests. The review receipt is
`../progress/2026-10-27-extrusion-fibers-review.md`. Default-target integration
is recorded separately in the parent progress ledger when performed. These
actual imported checks supersede the provisional interface-only evidence;
none of them closes an original whole-language root.
