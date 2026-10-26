# Native extrusion Work: computed local producers

## Status and exact claim

This packet supplies a checked, executable projection of the local `Work`
loop in `crates/yu-solver/src/candidate_extrusion.rs`. It proves structural
work priority, early row memoization, selected old-bound scheduling, exact
four-port Function keys, a concrete three-step row-to-`Work::Bound` producer,
and a concrete Function rebuild including post-publication sampling failure.
The namespace is `YulangClosure.OriginalExtrusionWork` (abbreviated `W` below).

It does **not** establish NQ, inference termination, a completed source
extrusion, an anchored successor, or an infinite execution. The original
inference-termination obligation remains open. Program evaluation termination
is not being claimed: ordinary recursive programs may diverge independently
of inference behavior.

The parent claim is NQ in
`2026-10-26-native-copy-quiescence-obstruction.md`, especially §§5.1, 5.3 and
6.1. Section 6.1 requires the actual negative copy of a high argument row,
the actual four native ports, and the selected `Work::Bound` operations that
will transport fibers along the copied upper path. This file supplies local
producers for that construction. It stops at precise external owners instead
of representing a fiber, complete path, successful drain, source extraction,
or successor as a field of a certificate.

Frozen Lean source SHA-256:
`c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58`.
The source has 1,092 lines and 41 authored theorems. The note remained writable
until the final audit and handoff; its final hash is reported separately.

## Operational representation and source correspondence

The state retains both Value and Effect bound vectors and their levels,
representative readouts, operation-local row/structure memos, both actual
stacks, aggregate child ports, parent records, and term cells. The root
`Operation` retains the initial endpoint, polarity, target, occurrence,
processing raw `RelationId`, complete `NativeValueStructure.Request`, source
handle and qualification readout. It does not replace the native caller by
an endpoint pair. Qualification and source association are input readouts;
this module does not derive them from the native source reference table.

`Endpoint` reuses the existing native Value and Effect endpoint constructors.
`RawBound` retains owner, polarity and endpoint without quotienting the raw
selected source key. `BoundRequest` contains three different objects:
`original` is the exact physical source key; `insertion` has the copied owner
and memo-selected copied endpoint; `destination` applies the current native
representative readout to that insertion. It also carries the complete
`Operation` and `capture = true`.

| Native owner or loop | Local definition and represented behavior |
| --- | --- |
| `candidate_extrude` entry and `Key` | `initializeLocal`, `start`, `CopyKey`; fresh local memos, exact polarity/target, canonical initial endpoint |
| `work.pop().or_else(|| pending_bounds.pop())` | `select`; structural stack always wins, with a separate pending stack |
| `Visit` memo test | `visit`; either memo hit skips the visit; subsequent lookups prefer the row memo |
| Low row visit | Selected level at or below target remembers the original row, without traversing its bounds |
| High row visit | `copiedRow`; checked row ordinal, new target-level row, retained parent, row memo, opposite-side source link, then pending selected bounds |
| Direct/exact bound vectors | `selectedValue` and `selectedEffect`; direct rows precede exact atoms, positive chooses lowers and negative chooses uppers |
| Reverse selected-bound loop | `boundJobs`, `scheduleBounds`; each raw source bound produces its canonical child Visit followed by its copied Bound in pop order |
| Positive Effect capture loop | `incomingJobs`; preserves both pushes and reverses the supplied capture traversal into stack pop order |
| Function Visit | `readValue`, `readEffect`, `functionKeys`, `visitFunction`; all four actual raw child terms, kinds and variances |
| Function completion | `rebuildOne`, `rebuildTerms`, `finishFunction`; original terms reused for unchanged endpoints, changed row terms interned with kind and polarity, real four-child formation guard, Function interning and memoization |
| Tuple/Record/Variant Visit | `visitAggregate`, `collectPorts`; actual port readout and publication, then aggregate frame and child Visits |
| Tuple/Record/Variant completion | `finishAggregate`; slice and missing-child guards, unchanged result, exact changed-call boundary |
| EffectView completion | `perform`; actual rows-first lookup and Effect-row guard before the external remapping call |
| IncomingAllowance completion | `perform`; actual copied-source lookup before the external remap/insert/transfer owner |
| Bound completion | `perform`, `boundRequest`; actual selected Work and actual memo lookup compute the exact external request |
| Both stacks empty | `step`; actual root memo lookup, then external `finish`, not a successful function return |

All eight `Work` constructors are present: Visit, Function, Tuple, Record,
Variant, EffectView, Bound and IncomingAllowance. Changed aggregate rebuilding,
view remapping, allowance initialization, Bound evidence/fibers, and the final
occurrence/replay/sample postlude are named external boundaries. No transition
from those boundaries is postulated in this module.

### Early memo and selected snapshot

The order of `copiedRow` matches the source: allocate, retain the parent,
insert the row memo, perform the one-sided opposite source link, and push
selected work. `memo_precedes_link_call` actually injects a failure at the
pre-append link boundary and computes the state that already contains the
new row and its memo. It does not assume the link or a fiber exists.

`old_value_vector_selected` and `old_effect_vector_selected` prove that an
opposite-side append leaves the selected side unchanged. This justifies
representing the native pre-link length snapshot by its selected list: the
own source link cannot add an element to that chosen side. Later calls may
append further entries, and the packet does not assert a global frozen-bound
universe. Raw entries of the old list remain in the `original` bound key even
when the child key is canonicalized.

The native bound insertion is append-only and deliberately does not deduplicate
physical entries. `physicalInsert` follows that behavior. Its two surrounding
gates retain errors before and after the represented append. The source
row-to-row link cannot match the special negative Effect-row-to-Allowance
capture registration case, so it does not itself mutate the capture traversal
used by `incomingJobs`.

`retain_does_not_merge` records the parent and possible pending parent while
preserving both representative maps and old levels. This is the local part of
NQ §5.1; it does not prove that no other owner can settle or roll back a larger
native history.

### Raw term labels and actual publication

A native `Term` has a lineage brand and a page-based raw index. Its index is
not the position in the count of newly allocated terms: the page size is 256,
branches claim pages, and the branch directory resolves raw indices. The
state therefore stores a finite directory of **explicit `(raw label, cell)`
pairs** in one fixed lineage. `termAllocations` is a separate local allocation
count; `termLabel` is the still-external allocator readout for the next newly
interned cell. No theorem identifies those two quantities.

`StoredCell` uses the existing `OriginalInferenceTerminationResolution.Cell`
and retains live-variable polarity separately. A live Value row and live
Effect row have different cell kinds, and opposite polarities have distinct
interning keys. Existing component cells have no live-variable polarity.
`matchesCell` follows `BranchTermArena::require_function_children` and
`matches_endpoint`: in particular, a source Component cell is not accepted as
a branch live-variable child. The complete ordered Function terms remain
`argument`, `argumentEffect`, `resultEffect`, `result`.

`internCell` computes exact-key reuse or actual raw-label publication. A bad
allocator readout that collides with a visible label is an explicit projection
invariant violation. That check is not being claimed as an additional Rust
availability guard. The native page allocator, brands, lineage visibility,
source Component readout and their extraction into this labeled directory
remain an external correspondence obligation. There is no assumed freshness
proposition or assumed `Cell.Formed` proof in the producer. The two generic
constructor theorems derive readback and preservation of existing labels from
an equality for the computed operation itself.

`with_term_events` executes the constructor and then samples capacity events.
If sampling fails after publication, the cells already committed remain.
The machine preserves that order: changed row construction and final Function
construction have a `constructAfter` stage. It does not incorrectly roll back
the new cells when that stage returns an error. Capacity-only mutations, the
capacity event array, resource counters and error precedence internal to a
failed pre-publication native constructor are outside the represented state;
`Funding` reports their result at the named boundary. Its `calls` index is a
ghost boundary index, not a count of every native allocation or sample call.

### Availability and omitted native internals

`Failure.identityExhausted`, `receiptMismatch`, `artifactMismatch`, and
`native code` retain normal failure outcomes. `invariantViolation` labels a
malformed projection or a native panic/assertion boundary; it is not silently
turned into a successful native result. Missing Bound/Function children and
wrong EffectView results take the actual failure branches. Aggregate shape
and slice failures are distinguished. The slice arithmetic uses the current
64-bit `usize` range; this is not an all-platform pointer-width theorem.

`Funding` is an explicit readout of fallible reserve/accounting/admission
operations, not a theorem that those operations succeed. `funded` is the
concrete all-success readout used to compute the finite witnesses. It does not
prove native resource availability. The aggregate reserve gate also owns the
unrepresented checked size/capacity calculations. Capture traversal and view
information are external readouts; this module does not prove extraction or
acyclicity of the linked capture table. The final two-stack-empty branch still
stops before `finish_candidate_extrusion`, initialized-allowance replay and
final sampling.

## Exact producer theorems and computed witnesses

The complete printed type and transitive axiom list of every originating
constant are retained in the audit log described below. The following are the
principal application types, written inside namespace `W` with the source's
existing native aliases open.

```lean
theorem selected_bound_dispatch (funds : Funding) (s popped : State)
    (owner : Endpoint) (p : Polarity) (child : CopyKey) (original : RawBound)
    (copied : Endpoint)
    (selected : select s = some (.bound owner p child original, popped))
    (memo : popped.lookup child = some copied) :
    step funds s =
      .external popped (.bound (boundRequest popped owner p copied original))
```

This is the parent client seam. The returned request is constructed from the
selected Work and memo; it is not an arbitrary request supplied as a success
certificate. `bound_dispatch_from_pending` discharges selection for an empty
structural stack and an actual Bound at the pending head.

```lean
theorem high_row_visit_schedules (s : State) (key : CopyKey)
    (old : List Endpoint) (level : Nat) (linked : State)
    (rowFresh : s.rows key = none)
    (structureFresh : s.structureMemo key = none)
    (row : ∃ id, key.endpoint = .value (.row id) ∨
      key.endpoint = .effect (.row id))
    (selected : s.rowInfo key = some (level, old))
    (high : key.target < level)
    (room : (match key.endpoint with
      | .value _ => s.values.length
      | .effect _ => s.effects.length) < 2^32)
    (link : physicalInsert (preLink s key)
      ⟨key.endpoint, opposite key.polarity, s.freshEndpoint key.endpoint⟩ =
        .ok linked) :
    visit funded s key = .next
      (scheduled {linked with calls := linked.calls + 1}
        key (s.freshEndpoint key.endpoint) old)
```

The hypotheses are concrete operation readouts and native index/level guards.
The conclusion schedules the old selected entries, without claiming their
Bound calls or fibers have completed. The `link` equality refers only to the
computed physical append; it is not a bound-origin or transport certificate.

```lean
theorem cell_constructor_readback (s after : State) (cell : StoredCell)
    (term : Nat) (computed : internCell s cell = .ok (after, term)) :
    after.storedTerm term = some cell

theorem cell_constructor_immutable (s after : State) (cell : StoredCell)
    (term : Nat) (computed : internCell s cell = .ok (after, term)) :
    ∀ old value, s.storedTerm old = some value →
      after.storedTerm old = some value
```

These preserve actual raw labels. They do not establish available row leaves
or native source extraction, and do not silently assume a successful arena
constructor with the desired conclusion.

### Complete three-step row producer

For every complete symbolic `Request caller`, `Computed.rowInput caller` has
Value row 0 at level 2, its selected upper row 1 at level 1, and a negative
Visit at target 1. Its actual local prefix is:

1. Allocate row 2 at level 1; memoize row 0's negative copy; append the
   opposite source link; push the selected child Visit and Bound.
2. Visit the low row 1 and memoize it unchanged.
3. Pop the Bound and compute its request from the memo.

The theorem has no supplied link, copied row, copied Bound, or completed drain:

```lean
theorem Computed.row_bound_produced (caller : Request) :
    runPrefix funded 3 (Computed.rowInput caller) =
      .external (Computed.rowBoundState caller)
        (.bound (Computed.rowBoundRequest caller)) ∧
    (Computed.rowBoundState caller).values.map Bounds.level = [2, 1, 1] ∧
    (Computed.rowBoundState caller).rows
      ⟨.value (.row 0), .negative, 1⟩ = some (.value (.row 2)) ∧
    (Computed.rowBoundRequest caller).operation.caller = caller ∧
    (Computed.rowBoundRequest caller).original =
      ⟨.value (.row 0), .negative, .value (.row 1)⟩ ∧
    (Computed.rowBoundRequest caller).destination =
      ⟨.value (.row 2), .negative, .value (.row 1)⟩
```

`runPrefix` is a finite observation evaluator. Its zero case returns the
unfinished state, and it stops at error or external calls. It is not solver
fuel, and no bounded-prefix theorem is called inference termination.

### Actual Function rebuild and retained failure state

`Computed.function_keys_from_cells` reads the four raw terms 10, 20, 30, 40
from the existing Function at label 50 and obtains Value-negative,
Effect-negative, Effect-positive, Value-positive keys in that order.

`Computed.rebuildInput` is an explicitly given in-progress Function frame with
four copied rows already present: Value rows 4 and 5 and Effect rows 1 and 2,
all at level 1. It is not represented as an extracted NQ seed or as a proved
state of a full six-step source extrusion. The generic row producer equations
supply the prior local operations, but their complete same-history composition
has not been established here.

From that frame, `Computed.function_rebuilt` computes four live row terms at
raw labels 4096–4099 and the rebuilt Function at 4100. It proves the exact
`step` result, the structure memo and all five cell readbacks. The actual
Function is `F⁺(4096,4097,4098,4099)`, whose leaves are Value row 4,
Effect row 1, Effect row 2 and Value row 5 with the required polarities.
`Computed.negative_copy_in_function` then applies the existing immutable-cell
occurrence theorem to establish `ValueUses` of Value row 4 in Function 4100.
It preserves the other three ports; it is not a Value-only substitute.

`Computed.post_publication_failure_retains_cells` uses a concrete readout that
fails the final Function's `constructAfter` stage with `native 17`. It proves
the exact failed state, all five published cells, and that the structure memo
for old Function 50 is still absent. Four separate `*_cell_computed` theorems
and `row_terms_computed` establish the shared successful child-construction
prefix for both the success readout and this failure readout.

## Parent application and remaining owners

The public `Endpoint`, `RawBound`, `Operation` and `BoundRequest` signatures
were kept stable for the parent's separate `OriginalExtrusionFibers` client.
That client can consume `selected_bound_dispatch` or
`Computed.row_bound_produced`, compute the complete transported relation key
from the exact parent, and invoke the real raw relation interner/linked-fiber
publisher. This module does not import or assume that client's unfinished
proofs.

`OriginalBoundFibers` supplies a separate actual linked-fiber store and
captured-cursor/attach facts. `OriginalReplayBoundary` supplies the separate
first-boundary-to-processed bridge. `FiniteCopyClosure` has conditional
snapshot/closure premises; this packet does not simply assume those premises
and call that native NQ. The three local results must still be connected in
one source-corresponding history.

The first remaining source-specific bridge is extraction of an authentic NQ
extrusion state and its successful native call readouts, followed by the
selected Work execution and exact transport owner in that same history. A
proof that a normal complete extrusion has finished every selected Bound is
still required before asserting the whole copied path. Other remaining owners
include aggregate and Effect view/capture execution, arena/brand/source
readout extraction, enclosing dispatch and pair-memo chronology, settlement
exclusion, retained seed fibers, and the anchored-successor/maximality argument.
No successful full drain, finite allocation universe, fairness principle,
source-bound allocation cardinality or successor law has been introduced.

## Verification and retained evidence

The pinned toolchain is Lean 4.35.0 / Lake 5.0.0-src+eb6cafb. The worker ran
only direct, no-output-file checks from `notes/theory/lean`:

```text
timeout 120 /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake \
  env lean -j1 -M1024 YulangClosure/OriginalExtrusionWork.lean
```

The worker did not build dependencies or mutate the shared cache. The parent
owns the subsequent module build. Proof check 12 returned exit 0 with no
diagnostics. The frozen source differs afterward only by source-boundary
documentation comments. No `maxHeartbeats` increase, `native_decide`, skipped
kernel checking, `sorry`, `admit` or project axiom was used.

Twelve of eighteen proof invocations were consumed. Logs
`/tmp/yulang-extrusion-work-check-1.log` through
`/tmp/yulang-extrusion-work-check-12.log` preserve the failures and final
success. Early checks repaired ordinary elaboration/library-name/layout
errors. Checks 8–10 exposed repeated reduction of a monolithic Function
calculation at the default 200,000-heartbeat limit; the raw-label correction
also removed an invalid dense-term-index prototype before acceptance. Check
11 left only an unreduced `Except.map` equation after four exact child-step
lemmas were introduced. Adding the actual reduction for `Except.map` produced
the clean check 12. These failures were not native divergence counterexamples.

The parent built the frozen source and its actual clients successfully:
`/tmp/yulang-extrusion-client-build.log` records 15 jobs, including
`OriginalExtrusionWork`, `OriginalExtrusionFibers` and `OriginalFiberTransfer`,
with no warnings or errors. The worker then audited the imported originating
module index, rather than a namespace prefix or an extracted prelude.

The final audit command was:

```text
timeout 120 /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake \
  env lean -j1 -M1024 /tmp/yulang-extrusion-work-census-final.lean
```

It exited 0. The log `/tmp/yulang-extrusion-work-census-final.log` prints
**all 950 originating declarations**, including **363 theorem constants**,
with every full type and transitive axiom list. It also explicitly checks all
41 authored theorem roots. Exactly 950 begin/end audit pairs were present;
there were no diagnostics, ellipses, target axioms or transitive dependencies
outside `propext`, `Classical.choice` and `Quot.sound`. Of all declarations,
737 have no axiom dependencies, 201 use only `propext`, 11 use
`propext, Quot.sound`, and one uses all three standard axioms.

Both assigned audit invocations were used. The first complete census also
reached all 950 declarations, but the scratch script had placed a documentation
comment before `#check`, causing a parser error and exit 1. Its unchanged log
is `/tmp/yulang-extrusion-work-census.log`; changing that scratch comment to
an ordinary comment produced the final clean audit. No target proof bytes,
resource limits or axiom policy changed. The final source hash remained
unchanged before and after the imported audit. The sandboxed direct binary
version lookup failed to locate its application; the authorized pinned
`lake env lean --version` lookup succeeded and reported Lean 4.35.0,
x86_64-unknown-linux-gnu, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The exact authored axiom inventory follows. Names without a further prefix
are in `YulangClosure.OriginalExtrusionWork`; `Computed.` names remain in its
nested namespace. This is an axiom-dependency report, not discharge of theorem
hypotheses or certification of the external native readouts.

**No axioms — 4 authored theorems:**

- `operation_local_memos`
- `structural_work_first`
- `pending_work_selected`
- `retain_does_not_merge`

**`propext` — 27 authored theorems:**

- `fresh_value_after_receiver`
- `rows_memo_first`
- `memoized_visit`
- `memo_insert_read`
- `old_value_vector_selected`
- `old_effect_vector_selected`
- `prepared_row_memo`
- `memo_precedes_link_call`
- `push_all_funded`
- `bound_job_preserves_raw`
- `function_keys_computed`
- `function_keys_have_four`
- `bound_missing_stops`
- `selected_bound_dispatch`
- `bound_dispatch_from_pending`
- `bound_request_whole`
- `function_visit_computed`
- `Computed.argument_cell_computed`
- `Computed.argument_effect_cell_computed`
- `Computed.result_effect_cell_computed`
- `Computed.result_cell_computed`
- `Computed.row_terms_computed`
- `Computed.function_keys_from_cells`
- `Computed.function_rebuilt`
- `Computed.post_publication_failure_retains_cells`
- `Computed.negative_copy_in_function`
- `Computed.row_bound_produced`

**`propext`, `Quot.sound` — 9 authored theorems:**

- `allocate_value_ordinal`
- `allocate_effect_ordinal`
- `selected_bound_job`
- `selected_visit_job`
- `schedule_bounds_computed`
- `scheduled_old_bound`
- `cell_constructor_immutable`
- `copied_row_schedules`
- `high_row_visit_schedules`

**`propext`, `Classical.choice`, `Quot.sound` — 1 authored theorems:**

- `cell_constructor_readback`

The full machine-readable declaration inventory is
`/tmp/yulang-extrusion-work-audit-manifest.json`; the compact authored list
is `/tmp/yulang-extrusion-work-axioms.txt`. Six unused proof invocations remain
from the original bound, and no audit invocations remain. All checker
processes are complete. The Lean source is frozen; this note is frozen at the
final hash handoff. The worker has stopped writes.

### Source and dependency hashes

| File | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| NQ note, `2026-10-26-native-copy-quiescence-obstruction.md` | `fc2676a6881ac662b2926b2f39223112dbd832e4fb44feca6e212422bbe33d75` |
| `OriginalInferenceTerminationResolution.lean` | `a89a316ea72e472b0e2c09effc144730dc4c683228008caf42a433d0a969a6dd` |
| `FiniteCopyClosure.lean` | `eaa4af374dfff21e74a9e8a89d681932404f7a8c4e97850fe0cae544dcf9e10b` |
| `OriginalReplayBoundary.lean` | `894f0008c7cf62a43a80c82eb75c5ae08c2a0aa84c0fbadae4dcec07529544c8` |
| `NativeRelationInterner.lean` | `1fd7ece6c6a7c6df7159efaebaec585b78a9e8513e9b10e6a3fb4d472b577d3a` |
| `OriginalBoundFibers.lean` | `1a512b23a55936e30088763d46d3f71458cec953b58edbf794e28bb13eaf0ca5` |

The only repository writes in this packet were the leased Lean source and
this paired note. No Rust, shared status, root import, Git, dependency,
`.olean`, or other worker's file was changed by this worker. Independent
review and parent integration are separate evidence, not self-certification.
