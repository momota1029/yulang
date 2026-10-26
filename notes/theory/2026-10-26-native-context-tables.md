# Native Context table lifetimes and committed readback

Date: 2026-10-26. Producer packet: `TABLES-LIFETIME-READBACK`, r4.

Status: constructed and checked with the pinned Lean kernel; fresh independent
review is required. This is a supplier to the original complete inference
soundness work. It does not mark the original parent or source inference
soundness complete.

The new proof is [NativeContextTables.lean](lean/YulangClosure/NativeContextTables.lean).
Its source SHA-256 is
`eaf2b037af40af01ad116e1ae413a6c7d5a0023d49c8b9f1b92d29c319d2df81`.
The fixed initial source revision is
`82b8fb669c5b51c6c99771cd2208c9730ebc85c3`. The separately accepted
`NativeContextReadback` dependency was pinned only after publication at
`ee61ba0b68789e2dea9eac024130f21c5a4e6453`; its SHA-256 remains
`321d087c8d2df5099f67beb75e4316d44114806bbfae2aa64ebda22a34bd83f2`.
No concurrently changing sibling module is an input.

## 1. Original obligation and the constructed supplier

The accepted [Context readback construction](2026-10-26-native-context-readback.md),
§7, left `TABLES-LIFETIME-READBACK` open. Its fixed `Tables` parameter could
not represent arbitrary native rollback followed by reuse of a raw Context ID.
The missing supplier had to account for Contexts, weights, Views,
contributions, and the actual `PrefixLeft(weight,Identity)` interner lookup in
one history. A generic equality assumption between two arbitrary tables would
both miss the native constructors and forbid legitimate fresh allocation.

This packet constructs the native vector changes, the Context cache changes,
the monotone ghost allocation clock, the table versions, and the rollback
frontiers. It proves that every successful computation in the existing
Context evaluator survives forward table extension. It then migrates every
constructor of the accepted Context/drain driver and places those driver
events together with the table constructors in one `JointHistory`.

The principal application is
`YulangClosure.NativeContextTables.committed_tables_context_readback`:

```lean
{state : Joint} → JointHistory state →
state.context.control.queue = [] →
state.context.control.frames = [] →
∀ work ∈ state.context.control.issued,
  ∃ receipt ∈ state.context.receipts,
    receipt.work = work ∧
    NativeContextReadback.Resolved state.context receipt ∧
    NativeContextReadback.RouteValid state.context receipt.route
```

There is no `TableExtension`, table-equality, complete-body, `ClosedAt`,
`InstalledAt`, or full Context coverage premise in this root. The constructed
`JointHistory` is the event-history premise. It contains the native storage
constructors and the existing actual driver transitions; it is not a theorem
that an arbitrary Rust success has already been interpreted as that history.
The exact native interpretation boundary is recorded in §9.

`committed_tables_original_body` additionally reads an actual Effect receipt
back to its owner's stored `BodyRecipe` at the current table version, the
original nonempty checked prefix, the route's Derived edges, the complete
source-set identity and transformer, and the native absence of Effect scoped
demand. `committed_tables_whole_child` applies the accepted complete child
payload theorem to every child of that body.

## 2. Native mutation and read owners

The source snapshots are the five immutable files listed in the packet's
`inputs.json`. The following are the storage owners, rather than just uses of
the same field names.

| Native owner | Mutation and index rule | Constructed representation |
| --- | --- | --- |
| `candidate_context.rs`, `State::context`, 2630–2655 | Assert every Context child; return an existing full-expression key or append at `contexts.len()+1`; zero is identity; insert the expression in `context_keys`. | `Store.intern`, `Step.context`, `internCell`, `native_interner_cache`, `native_interner_reuse`. All six `Expr` constructors remain available. |
| `candidate_context.rs`, `source_weight`, 2734–2758 | Append at `weights.len()`. Keep exact allowed members, reserved View boundary, owner, position, zero words and optional attachment source/ordinals/unit-push flag. | `WeightRecord`, `weightRecord`, `Store.appendWeight`, `Step.sourceWeight`. |
| `candidate_effect.rs`, `candidate_signature_view`, 859–909 | Reserve View index `views.len()` before optional weight creation; append the complete View; sample after publication. | `ViewInput`, `Draft`, `Store.reserveView`, `Store.publishView`, `Store.finishView`, and the separate reserve/weight/publish/sample events. |
| `candidate_effect.rs`, `candidate_copy_effect_view`, 1155ff | Read the original View; validate any source weight; copy owner, position, allowed sequence, operation origin and attachment source; use the requested new tail. | `validateView`, `copyInput`, `Step.reserveCopy`, `construct_copy_run`, `copy_input_fields`, `view_validation_readback`. |
| `candidate_effect.rs`, `candidate_remapped_effect_view`, 1181ff | A cache hit leaves these five tables unchanged; a miss delegates to the copy constructor and publishes the local remap only after success. | A hit is a table stutter. A miss uses the complete copy constructor above. The external local remap's ownership and semantic meaning are not replaced by this table model. |
| `candidate_effect.rs`, `candidate_effect_contribution`, 1213–1236 | Append effect, source origin and `instance = contributions.len()` at that same raw index, then sample. | `Contribution`, `Store.contribution`, `Step.contribution`. The append is a separate storage cut; the later resource sample is a table stutter, and a failed route can cancel this cut. |
| `candidate_context.rs`, `candidate_context_source`, 3361–3372 | For a closed allowance, intern the actual `PrefixLeft(weight,Identity)` expression; otherwise use identity. | `interner_prefix_identity`, `interned_source_available`, and `native_prefix_is_cache_lookup`. |
| `candidate_context.rs`, checkpoint/rollback, 2044–2160 | Capture Context and weight lengths; drain the new suffix; remove every drained Context expression from `context_keys`. | `Frontier`, `truncateContext`, `cancellation_vectors`, `native_cache_rollback`. |
| `candidate_effect.rs`, checkpoint/rollback, 313–389 | Run Context rollback first, then truncate contribution and View vectors to the saved lengths. | `truncateEffect`, `native_rollback_order`, `context_rollback_can_precede_view_rollback`. |
| `candidate_context.rs`, `rename_contexts_impl`, 1556–1689 | Every source handle is checked against the captured Context frontier, even after new outputs have been interned. Failure removes inserted local remap entries and rolls back the Context checkpoint. | `renameSource`, `rename_source_old_frontier`, `rename_new_source_rejected`, the full-expression interner, and the native Context frontier/cached-key rollback equations. Weight/certificate remapping semantics remain with the caller's source interpretation; every resulting `Expr` is represented. |

The `Tables` projection preserves all five lanes. A `Cell` additionally stores
an allocation birth. `WeightRecord` retains attachment metadata that is not
consumed by the frozen parser. `ViewRecord` retains both source and executable
closed weights and the full operation-origin identity, occurrence and retained
byte field. A contribution retains its source origin and instance as well as
the effect used by operand checking. Source object identities are the same
opaque natural-number identities used by the accepted modules; they are not
replaced by source-text hashes or a reduced set of syntax cases.

## 3. Publication windows and dependent handles

`ViewInput.needsWeight` is exactly

```lean
operation.isNone && (tail.isNone || attachment.isSome)
```

An operation View therefore follows the source's no-source-weight branch. An
annotation with an open tail can still have a source attachment weight; it
does not expose that weight as an executable closed filter. `viewRecord`
selects `closedWeight` only when the tail is absent.

The View's ghost birth is reserved before weight construction, at the native
View capacity/index reservation cut. The optional weight receives the next
birth. This order is deliberate: a weight can exist with its reserved View
index while that View is not yet in the View vector. The theorem
`source_weight_before_view` proves the weight lookup succeeds and the matching
View lookup is still `none` at that cut. `construct_view_run` constructs the
whole successful reserve/optional-weight/publication/sample sequence.

`constructed_closed_weight_valid` supplies the actual frozen `weightValid`
predicate for a newly constructed closed annotation View. It derives the
weight and View lookup results and their dependent boundary/owner/position
matches from the two appends. It does not assume a globally valid View table.
The attachment theorem preserves source polarity, scope, all original member
ordinals, and the exact positive/nonempty unit-push condition.

The opposite transient window occurs during rollback: Context and weight
suffixes are removed before the View suffix. The module explicitly exhibits
that the old View can still be present after its new weight has been removed.
It makes no global well-formedness claim about that intermediate cut. The
complete native rollback restores all five projected lanes.

## 4. Forward extension, cancellation and raw-ID reuse

Every `Step` is a source constructor cut. Context interning either keeps the
vector or adds one fresh full expression; the remaining writes append to
their own vector. `step_prefixes` and `run_prefixes` construct a suffix witness
for every storage lane. They are stronger than an extensional lookup relation.

`cancel` uses the native saved lengths to take the retained prefixes.
`cancellation_all_five_tables` proves equality with the saved projection as a
conclusion of a constructor `Run`. Equality is not an input. The fifth lane
is not an independent immutable array: the cache section proves exactly that
new expression insertion preserves `keyLookup`, that interning never creates
duplicate expressions in a constructed history, and that removing the
expressions in the drained suffix recovers the original cache. The removal
proof needs the derived no-duplicate invariant, since otherwise deleting a
new duplicate could delete an old key.

The raw frontiers rewind; the ghost allocation clock does not. `Fresh` proves
that every existing cell and reserved View birth is below that clock.
`retry_context_birth` and `retry_all_lanes_birth` show that a retry can reuse
the same numeric index while receiving a birth later than every allocated
birth in the cancelled attempt. The View and source-weight births remain
distinct even though View publication happens later.

`allocated_lookup_extension` preserves complete cells, including births and
metadata, during a forward run. It intentionally requires an allocated old
answer. An old `none` answer is allowed to become `some`. `Observation`
therefore contains the actual version, query and answer. The common history
records such observations at their actual cuts, and
`committed_observation_readback` supplies a source-constructed saved/cut
witness for each retained observation. No current table is substituted for
the table that produced an earlier missing answer.

## 5. Transporting the actual evaluator

`run_table_extension` derives a positive lookup extension from the source
constructors. Positive Context, weight, View and contribution reads retain
their values; an already nonzero prefix lookup keeps its actual interner ID.
This relation is an internal lemma, not an extra hypothesis of the committed
readback root.

The proof then follows the definitions of the accepted evaluator:

| Computation | Main proof |
| --- | --- |
| Weight validation and every parser stack step, including all modes and failure branches | `valid_weight_extension`, `scan_step_extension`, `scan_loop_extension`, `parse_extension` |
| Child-local Context source and complete admitted key | `source_extension`, `admit_extension` |
| Member effect lookup, closed-allowance membership, support/member/tail expansion and unavailable cases | `effect_member_extension`, `closed_view_extension`, `member_check_extension`, `operand_check_extension` |
| Actual operand availability, bound/local-return/children/conflict callback selection | `operand_available_extension`, `apply_effect_extension` |
| Every installed filter, including already-registered bounds and every callback result | `apply_filter_extension`, `check_filter_extension`, `collect_extension` |
| Complete ordered prefix, stored/post-check Context choice and consumed/residual body | `prepare_parsed_extension`, `prepare_extension`, `finish_prefix_extension` |
| Original construction-directed prefix/body recipes, including carrier transport | `prefix_recipe_extension`, `body_recipe_extension` |
| Full Value Context forwarding request and all ScopedDemand fields | `value_context_extension`, `execute_value_extension` |

A successful operand's closed-weight availability guard matters here. A raw
View with a missing closed weight could otherwise expose `closedAllowed =
none`, and a later append could change membership behavior. The proof uses
the native `operandAvailable` check before the old successful member/allowance
operand. It does not add a blanket View-well-formedness assumption or silently
assume that all missing reads are stable.

`VersionedChecks` further permits arbitrary native constructor runs before
each individual installed filter callback and after the last callback. Its
constructors carry the actual `checkFilter` result at each cut, retaining the
entire original weight/check sequence. `versioned_checks_readback` constructs
the final `collect` result. `versioned_prepare_readback` transports the actual
parser result and combines it with all those checks at the later cut.
`versioned_finish_readback` allows more allocation between the completed
prefix and residual/consumed completion. No completed body is a callback to
these constructions.

## 6. One table and Context/drain history

The dependent `Joint` payload contains a `Store`, a
`NativeContextReadback.State store.tables`, and versioned observations.
`JointStep.table` obtains the new store from a native constructor `Step` and
migrates the existing driver state using its derived extension.
`JointStep.context` executes one original driver event at that very store.
`JointStep.observe` reads that store. The two histories cannot be selected
independently.

`Reindex` preserves all driver fields: immutable issued work, current
processing owners, both representative maps, generation, relations, tasks,
routes, checked/published/ready stages, Value requests, the full discharge
table, post Context map, active owners, typed/memo state, seals, receipts,
Derived edges and settlement flag. It changes construction proofs to use the
later table while retaining all underlying keys and data.

`Reindex.step` proves the migration equation for every original event:
control, relation/task interning, queued-key Transport, empty/nonempty Context
checking, early publication, sampling, cached parsing, Value Context,
memo admission, fresh residual completion, duplicate return, Value return,
settlement begin, representative merge, and settlement end. In particular,
the duplicate memo can still name an active owner. Migration does not turn
that owner into a completed body.

`JointHistory` starts at the empty native store and the original initial
driver. A committed attempt is a `JointRun` with no outstanding View draft.
A cancelled attempt uses the proven vector/cache rollback to cast the actual
saved driver checkpoint to the restored table projection. It retains the
later ghost clock and advances the table version. The central lemma
`joint_history_facts` derives an original Readback `Run` at the resulting
store; this is the input supplied to the accepted quiescent theorem.

This construction uses checkpoint restoration for the driver projection,
whose concrete joint journal construction is in the accepted
`NativeContextReadback`/`NativeExecutionHistory` dependency. The table
restoration is separately and constructively supplied here by the native
lengths and cache-removal operations. It is not justified merely by treating
the entire table as an arbitrary journal cell.

## 7. Concrete allocation/retry witnesses

The `Examples` namespace constructs a real closed annotation View with allowed
members `[7,8]`, weight 0, owner 3, position 4 and positive attachment scope 9.
It interns `PrefixLeft(0,Identity)` at Context 1 and appends contribution 0
with effect 7 and source origin 44. `all_five_lanes_first` reads all five lanes.

Cancellation to the empty checkpoint removes those cells and the prefix
cache entry. A retry creates a different closed View, then interns `Swap(0)`
at the reused raw Context index 1. The old Context birth is 2; the retry's
birth is 6. The first parser result is the single filter `[0]` with residual
0. The retry parser result has no filters and is directed with residual 1.
These are successful computations on two source-constructed histories, not
two hand-written unrelated `Tables` functions.

The same example constructs the original `PrefixRecipe` and `BodyRecipe` for
the first store. Its parent keeps Context 1, source-set identity 11 and
nonzero transformer 4. The installed filter is retained, the upper allowance
is consumed, and no residual continuation is invented. A subsequent fresh
contribution allocation preserves that exact completed body by the general
extension theorem.

## 8. Settlement and evidence horizon

The complete issued-work root requires both an empty queue and empty drain
frame stack, as in the accepted theorem. The Effect body root uses the exact
`NoCurrent` cut. An inner settlement with an active outer owner still permits
the existing active-owner alternative; this packet does not infer a seal from
pending coverage or from publication alone.

Receipts are proof-history data derived from the same driver transitions.
They are not read back from the optional native `source_drain_completions`
vector. The source's `record_source_drain_completion` can return early when
its observation-only reservation fails, while inference success is preserved
(`candidate_context.rs`, 2177–2184). None of the new roots assumes that this
optional observation was stored.

## 9. Exact remaining application boundaries

The fixed-table lifetime premise of the represented Context/drain history is
now supplied constructively. Applying that history to the original native
runtime still has the following concrete owners:

1. The native callback/control interpreter must build the `JointStep.context`
   events and insert the actual storage `Step` events at their source cuts.
   The existing full driver requirements remain intact: actual raw task and
   relation lookups, complete keys and demand, successful callback guards,
   allocation/error results, publication order, active owner/memo linkage,
   dequeue/Transport/Dispatch control, and the real settlement cuts. The
   current root's Context callback/completion construction owns that bridge.
   This module does not derive it from an arbitrary `Ok` return.
2. Representative maps must be the actual source forest maps; the source
   merger must supply the same Derived and body-carrier transport. The
   reindex proof leaves those maps and all complete payloads unchanged. It
   does not identify a historical seal with a different final physical bound
   carrier without that source bridge.
3. Function/Tuple/Record/Variant ports and the other original Value forms must
   supply their actual dispatch semantics and callback-to-issued-work links.
   The root's Value drain/Context completion packets own those links. This
   packet preserves the complete Value request and all ScopedDemand fields
   but does not claim Value typing soundness.
4. Effect semantic dispatch and conflict-free inference acceptance remain
   semantic obligations. The existing evaluator can record a conflict and
   return locally; a computed `BodyRecipe` alone does not prove successful
   source subtyping or `SourceProblem.InferenceSoundness`.

The View-copy/remap and fresh-Context renaming source metadata are preserved
at the table boundary. Their external substitution maps, source-object
interpretation, resource accounting and any concrete runtime journal erasure
are not redefined here. The represented table changes admit every installed
constructor and every allowed input; no source-language restriction, weaker
typing predicate, or new inference behavior is introduced.

## 10. Verification and frozen receipts

The producer used only the pinned native toolchain, an isolated project/cache,
one Lean thread and `-M1024`. There were 19 focused checks, all at most 120
seconds; the longest took 55.687 seconds. Total measured focused-check wall
time was 261.166 seconds. The final complete audit, check 19, took 14.749
seconds and reported child-process maximum RSS of 1,022,980 KiB. Its module
build and complete census both exit 0 with no warnings. Failed source
snapshots and all failure logs are retained.

The final audit traversed every constant originating in the module and
printed its complete type and actual axiom dependencies, including generated
and private constants: **1,125 declarations, 521 theorem constants, 145 named
source roots, 65 private declarations and 43 private theorem constants**.
Among theorem constants, 260 use no axioms, 118 use `propext`, 113 use
`propext` and `Quot.sound`, and 30 use those two plus `Classical.choice`.
There is no originating project axiom, proof hole or unchecked native
evaluation. The complete census is 771,138 bytes with SHA-256
`ec9858b8f1f923d47fddf1e627227e060ff96bdcfdcbfde9331474420b8db32d`.

The first independent review requested one batched repair of 21 warnings.
The repaired lines replace unnecessary `simpa`, remove unused simp arguments,
rename one unused binder, and remove the global simp registration from
`Reindex.map_put`; existing uses name that theorem explicitly. No theorem
statement, definition or semantic guard was weakened, and no linter was
suppressed. All 145 named root types and axiom sets are byte-identical in the
printed census. Among the remaining declarations, only two generated
`step_fresh` simp auxiliary names shift; their complete types and axiom sets
match under the exact recorded renaming.

The entire original frozen scratch tree and its repository module, paper and
handoff are preserved under `pre-review-20261026T125109Z/`, including the
original freeze, all failures and the review diagnostics. The snapshot
manifest SHA-256 is
`ceded2ab2448689e96e2dd4fba00d369d1785f0dbe94a928a5f5b41b42c2472b`.
`review-repair.diff`, `review-repair.json` and `review-delta-census.json` record
the exact proof delta and complete census comparison. The substantive review
reported no semantic finding; independent acceptance of the final delta
remains with the assigned reviewer and primary.

The reproducible producer scripts, all frozen source snapshots, exact commands,
version output, per-check receipts, all 18 input hashes, root list and complete
origin inventory are under the leased scratch directory
`/workspace/scratch/f98087c7ac1a/context-tables-r4/`.
The handoff is
[20261026-native-context-tables-r4.md](../../tasks/agent-loop/inbox/20261026-native-context-tables-r4.md).
The final freeze manifest provides the output hashes. Fresh independent review
must assess source correspondence and the remaining parent application; the
producer does not self-certify acceptance.
