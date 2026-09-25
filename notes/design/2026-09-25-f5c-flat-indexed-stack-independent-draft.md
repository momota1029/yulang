# F5c flat indexed draft and stack-independent finalization

Status: Reviewed proposal; user approved the non-shipping candidate-before-boundary sequence (2026-09-25); solve-wide charged-work meter lifetime is approved; candidate implementation may proceed within §§2–8 after focused M3 review; numeric support boundary and production acceptance remain open
Scope: F5c structural-depth stack use from live expansion through closed-scheme finalization and cleanup
Related authority: F5 §§14–16, 24–26, 32–36, 43–44; F5b closed-finalization accounting amendment §§2, 6, 9
Decision: implement and measure a non-shipping flat-draft/indexed-finalization candidate before selecting numeric resource thresholds; no production acceptance or release before independent resource review and separate user approval
Supersedes: proposes to replace the bounded boxed-draft candidate in `2026-09-24-f5c-bounded-boxed-draft-gate-draft.md` and the conditional Boundary A preference in §9 of `2026-09-23-f5c-indexed-finalization-accounting-boundary-draft.md`; no existing authority is superseded before user approval

## 1. User direction and decision boundary

The user chose to support structurally deep F5c schemes using explicit stacks
rather than a fixed structural-depth threshold. The user later approved the
non-shipping candidate-before-resource-boundary sequence in §15. This permits
candidate implementation after focused independent M3 review of that sequence;
it does not authorize production acceptance, release, or an unreviewed
semantic/API expansion.

On 2026-09-25, the user approved the first-stage investigation of this
direction: inspect practical source inputs, source charge sites, and focused
scale behavior. That earlier approval, like the later solve-wide meter-lifetime
approval, did not by itself authorize candidate implementation. The subsequent
explicit approval in §15 authorizes the non-shipping candidate, contingent on
focused review of the revised sequence; neither approval selects numeric
resource limits or authorizes production acceptance.

The product target remains Oracle-equivalent behavior for practical source
inputs and a lightweight successful path. The proposed change removes native
call-stack growth proportional to F5c structural depth; it does not promise
unbounded memory, work, or acceptance. Resource exhaustion must remain a
checked failure before any scheme, fact, receipt, provenance, route marker, or
`SolvedModule` becomes visible.

The existing depth-256 experiment is only evidence about the current boxed
finalizer and destructor: debug overflowed at 64 KiB and 256 KiB, passed at
512 KiB, while optimized release passed at 64 KiB. It is not a minimum-stack
guarantee and does not select a depth limit.

## 2. Required ownership boundary

Use one flat, solver-owned F5c draft representation from the first potentially
deep producer through finalization input and every error exit. Nodes and
children are represented by polarity-specific indices, child spans, scalar
payloads, and root IDs. Recursive-bound entries and the predicate name node
IDs; they do not own nested `Box` or per-node child `Vec` trees.

The flat representation must remain in use through:

1. component-summary expansion and root-local Q/R generalization;
2. replay, binder substitution, and raw-bound materialization;
3. canonical normalization, ranking, deduplication, and root/member
   projection;
4. component draft staging and indexed finalization input construction;
5. checked error cleanup, cancellation by error return, and ordinary drop.

No accepted deep path may rebuild a recursive `F5cPositive` or
`F5cNegative` tree, including on an error path. A worklist over a boxed tree,
or a finalizer-only adapter that first accepts a boxed draft, does not meet
this boundary: Rust would still recursively drop the owned source or a partial
task/value tree.

The Function Cartesian product in `InferenceSession::closed_parts` is
post-finalization per-use scheme instantiation, not construction of the F5c
scheme draft. It remains outside this flat-draft boundary and in the separate
F5e closed-DAG instantiation/resource gate. Its checked product multiplication
detects arithmetic overflow but does not cap the number of generated pairs.

The current flat `Node` representation in `f5c_normalization.rs` is a starting
point, not the handoff contract. Its boxed `rebuild` must be replaced by flat
output. Existing F5c modules should own their corresponding flat operations;
`lib.rs` should retain component orchestration and not become the new arena or
transaction implementation.

After normalization removes duplicate Union/Intersection members, compact the
final graph from the predicate and every retained R lower/upper root. Visit
roots in the specified deterministic order, preserve normalized child-span
order, reuse IDs for shared nodes, and remap every surviving edge/root into
dense final arrays. The indexed finalizer rejects orphan nodes, so unused
pre-normalization nodes must not be carried into its input. Tests must include
duplicate members and shared DAG children that become shared or unreachable
after normalization.

## 3. Proposed cross-crate finalization boundary

Add a `yu-types`-owned indexed finalization transaction adjacent to
`ClosedTypeFinalizationSession::finalize_scheme`. This is a proposed public
API, even when hidden from rustdoc. Its exact method and seven input types are:

```rust
#[doc(hidden)]
pub fn finalize_indexed_scheme(
    &mut self,
    input: IndexedSchemeRef<'_>,
) -> Result<ClosedSchemeFinalization, ClosedTypeFinalizeError>;

#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct IndexedPositiveNodeId(pub u32);
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct IndexedNegativeNodeId(pub u32);
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IndexedChildSpan { pub start: u32, pub len: u32 }
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IndexedPositiveNode {
    Bottom, Int, Quantified(u32), Recursive(u32), Union(IndexedChildSpan),
    Function { argument: IndexedNegativeNodeId, result: IndexedPositiveNodeId },
}
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IndexedNegativeNode {
    Top, Bottom, Int, Quantified(u32), Recursive(u32), Intersection(IndexedChildSpan),
    Function { argument: IndexedPositiveNodeId, result: IndexedNegativeNodeId },
}
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IndexedRecursiveBound {
    pub ordinal: u32,
    pub lower: IndexedPositiveNodeId,
    pub upper: IndexedNegativeNodeId,
}
#[doc(hidden)]
#[derive(Clone, Copy, Debug)]
pub struct IndexedSchemeRef<'a> {
    pub quantifier_count: u32,
    pub predicate: IndexedPositiveNodeId,
    pub positive_nodes: &'a [IndexedPositiveNode],
    pub negative_nodes: &'a [IndexedNegativeNode],
    pub positive_children: &'a [IndexedPositiveNodeId],
    pub negative_children: &'a [IndexedNegativeNodeId],
    pub recursive_bounds: &'a [IndexedRecursiveBound],
}
```

The ID newtypes index only their matching polarity arrays. Positive
`Union` spans index `positive_children`; negative `Intersection` spans index
`negative_children`. Effects are fixed to the existing closed pure pair and
are intentionally absent from this input. There are no new traits, error
variants, handle accessors, or accounting getters. All seven items and their
shown trait/field contracts require review as part of the §24 surface.

Before creating any transaction handle, validate with checked arithmetic:

- every positive/negative node ID against its matching array;
- each child span's checked `start + len` endpoint against its child array,
  and every child ID in both child arrays, including entries outside selected
  spans;
- Q references exactly in `[0, Q)`, where `Q = quantifier_count`;
- exactly `R = recursive_bounds.len()` bounds, with entry `i` having ordinal
  `Q + i`, checked for overflow; every R reference is exactly in `[Q, Q + R)`
  and maps to bound `ordinal - Q`;
- every bound lower/upper root and the positive predicate root;
- the complete structural child graph for acyclicity and reachability. Shared
  DAG nodes and repeated child edges remain valid. Recursive references are
  leaves, not structural edges. Every node must be reachable from the
  predicate or one of the R lower/upper roots; orphan nodes are invalid.

The intended indexed validation bound is `O(V + E + B + Q)`, with scratch
bounded by those input dimensions, but only if the implementation follows a
direct dense-index path. Let `V` be the total positive and negative node
count, `E` the stored child-ID entries plus logical parent-to-child
incidences (including Function argument/result edges and repeated incidences
from overlapping spans), `B` the recursive-bound count, and `Q` the
quantifier count. Check `Q + B` and all index conversions; validate bound
entry `i` as ordinal `Q + i`; resolve Q references by `ordinal < Q` and R
references by checked `ordinal - Q` into `[0, B)`. Scan every stored child ID,
including IDs outside selected spans. Then use a three-color iterative DFS
from the predicate and every bound endpoint, visiting each node and outgoing
incidence once; a gray edge is a structural cycle, and any node still white
after all roots is an orphan. Recursive-reference leaves do not add structural
edges. Planning and commit need their own bounded-pass source proof. The
current callback validator has nested linear membership/duplicate searches,
so its complexity cannot be cited as evidence for this proposed indexed path.

Solver-side production must compact after normalization before constructing
this input, so deduplicated-away nodes cannot violate the no-orphans rule.
The producer owns F5c source semantics: it assigns Q/R with the approved
first-surviving producer encounter order, preserves root-local uncached state,
and emits only retained R owners whose §33 trace re-enters the same owner,
contains a Function field, survives hypothetical non-R one-sided elimination,
and completes to a nontrivial bound. An unguarded/unproductive source cycle
continues to collapse as currently specified; it is not emitted as a retained
F5c R owner. `yu-types` validates ordinal/reference closure, polarity,
structure, and transaction validity; this draft does not silently change the
existing F5a closed-finalizer contract for structurally valid recursive
schemes that its callback currently accepts.

The flat producer must preserve the full order/ownership crosswalk: census
before elimination, retained R classification before Q, Q/R namespaces local
to each root, R order from the first-surviving producer re-entry trace, Q
order from first retained bipolar producer occurrence, and no cache sharing of
root-dependent or provisional/retained-R state. This implements the approved
2026-09-23 producer-order addendum; hash iteration, source permutation, flat
node ID allocation, or compaction order cannot select a binder ordinal.

After Q/R substitution, closed normalization, pruning, and closure validation,
the F5c producer asserts that final unreachable-R pruning removes zero owners
and every emitted Q ordinal remains referenced. The indexed finalizer validates
reference ranges and its existing F5a acceptance contract; it does not repair,
renumber, or impose this producer-specific dense-closure invariant. A failure
is an internal producer invariant error and publishes no draft. Producer tests
must include unused-Q and unreachable-R fixtures that reach this final check,
plus successful cases proving the post-normalization prune is a no-op and Q is
dense and fully referenced.

The solver must fail before input construction if an internal count/ID/span
cannot be represented, mapping that failure through the existing
`IdentityExhausted` availability path. A `yu-types` `InvalidDraft` from a
solver-produced input is an invariant failure: return no module and do not map
it to a new `SolveAvailabilityError`. Direct malformed indexed input returns
`InvalidDraft`; valid-input checked index/capacity/byte exhaustion returns
`IdentityExhausted`.

The caller owns immutable flat input arrays for the call. `yu-types` owns all
transaction-branded handles, source-ID maps, validation marks, explicit
DFS/postorder worklists, temporary child mappings, and commit scratch. No
lifetime erasure, raw-handle reconstruction, or typed handle stored in
solver-owned state is allowed.

Build order remains deterministic: R bounds by ordinal, each lower before its
upper, then the predicate; Function argument before result; product children
in source span order. Closed normalization remains owned by the existing
canonical normalizer. `yu-types` uses its existing transaction/overlay,
failure-epoch, validation, planning, and atomic commit/rollback path. A failed
attempt returns no scheme/checkpoint and publishes no partial component or
`SolvedModule`.

Every valid-session indexed invocation begins one finalization attempt. Any
validation/callback-equivalent/commit failure after that point rolls back
logical overlay state and advances the private failure epoch once. A
representable failed reserve reconciles the actual retained capacity even
when the reserve returns `Err`; the session may be retried and the next
successful checkpoint includes that capacity. Checked aggregate overflow
transitions the session to terminal `IdentityExhausted`, advances the epoch
once, and poisons it; later calls short-circuit without another epoch change.
Unwind restores logical state, reconciles representable capacity, advances
the epoch once, then resumes the original panic. Solver-side producer failure
before entering `yu-types` does not advance its failure epoch. Only
`IdentityExhausted` maps to the existing solver availability error; no new
public variant is added.

## 4. Semantics held fixed

For every input admitted by the eventual resource envelope, preserve:

- Oracle-observable scheme shape and current F5c Q/R eligibility,
  classification, namespaces, encounter order, and lower-before-upper
  restoration;
- §25/§34 normalized canonical ordering and the authoritative §36 counter
  meaning and work ordering;
- component draft/finalize/install ordering and all existing F4 facts,
  diagnostics, and counters;
- §44's first canonical normalized positive-Union member as the sole public
  representative fact, with all remaining members as private live constraints
  under the same occurrence/cause;
- one transaction for representative publication and every private member
  constraint, so later failure leaves no fact, receipt, provenance, or
  routed-use marker.

The indexed API changes construction, not the resulting closed scheme or
observable route. Existing shallow witnesses must compare the old and new
closed schemes, observations, counters whose contracts remain authoritative,
and public route/fact projections exactly.

The existing F5a callback contract remains unchanged, including acceptance of
caller-ordered selections/subsets of the created R bounds (including reordered
and subset cases). The proposed indexed F5c producer emits dense bounds in
`Q + i` order and must produce the same scheme for that input form; this does
not narrow or replace the callback's broader accepted-input contract.

## 5. Resource, work, and failure boundary

Structural depth itself has no fixed cap in this proposal. Every flat node,
child entry, Q/R entry, root, frame, mapping, and normalization/work lane
still has a finite representable range and fallible growth. Use checked index
conversion, `try_reserve`-style growth, and existing `IdentityExhausted`
mapping; never truncate, approximate, or silently omit a child.

Keep two different limits distinct:

- **Draft-size limits** cap positive/negative node admissions; stored
  child-ID entries and logical parent-to-child incidences separately; Q/R
  bounds, roots, descriptor words, and live intermediate graph size before the
  corresponding lane grows. Frames, maps, and finalizer scratch are bounded
  by these admitted dimensions but still require physical-lane accounting.
  Logical incidences are separate because overlapping spans can make them
  exceed the stored child-array length.
- **Repeat-work limits** use one solver-owned checked meter. One unit is one
  actual task/node visit, inspected child or bound incidence, summary/memo
  edge traversal, candidate-pair check, structural node-pair comparison,
  trace/frame inspection, R fixed-point owner check, or copied element. Charge
  immediately before each operation or loop iteration; charge both the outer
  candidate-pair check and every structural comparison task it schedules.
  Candidate-set clones, copied trace hops, replay output, and other bulk copies
  charge each copied entry. A failed early-exit comparison or trace scan charges
  the work actually performed. Optional per-family subtotals may aid
  diagnosis, but do not create separate independent limits. This deterministic
  logical-work meter is not a timing or hash-table-collision counter. It stops
  path amplification and repeated root-local work even when the final flat
  draft stays small; do not pass fuel across the `yu-types` API.

  Charge child-edge inspection and task scheduling before each operation,
  separately from comparison-task pops and stack-slot/storage admission.
  Early mismatch leaves scheduled but unpopped tasks charged for scheduling,
  not comparison. Charge each bounds-row endpoint copied before a clone and
  separately admit storage; borrow an external session row where possible.
  On epoch wrap, charge every entry before `root_edge_marks.fill(0)` or
  `F5cComponentExpansionMemo::begin_visit`'s `visit_epochs.fill(0)`, called by
  `propagate_active_row` and `invalidate_row`. Exhaustion precedes either fill
  and takes the normal error/rollback path. In `record_reentry`, charge active
  entries examined until the first owner match or end; on a match, charge all
  copied path hops, then only the prefix `.any` inspects through the first
  Function hop, or the full path if none exists. Copy and guard lengths differ.

  User-approved meter lifetime (2026-09-25): use one solve-wide meter for
  charged F5c draft work across components in one solve. It gives a hard ceiling
  on that charged scope and prevents component-count bypass. Its cost is that a
  large collection of individually small components can exhaust the shared
  budget; per-component resets avoid that case but leave aggregate work
  proportional to component count. The user approved this lifetime only; no
  numeric cap follows from that choice. Indexed-finalizer-local work,
  F5e Function-product generation, §44 per-use routing, and physical
  peak/storage have separate scopes and accounting; this meter does not cap
  total invocation work or peak memory. The resource subgate must measure
  ordinary workloads before selecting a supported numeric boundary.
  Do not reset implicitly at a root or component boundary.

The 2026-09-25 architect adjudication found the prior `k!` alpha-permutation
concern stale: the authoritative producer-order addendum removed that ranking
path, and current-source search found no `unordered_root_keys`. Do not add a
budget lane for deleted work. Authoritative F5 §36 supersedes the old §34
complexity claim with `O(N+W+C)`: `N` is finalized nodes, `W` descriptor words,
and `C` the exact prescribed word comparisons. The 2026-09-24 normalization
counter addendum retains that bound and adds canonical preordering `O(N+W)`.
Charge each prescribed §36 word comparison at its existing site, preserving
the exact public `C` schedule. Privately charge radix frame schedule/pop/checks,
bucket reset and 257-symbol prefix/bucket scans, histogram/distribution
item/symbol reads, bucket-position/cursor checks, swaps/writes, and child-frame
checks; small insertion-sort symbol comparisons and key moves; stable-merge
tail copies, full write-back, rank/key assignments, adjacent duplicate tests
and dedup writes; and flatten/rebuild/compaction node and incidence visits.
Preordering charges never alter public counters. Pre-growth `N`/`W` admissions
bound stored nodes/words and their bounded-pass visits; individual operations
still consume private work or prescribed `C` at their sites. Together these
bound normalization by `O(N+W+C)`, subject to future source proof and witnesses.
The indexed finalizer must validate and build each
supplied node/edge a bounded constant
number of times, with scratch bounded by the same input dimensions. These are
conditional complexity claims, not facts established by the current callback
or by using flat IDs alone. The source audit must verify each pass and every
charge site.

This F5c meter covers pre-finalization draft production and normalization
inputs, not later per-use expansion of a finalized scheme. The Function
Cartesian loops in `InferenceSession::closed_parts` visit generated
argument/result pairs and append a live Term for each pair; that path has a
checked multiplication but no pair-visit meter. Keep its memoization and
resource accounting in the F5e gate rather than charging it to this draft
meter. Likewise, the §44 route operation keeps its separately specified
transactional rollback contract; this source map does not claim that the
end-to-end per-use failure-lane gate is closed.

No numeric size/work threshold is selected here. The repository source corpus
has now been inspected, but it establishes only a repository-bounded surface
envelope: it does not connect source bytes or expected signatures to expanded
solver graph size or repeated work, and it is not evidence that external Oracle
inputs have the same distribution. Existing synthetic stress tests cover deep
traversals and selected lane accounting, but not every proposed charge family
or a future flat producer/finalizer. A separate reviewed resource subgate must
choose limits above the measured envelope, map pre-step/pre-growth exhaustion
to existing `IdentityExhausted`, and prove no partial publication. Until that
subgate is closed, this design does **not** claim a concrete deterministic
practical-work ceiling or general pathological-work rejection. This boundary
is intentionally narrower than full F5c/F5e closure.

The proposed private failure invariant is that work-meter exhaustion stops
new forward work and returns existing `IdentityExhausted` without partial
publication. Cleanup is not interrupted by the exhausted forward meter.
Future implementation must size-admit each undo/invalidation journal entry as
an explicit separate dimension before its reversible mutation; final node/edge
counts do not bound the journal. No fallible operation may separate a private
mutation from its rollback-visible undo record. In the current source sequence,
`memo.admit` followed by fallible `observe_walker()?` before the `admitted_keys`
push exposes this gap. Future implementation must close it; if admission can
partially mutate and then fail, journal enough prior state before that mutation
to restore every failure path. A focused failure/exhaustion witness must cover
this exact mutation-to-journal boundary. Cleanup must be bounded by admitted journal
and memo entries, require no fallible reserve or allocation after exhaustion,
and remain uninterruptible by the forward meter. It must restore memo
admissions, invalidations, nodes, and edges, then return existing
`IdentityExhausted` without a public result. Whether invalidation and
reinsertion can restore state without allocation, and whether their capacity
is sufficient, remain unverified. The co-resident memory peak is unmeasured;
source proof and exhaustion witnesses remain required.

The existing F5/F4 resource contracts are not removed by this draft. Every
new or retained physical lane remains classified and counted exactly once;
solver input/scratch and `yu-types` finalizer scratch must be reconciled at
their true simultaneous peak, including partial failure and retained capacity
on retry. Existing §26/§34 counters, capacity equations, and required scale
families remain in force unless a later, separately reviewed addendum
explicitly supersedes them.

The solver-side physical-lane audit starts with: positive and negative flat
node arrays; positive and negative child-ID arrays; recursive-bound/root
arrays; component-summary memo nodes/edges; root-local Q/R census, trace,
fixed-point, incidence and replay task/value lanes; normalization descriptors,
sort/dedup scratch, compaction maps/frames and final root maps; and the outer
all-member draft vector. Co-resident `build_inner` and
`non_generic_closure` temporaries also include raw/retained bounds and row
copies; previous/candidate/survivor/reachable/reference/adjacency/connected
sets and frontiers; replayed bounds/predicate; traces and Q/R maps;
comparison/work stacks; memo restoration lanes; and all-member drafts while
finalized drafts accumulate. This is a minimum to verify, not a measured
complete peak; `C + 1` bounds R rounds alone, not repeated round work or peak
residency. The future lane ledger must record lifetimes, pre-growth
admission, actual capacities after reserve success or failure, cleanup owner,
and overlap at §26 snapshots. Verify against every constructor, nested
payload, transfer, `collect`, clone, failed reserve, and
drop in source; it is not permission for untracked local temporaries. In
`yu-types`, add the positive/negative source-ID-to-draft maps, DFS color and
frame arrays, mapped child lanes, bounds maps, existing overlay/draft lanes,
and commit planning/rollback scratch to its physical-lane ledger. Each
fallible reserve is reconciled against actual capacity before append or error
propagation.

Use the existing §26 O(1) event/snapshot boundaries. Track every flat input
lane and live work lane through the existing solver resource owner; do not
scan all drafts or sibling lanes on a capacity event. All component drafts
must coexist before the first finalization call. Immediately before that
call, release/clear only memo lanes whose current ownership ends, then take
the authorized all-drafts snapshot. Freeze:

```text
solver_semantic_baseline = semantic_current - current_closed_retained_bytes
solver_session_baseline  = session_current  - current_closed_retained_bytes
semantic_candidate_peak  = solver_semantic_baseline
                          + yu_types_checkpoint.peak_bytes_during_call
session_candidate_peak   = solver_session_baseline
                          + yu_types_checkpoint.peak_bytes_during_call
```

While `yu-types` borrows the input, solver lanes are immutable. On success,
require checkpoint-before to match the pre-call closed scalar, replace the
scalar with checkpoint-after, account `self.drafts` growth, and take the
existing post-`DraftMember` sample. On error there is no successful checkpoint
and no new solver post-failure sample; the consuming solve returns no module.
The independent test ledger must enumerate physical lanes and reconcile
transfer, release, failed-reserve retained capacity, retry, and same-time
peaks without adding historical peaks from non-overlapping owners. In
`yu-types`, observe actual capacities after every reserve return (success or
failure) before append/propagation; on an unrepresentable aggregate, mark the
session exhausted without logical commit, and preserve the original panic on
unwind.

## 6. Proof and code-size tradeoff

This proposal removes the fixed-depth threshold, build-profile/caller-stack
calibration, and proof that every recursively owned success/error value stays
below that threshold. Cleanup reasoning becomes: accepted deep data consists
of flat scalar/index containers, so dropping the ownership graph does not
recurse through its structural depth.

It does **not** remove proof of producer parity, Q/R and normalization
determinism, index validity, no-orphan/acyclic validation, checked allocation,
simultaneous peak accounting, finalizer rollback, route atomicity, or bounded
work. The hidden indexed API, arrays, accounting, and failure tests may grow
the implementation before old boxed paths can be removed; there is no
line-count reduction claim. Keep the new producer/finalizer bridge in
dedicated modules, and after parity is established remove obsolete boxed
representations, reconstruction paths, and depth-probe-only machinery rather
than retaining two production authorities.

## 7. Required review and implementation gates

This is an M3 cross-crate construction/ownership/resource design. Before user
approval, independent review must cover:

- `compiler_referee`: accepted-input parity, all recursive ownership/drop
  paths, normalization compaction, producer Q/R/order invariants, failure
  cleanup, index/lifetime invariants, transaction and §44 publication;
- `spec_auditor`: exact F5/F5b supersession scope, all preserved contracts,
  all seven public item declarations/traits, ordinal and failure-epoch rules,
  error mapping, and test obligations;
- `performance_auditor`: successful-path traversal/allocation cost, work
  limits, retained and co-resident peak accounting, and resource-test budget.

The round converges only with no accepted blocking/major findings. Any repair
must be one batched design-document update followed by delta review of the
accepted findings. Builds and broad tests are not run for this design-only
gate.

Before an implementation proposal can be approved, its evidence plan must
include:

- exact old-callback/new-indexed parity for shallow schemes, including
  positive/negative Functions, normalized duplicate/shared Union/Intersection
  children, Q/R, alpha-equivalence, and counter order;
- malformed finalizer inputs: wrong-polarity/out-of-range IDs, overflowing or
  out-of-array spans, invalid IDs anywhere in child arrays, Q references
  outside `[0,Q)`, R bounds whose entry `i` is not ordinal `Q+i`, R references
  outside `[Q,Q+R)`, structural cycles, shared DAG/repeated edges, and
  orphan-node rejection;
- finalizer failure injection before handles, during each new scratch lane,
  validation, planning, reservation, and commit; invalid-input failure epoch,
  exactly-once epoch changes, terminal poison and later short-circuit,
  retained-capacity retry, unwind rollback preserving the panic, and no
  published handle/scheme/checkpoint on failure;
- F5c producer witnesses for forward/reverse/rotated roots, first-surviving
  guarded R order, root-local cache exclusion, Q census and eligibility,
  lower-before-upper restoration, and final post-normalization compaction with
  shared and duplicate members; assert final unreachable-R pruning removes
  zero owners and all emitted Q ordinals are referenced; include unused-Q and
  unreachable-R internal-invariant witnesses; compare first-surviving order
  and alpha-normal output against pre-refactor producer fixtures;
- deep positive and negative Function chains through the production producer,
  indexed finalizer, result drop, draft drop, and checked-error cleanup on a
  small stack; no deep path may use recursive `Box` reconstruction;
- §44 success and late private-member/provenance failure, with full public and
  private route restoration and the canonical first-member projection;
- the independent per-lane resource ledger at all-drafts coexistence and
  solver-plus-finalizer same-time peaks, plus scale/work witnesses for each
  admitted-size and repeated-work dimension before the numeric resource gate
  closes.
- retain all F5 §16 source witnesses and §26 scale families (independent
  identities, alias uses, shared/independent acyclic graphs, guarded recursion,
  normalization, and arena factorization), plus the §34 mixed-height and
  exact-permutation-counter witnesses; the stack-safe migration does not
  replace these contracts.

The source audit must map every high-volume repeat loop to a charged-work
family and show that finalizer node/edge passes are bounded by admitted-size
limits. The old `unordered_root_keys` permutation family is excluded because
the authoritative producer-order decision removed it; do not reintroduce it
as a guard or counter.

The resource subgate must record the corpus selection and surface-size method,
distinguish source size from inferred/expanded solver size, and label the
resulting margin as repository-bounded unless a representative external Oracle
corpus is available. Scale witnesses must report admitted nodes, stored
entries, logical incidences, roots/bounds, each charged-work subtotal, peak
co-resident bytes, and the first pre-growth/pre-work rejection point.

If approved, implementation is still staged and reviewed separately. First
replace the producer-owned recursive draft boundary and normalization rebuild
with flat IDs while preserving existing output on bounded fixtures; then add
the `yu-types` indexed transaction and validation/rollback evidence; then
exercise deep success, checked-error cleanup, and §44 later-member/public
failure. Stop and return to design on any accepted-input mismatch, recursive
success/error cleanup, unaccounted simultaneous capacity, unbounded work, or
partial publication. Do not claim F5c/F5e complete until their separate
source, resource, public-observation, and scale gates close.

## 8. Open decisions after review

The initial M3 reports found the flat/indexed boundary directionally sound but
not approval-ready. The primary accepted the API/input, failure-epoch,
normalized compaction, Q/R producer-order, simultaneous-accounting, and
witness-coverage findings; these are reflected in §§2–7. The performance
review's `k!` alpha-permutation concern is rejected as stale: the authoritative
producer-order addendum removed that path, and current-source search found no
`unordered_root_keys`. Shared-summary path expansion and root-local
incidence/replay plus R fixed-point repetition remain live risks. The
architect recommends admitted-size gates plus one solver-owned charged-work
meter. The subsequent source/corpus investigation in §13 confirms that numeric
thresholds remain unsupported: repository fixtures do not expose expanded
solver work, and no external corpus is available in this workspace.

The source map now makes the meter units explicit. Following a read-only
architect consultation and the user's stated priority for Oracle-compatible
practical inputs with a lightweight path and rejection of pathological work,
the primary's recommendation was one solve-wide meter for charged F5c draft
work across components. The user approved that meter-lifetime choice on 2026-09-25. It
prevents component-count bypass of the charged F5c draft-work ceiling but can
reject a large ordinary solve, while per-component resets preserve
many-small-component workloads but leave aggregate charged F5c draft work
proportional to component count. This approval fixes only meter lifetime; it
does not select a numeric cap or authorize an API or production code.
Indexed-finalizer-local work, F5e
Function-product generation, §44 per-use routing, and physical peak/storage
remain separately scoped and accounted; neither total invocation work nor
peak memory is capped by this meter.
The current evidence does not establish a numeric margin or which workload is
ordinary. Keep the numeric cap and supported-input boundary open until measured
scale evidence can be independently reviewed. Do not infer a reset boundary
from implementation convenience.

The user approved solve-wide accumulation for charged F5c draft work across
components on 2026-09-25. This fixes meter lifetime only and selects no numeric
threshold or candidate implementation by itself. The earlier first-stage
investigation approval likewise did not authorize the candidate. The user
subsequently gave explicit approval for the revised sequence recorded in §15:
after focused M3 review, build a non-shipping candidate using this proposal,
then gather resource evidence from that candidate before choosing a numeric
support boundary. This supersedes the former requirement that all numeric
thresholds be selected before any candidate implementation. It does not waive
independent review or separate user approval of the eventual supported-input
boundary, and it does not make a candidate accepted or releasable.

The candidate remains constrained by §§2–7: preserve Oracle-visible schemes,
Q/R and canonical order, §44 representative projection and atomicity, and exact
public observation; use flat indexed data and explicit worklists through error
cleanup/drop; retain checked index conversion and fallible growth; and keep
`lib.rs` as orchestration. Structural depth has no fixed cap. No numeric
draft-size or repeat-work threshold is selected before candidate measurements,
and no practical acceptance or pathological-input claim may be made meanwhile.

After candidate implementation, measure the actual logical work and physical
lane capacities/retained/peak values at the §26/§34 boundaries, with practical
inputs and scale cases. Physical reconciliation is a hard stop before calling
the implementation gate complete or production-ready. If the observed work,
storage, failure behavior, or Oracle parity is not safe and proportionate,
stop and return to design; do not ship by treating fallible allocation alone as
a resource policy. Independently review the resulting numeric support boundary
and obtain separate user approval before production acceptance/release. F5e
Function-product and §44 per-use resource/rollback gates remain separate.

The prior first-stage source and charge-site investigation remains useful
background evidence, but the candidate is now the next measurement source. The
old diagnostic campaign used seven of eight process invocations; it does not
provide a suitable budget for the candidate campaign. Set a fresh bounded
measurement plan under `rules/performance.md` before running scale probes.

## 9. Initial M3 review and primary adjudication (2026-09-25)

The initial post-write review round used the `compiler_referee`,
`spec_auditor`, and `performance_auditor` roles. The draft was not
approval-ready. The primary accepted and batched these findings:

- Specify post-normalization reachable-node compaction, including canonical
  roots, child order, ID remapping, and shared/deduplicated children (§2).
- Specify exact Q/R ordinal ranges and map equations; separate solver-side
  unrepresentable-index failure from `yu-types::InvalidDraft`; define the
  indexed attempt's epoch, retry, poison, retained-capacity, and unwind rules;
  enumerate malformed-input and failure witnesses (§3, §7).
- State the complete proposed seven-item public API surface and traits, not
  only a reference to another Draft (§3).
- Map the approved census/R/Q/producer encounter ordering and root-local
  cache exclusions to the flat producer; preserve §33 guard semantics in the
  solver while retaining the existing F5a finalizer's acceptance contract for
  structurally valid recursive schemes (§3, §7).
- State the solver/finalizer same-time peak equation, all-drafts sample,
  frozen baseline, no-solver-growth call interval, capacity event owner
  inventory, and retry/unwind evidence (§5, §7).
- Require a deterministic draft-size boundary and charge repeated summary,
  root-local, replay, and R fixed-point work before each operation; choose
  numeric thresholds only after practical-source and focused scale evidence
  in a separate resource subgate (§5, §7, §8).

The performance report's `k!` alpha-permutation finding is rejected as stale,
not as an accepted-input risk: the authoritative 2026-09-23 producer-order
addendum removed the grouped alpha-key pass, and a current `crates/` source
search finds no `unordered_root_keys`. The old handoff mentions are historical.
The compiler review's concern that an unguarded recursive bound must be
rejected by `yu-types` is also narrowed: §33 guard eligibility belongs to the
F5c solver producer, while the existing F5a finalizer accepts a structurally
valid self-reference in `function_field_order_and_recursive_closure_are_observable`.
The indexed API must preserve that existing finalizer behavior; the producer
must still never emit an unguarded retained F5c R owner.

The first batched design repair is reflected in §§2–8. The first focused delta
round found two further major issues; the primary accepted both and recorded
the batched repair in §10. A second focused delta review found no remaining
blocking or major finding in its assigned scope; see §11. Numeric resource
thresholds remain intentionally unresolved. At this earlier checkpoint, the
proposal was considered for architecture/API approval only; it could not
authorize production implementation or claim pathological-work rejection until
the separate resource subgate was closed and approved. The later full-slice M3
review in §14 supersedes that tentative status: keep the proposal Draft until
the gate sequence is resolved.

## 10. First focused delta review and primary adjudication (2026-09-25)

The focused M3 delta round reused `compiler_referee`, `spec_auditor`, and
`performance_auditor` against the accepted findings from §9. The primary
accepted two major findings and repaired them together:

- The approved producer-order addendum requires final unreachable-R pruning
  to be a no-op and every emitted Q to remain referenced. §3 now assigns both
  checks to the F5c producer after normalization, without strengthening the
  `yu-types`/F5a indexed-input acceptance contract; §7 requires unused-Q and
  unreachable-R witnesses.
- §§8–9 mixed architecture approval with production authorization while
  leaving numeric work limits open. They now define two gates: architecture
  approval authorizes only practical-source/charge-site/scale investigation;
  production implementation remains forbidden until the numeric support
  boundary is reviewed and separately approved.

The performance/resource delta review found no blocking or major finding in
its accepted scope: charged-work families, no-premature-bound claim, physical
lane inventory, same-time peak equation, and scale evidence requirements are
documented. It explicitly did not inspect source-wide charge placement or
numeric threshold evidence; those remain in the resource subgate.

## 11. Second focused delta review and primary adjudication (2026-09-25)

The second focused delta round reused `compiler_referee`, `spec_auditor`, and
`performance_auditor` to inspect only the two accepted major repairs from the
first delta round. All three found their assigned finding closed and reported
no remaining blocking or major issue in scope:

- The compiler referee confirmed the producer-owned post-normalization
  zero-prune and dense-Q assertions match the authoritative producer-order
  addendum, leave F5a/`yu-types` acceptance unchanged, and preserve Q/R order
  and §44 publication.
- The specification auditor confirmed architecture/API approval authorizes
  only the resource investigation, while implementation remains gated on
  numeric limits, evidence, independent review, and separate user approval.
- A final narrow specification delta clarified that independent design review
  precedes architecture approval, while source/charge-site investigation
  follows that approval; the specification auditor confirmed the sequencing
  without changing the two-stage authority boundary.
- The performance auditor confirmed the two-stage wording makes no premature
  practical-work or pathological-input claim and preserves the resource
  subgate.

At this checkpoint, the primary proposed marking this proposal Reviewed. The
later full-slice M3 review in §14 supersedes that tentative disposition: keep
the proposal Draft until the resource/implementation gate sequence is resolved.
The user's first-stage investigation authorization is recorded in §12; numeric
resource limits, implementation authority, and implementation/performance
certification remain open.

## 12. User authorization for first-stage investigation (2026-09-25)

The user approved proceeding with this design direction for investigation only.
Authorized work is limited to repository source/corpus inspection, mapping
work and allocation sites, and focused scale/resource measurements within the
repository measurement budget. This does not authorize production-path
prototypes, the proposed `yu-types` public API, semantic/support-limit changes,
or F5 clause supersession. After the evidence is gathered, present the concrete
numeric support boundary for independent review and separate user approval
before implementation.

## 13. First-stage source and scale investigation (2026-09-25)

The approved investigation began with a read-only audit of the repository
corpus and current F5c paths. A later focused probe adds one ignored,
test-only measurement module; no production behavior or API changed. The
worktree was clean at `baa8d78b` before the source-audit record update.

### Practical-source envelope

The stable-core manifest contains 73 cases, including 16 public-signature
fixtures. The 16 `main.yu` files and 16 expected `signature.toml` files total
4,513 bytes; all stable-core `main.yu` files total 10,258 bytes. These are
surface measurements only. The runtime performance corpus has 10 cases but is
not a type-size distribution; the phase2 parser corpus is parser-only. The
repository has no compiler CLI/driver or corpus harness that connects these
fixtures to F5c expanded-node, incidence, or repeated-work measurements.

Some checked-in examples contain higher-order Function signatures, effects,
and small Union/Intersection forms. They establish that those shapes occur,
not a large-component envelope. `tail_self_recursion_100000` is value recursion,
not a recursively defined type graph. No practical corpus witness was found
for guarded recursive type structure or large normalized product families.
Therefore repository fixtures can support a repository-only margin, not an
external-practical-input claim.

### Current charge-site map

The primary source audit maps the future meter and separate storage admissions
to these owners. It closes source discovery, not independent review or a numeric
limit. The exact epoch, reentry, normalization, and rollback charges in §5
govern these rows:

| Family | Current owner/evidence | Repeat-work charge | Separate admitted-size charge |
|---|---|---|---|
| Summary DAG build and maintenance | `F5cComponentExpansionMemo::{push_node,push_children,admit,seed_row,propagate_active_row,invalidate_row}` and `materialize_summary` in `lib.rs` | Each attempted queue admission, work-item pop, child/incidence/root-edge/reverse-parent edge inspected, conflict-journal entry copied, and summary child actually expanded. Charge each entry before `root_edge_marks` or `begin_visit`/`visit_epochs` epoch-wrap fill; repeated propagation/invalidation traversals count again. | Each memo node/child edge, root/parent incidence, materialized flat node/edge, and work-lane slot before growth. Separately size-admit each restoration/invalidations journal entry before mutation. Memoized size alone does not bound unshared output. |
| Root-local expansion and census | `F5cGeneralizer::walk`, `record_reentry`, and `f5c_tree_analysis::Walker` | Each task popped; each bounds-row endpoint copied before cloning; child/member incidence visited and task scheduled; eligibility/order/set entry visited. In `record_reentry`, count active entries through owner match/end, all copied hops on match, and only the `.any` prefix through first Function hop (or full path if absent). | Flat nodes/edges, Q/R census/order entries, traces/hops, direct-target and task/value/frame lanes; separately admit any copied row. Borrow external session rows where possible. |
| Direct-bound deduplication | `F5cGeneralizer::walk` plus `structural_equal` | Each incoming-vs-prior candidate pair, child edge inspected, comparison task scheduled, and comparison task popped are distinct charges. An early mismatch leaves scheduled unpopped tasks charged for scheduling only. This is potentially quadratic in distinct direct endpoints and multiplied by compared structure size. | Candidate/direct-target entries and comparison stack slots; storage admission is separate from work charges. |
| Tree analysis and non-generic closure | `f5c_tree_analysis::{Walker, incidences_*, references_*, occurrences_*, guarded_bound_survives}` and `F5cGeneralizer::non_generic_closure` | Each task/node and child incidence visited; each bounds row/endpoint examined; each adjacency incidence inserted or checked; each frontier pop and neighbor/reference checked. Repeated calls count again. | Adjacency entries, seen/frontier entries, and traversal scratch lanes. |
| R fixed point and trace filtering | `F5cGeneralizer::build_inner`, `guarded_trace_path_survives`, and post-convergence passes | Each round; each copied candidate owner; each owner at each retain/reachability stage; each trace record and examined hop; each lower/upper replay and guard-analysis visit; each frontier/reference; each bound and retained trace revisited after convergence. The monotone candidate set gives at most `C + 1` rounds, not a bound on cost per round. | Candidate/survivor/reachability sets, raw/retained bounds, Q/R maps, trace arrays, and frontier lanes. |
| Replay, substitution, and raw-bound materialization | `f5c_replay::replay`, `f5c_binder_substitution::substitute`, `f5c_materialization::materialize_iterative`, and callers in `build_inner` | Each task/source-node visit and examined edge/member; each emitted flat node/edge; each leaf/container/output element copied. Repeated replay calls charge independently. | Output node/edge arrays, maps, and task/value/parts lanes before growth. |
| Closed normalization and compaction | `f5c_normalization::{flatten,rank_all,rebuild}` and proposed root-reachability compaction | Preserve exact public §36 `C` comparison schedule at existing sites. Privately charge the radix, insertion, merge, dedup, flatten/rebuild, and compaction operations in §5; `N`/`W` admission alone does not charge execution. Together the admissions and work charges cover `O(N+W+C)`. | Raw/intermediate/final nodes, stored child IDs, logical incidences, descriptor words, roots, maps, radix frame/workspace and sort/dedup/compaction lanes; future finite admissions and work cap cover both bounds. |
| Indexed finalizer (proposed) | Current callback `yu-types::validate`, `plan`, and `commit`; indexed method does not exist | For the proposed direct-index path, count each supplied node, child entry/logical incidence, bound, and DFS visit. Prove validation/planning/commit passes touch each indexed item only a bounded constant number of times; this is finalizer-local work, not solver fuel. | Source-ID maps, colors/frames, mapped lanes, overlay, and commit/rollback scratch bounded by input dimensions. |

The Function Cartesian product in `InferenceSession::closed_parts` is
intentionally not a row in this F5c draft meter: it runs after closed-scheme
finalization. It checks `arguments.len() * results.len()` for overflow, then
visits each pair and appends a live Function Term, but has no pair-visit cap;
closed-DAG instantiation memoization/accounting remains an F5e gate. The §44
route's all-private-constraints-plus-representative rollback is also a
separate per-use gate, not proof supplied by the F5c draft meter.

Existing counters mostly describe retained capacities, growths, comparison
subsets, or normalization scratch. They do not expose all task pops, shared
path expansions, R fixed-point rounds, replay clones, or candidate-pair
structural visits. In particular, the existing callback validator's nested
linear membership/duplicate searches cannot justify the proposed indexed
linear-pass claim.

The physical-lane list in §5 is a minimum future verification inventory,
including simultaneous `build_inner`/`non_generic_closure` temporaries and
all-member drafts beside accumulating finalized drafts. Record lifetime,
pre-growth admission, actual capacity after reserve success/failure, cleanup
owner, and overlap at §26 snapshots. Current probes measure neither that
co-resident peak nor repeated R-round work; `C + 1` caps rounds alone. The
second focused M3 delta review accepted the corrected stale §34 claim and
`O(N+W+C)` boundary, then found new BLOCKING/major omissions in epoch scans,
reentry, normalization work, rollback, and peak evidence. The third focused M3
delta round found no new charge-map omission and accepted the mutation-to-journal
visibility gap as an open implementation requirement. This documentation repair
passed fresh focused review with no blocking, major, or minor finding. Only
source-map wording received these focused rounds; earlier architecture review
does not certify the full proposal.

Future implementation and focused review must supply exact-charge witnesses
for scheduled versus popped comparison tasks after an early mismatch, both
`begin_visit` and `root_edge_marks` wrap scans, reentry short circuits, and
normalization operation coverage with §36 public-counter parity. Exhaustion
witnesses must establish restoration without fallible allocation or public
publication. The simultaneous lane ledger and restoration peak need source
proof and §26 snapshot witnesses. None was run or measured for this documentation
repair.

### Scale evidence and remaining limit

The existing synthetic witnesses exercise 1,024 direct rows through summary
admission/materialization, a 2,048-deep alternating Function walk/comparison,
and 4,096-deep iterative replay/materialization/tree analysis on small stacks.
They establish selected traversal feasibility and lane reconciliation, not a
size/work ceiling. The diagnostic below adds one shared-DAG amplification
point and standalone replay lane counts, but many-candidate deep deduplication,
actual R-loop work, and indexed-finalizer passes still lack independent visit
ledgers. The depth-256 finalizer probe is profile/stack dependent as recorded
in §1 and does not bound flat graph size.

An ignored test-only probe measures the current normalizer across deep chains,
wide unique/duplicate-heavy Unions, and multiple roots. It reports raw
flattened node/child slots, existing normalization comparison counters, and
the normalization lane ledger. Selected largest points were:

| Shape | Raw nodes | Child slots | Root slots | Relevant counters | Tracked normalizer-lane peak |
|---|---:|---:|---:|---|---:|
| Function chain, depth 4,096 | 8,193 | 8,192 | 1 | 28,673 word comparisons | 1,972,544 bytes |
| Unique Union, width 1,024 | 1,025 | 1,024 | 1 | 6,143 child; 24,572 word comparisons | 293,224 bytes |
| Duplicate Function Union, width 1,024 | 3,073 | 3,072 | 1 | 1,023 duplicates; 56,312 word comparisons | 547,176 bytes |
| Independent roots, count 128 | 128 | 0 | 128 | 1,150 word comparisons | 24,952 bytes |

These are current-normalizer diagnostic values, not limits for the proposed
flat representation. Raw node slots include members later deduplicated. The
byte peak covers the normalizer's tracked vector lanes; it excludes heap
allocations inside the recursive boxed input/output values and is not process
resident memory.

A follow-up extends the same ignored probe to current summary materialization
and replay. For a synthetic binary shared-summary DAG, depth 12 has only 13
memoized nodes and 24 stored child edges, but materializes to 8,191 output
nodes and 8,190 edges. Its materializer scheduled 12,286 task slots; the
tracked task-lane peak was 512 bytes. This is about 630 output nodes per
memoized node, showing that memo storage does not bound the size of an
unshared boxed result. The 512-byte figure covers only the task lane, not the
materialized tree or all co-resident allocations.

For a Function replay chain of depth 4,096, the existing replay lanes report
12,289 task-slot requests and 8,193 value-slot requests, with tracked peaks of
131,072 and 262,144 bytes respectively. On these successful cases, slot
requests correspond to scheduled task/value entries; they do not count all
structural comparisons, copied output payload bytes, or unrelated owner work.
The probe therefore provides a useful replay-work signal, not a complete
resource ledger.

Static inspection of `F5cGeneralizer::build_inner` confirms repeated R-bound
replay uses the same cumulative memo walker lanes, so a purpose-built
generalizer fixture can expose aggregate replay task/value traffic. There is
no separate counter for fixed-point rounds, candidate-set clone/retain work,
per-owner bound checks, trace-hop checks, or reachability-frontier visits.
Those remain unmeasured; lane counters alone cannot certify the R fixed-point
cost. Substitution and indexed-finalizer work also remain unmeasured here.

The source does give a useful structural bound: the fixed-point loop starts
with eligible re-entry owners and only removes candidates; it never adds one.
Every non-final round therefore removes at least one candidate, so the loop
executes at most `C + 1` rounds for `C` initial candidates. This is a source
inference, not a measured R witness. A round can still replay and inspect
large bounds and traces, so the repeat-work meter must charge each round,
candidate-owner examination, trace record and trace hop, reachability-frontier
visit, plus the underlying replay and tree-analysis visits. Candidate-set
copying must charge the copied owner entries. The
remaining diagnostic budget is one process invocation; a dedicated R fixture
would need a test-only loop observer to count rounds and per-owner checks.
Given the source-level monotonicity proof and the need to keep this diagnostic
small, no additional R probe is added in this slice. Keep the dynamic R work
dimensions explicitly open for independent review rather than implying the
depth-4,096 replay probe covered them.

The combined manual probe command was invoked seven times while its test-only
reporting/assertion code was finalized: five completed diagnostic runs and two
compile attempts that exposed and then fixed test-code issues. An initial
compiler warning was removed before the successful final run. These were
deterministic count/capacity captures, not timing samples. The ordinary
single-threaded `f5c_` suite passed 162 tests with the one manual probe ignored;
the earlier narrower `f5c_deep` check passed two tests. No elapsed-time or
process-RSS measurement was taken. No numeric cap is selected. The resource
subgate still needs the unmeasured R-loop work dimensions and the actual
co-resident lane ledger after a reviewed implementation exists. The probe is
primary-authored and was not independently reviewed; it is diagnostic
evidence only.

Primary disposition: accept the corpus, charge-site maps, and normalization,
shared-summary, and replay probes as repository-bounded diagnostic evidence.
The R loop has a source-level `C + 1` round bound because its candidate set is
monotone-decreasing, but per-round replay/owner/trace work is not measured.
Keep the one-meter design and linear indexed-validation claim conditional as
amended above. The detailed charge-site map remains a primary source-audit
result. Its follow-up documentation repair passed a fresh focused M3 delta
review with no blocking, major, or minor finding; that review does not certify
the full proposal. The separate meter-lifetime recommendation then passed its
own focused M3 delta review after scope/sequence corrections, with no remaining
blocking, major, or minor finding. The user approved solve-wide metering for
charged F5c draft work across components on 2026-09-25. The numeric cap,
supported-input boundary, and resource evidence remain open. The subsequent
full-slice review and primary adjudication are recorded in §14; do not treat
the earlier proposed next step as active until the gate-sequence decision is
resolved.

## 14. Full-slice M3 review and resource-gate sequencing (2026-09-25)

A full-slice M3 review by `compiler_referee`, `spec_auditor`, and
`performance_auditor` found no issue in the compiler and performance scopes.
The specification review found one major circularity and one minor stale-status
statement. The major is accepted: §8 requires a concrete numeric supported-work
boundary, independent review, and user approval before production implementation,
while §13 requires the actual co-resident solver/finalizer capacity ledger after
implementation. F5 §§26/34 require physical-lane reconciliation and peak
evidence; current source/corpus and synthetic probe evidence cannot establish
the proposed architecture's physical peak or a practical numeric margin.

Read-only architect, specification, and performance consultations agree that
current evidence does not support choosing a numeric cap. The unresolved
sequence cannot be repaired by claiming the pre-implementation logical meter
certifies post-implementation physical capacity. A possible sequence is to
review and approve a logical-work/support boundary before implementation, then
make physical lane reconciliation a hard stop acceptance gate after
implementation. If a test-only prototype is needed to select that logical
boundary, it is outside the current authorization and requires a new bounded
prototype scope and measurement budget. The earlier diagnostic campaign used
seven of eight process invocations; its one remaining invocation is
insufficient for prototype work and practical-margin evidence. No prototype,
probe, or test ran during this review.

Primary disposition: retain Draft status and stop before production code, public
API work, numeric-cap selection, or further resource probes. The user must
choose whether to authorize a bounded non-shipping test-only measurement
prototype with a fresh budget, or to defer that route and leave the resource
gate open while another evidence path is developed. Any revised gate ordering
also needs explicit user approval before becoming durable design authority.
The minor finding is closed here by correcting the tentative status above. The
solve-wide meter-lifetime approval remains in force and is not reopened. This
was the status at the close of that review; the user later approved a revised
candidate-before-boundary sequence, recorded below.

## 15. User-approved candidate-before-boundary sequence (2026-09-25)

After the §14 review, the user approved the recommendation to build a
non-shipping implementation candidate using explicit stacks, then measure that
candidate before selecting numeric resource limits. This resolves the circular
gate sequencing finding, contingent on a focused independent M3 delta review of
the revised sequence before code changes begin.

The user decision approves candidate implementation on `yulang3` for the scope
already specified in §§2–7 and §8. The candidate may be committed and pushed as
an incomplete, non-release checkpoint. It is not accepted as production-ready;
it does not close F5c/F5e, authorize release, or authorize changes to Oracle
semantics, Q/R ordering, the §44 representative/transaction, or the proposed
API beyond the exact draft surface. Do not add a structural-depth cap.

The pre-implementation focused M3 review gate for this sequence is now closed,
as recorded below. The candidate must retain the flat indexed representation and explicit worklists
through producer expansion, normalization, finalization input, failure
cleanup, and ordinary drop; use checked index conversion and fallible growth;
keep `lib.rs` orchestration-only; and preserve all listed parity and atomicity
witnesses. Numeric draft-size and repeat-work thresholds remain unset while
building the candidate. Ordinary focused correctness tests on small fixtures
may exercise the candidate under `rules/testing.md`. Any candidate
resource, scale, or capacity probe requires the measurement plan and review
gate below before its first invocation.

After candidate implementation and before the first candidate resource probe,
prepare a fresh measurement plan under `rules/performance.md`. Specify input
families and sizes; exact logical-work observations, physical lanes, and
F5/F5c checkpoints for capacity, retained, and peak values; environment and
build mode; exact commands; a per-process timeout; total measurement process
count and wall-time budget; stop criteria; and how failures, retries, and
rollback are sampled. `performance_auditor` and the primary must review the
plan before execution. The prior campaign's remaining single process
invocation is insufficient for this separate candidate campaign.

The default campaign maximum is eight measurement process invocations and ten
minutes total wall time. A plan exceeding either limit requires written
`performance_auditor` justification and primary approval before execution; a
plan exceeding sixteen invocations or twenty minutes also requires explicit
user approval. Only dedicated resource-capture invocations consume this
campaign budget. Correctness tests and builds that do not capture resource
samples remain separate and governed by `rules/testing.md`.

Under the reviewed plan, measure actual logical work and physical lane
capacity/retained/peak values at the required F5/F5c boundaries, including
practical inputs and scale behavior. Physical reconciliation is a hard stop
before the implementation gate can be called complete or production-ready.
Any proposed numeric supported-input boundary must pass independent review and
receive separate user approval. If the candidate cannot preserve oracle parity,
atomic publication, safe checked failure, or proportionate resource use, stop
and return to design rather than accepting it.

The first focused M3 review of this sequence found one accepted major
measurement-plan ambiguity and one accepted minor historical-authorization
wording issue. A batched documentation repair separated small-fixture
correctness tests from resource probes, made a reviewed pre-probe plan mandatory,
specified its contents and budget rules, and clarified the earlier approvals'
scope. A fresh focused delta review by `spec_auditor` and
`performance_auditor` found no remaining blocking, major, or minor finding;
the `architect` found no issue in the first round. No code, tests, or probes ran
during these documentation reviews.

Primary disposition: the candidate-before-boundary sequence is reviewed and
authorized within the exact draft scope. Candidate implementation may begin in
small module-owned slices, preserving `lib.rs` as orchestration. The resource
measurement plan remains a separate mandatory review gate before any resource,
scale, or capacity probe. Numeric support limits, physical-lane certification,
production acceptance, F5c/F5e completion, and release remain open.

## 16. Fixture-only flat-draft normalization checkpoint (2026-09-25)

The first code slice adds crate-private polarity-specific node IDs, flat node
arrays, child spans, predicate/bound roots, and insertion-order metadata in
`crates/yu-solver/src/f5c_draft.rs`. The new `normalize_flat` path in
`f5c_normalization.rs` feeds the existing iterative ranker, then uses an
explicit worklist to emit a dense, root-reachable flat result after
Union/Intersection deduplication. It does not rebuild boxed `F5cPositive` or
`F5cNegative` values. `lib.rs` changes only by one module declaration.

Focused fixtures compare all five logical normalization counters with the old
boxed normalizer for the same unshared shallow graph containing both-polarity
Functions and Union/Intersection nodes. Separate witnesses assert exact flat
node/child/root output, mixed-height order, duplicate removal, sharing,
multiple-bound order, root/member permutation counter invariance, and checked
rejection of swapped or duplicate source IDs. The raw fixtures are rooted
before normalization; a distinct child subtree becomes unreachable only after
canonical duplicate-member removal and is excluded from the dense output.

Review disposition for this slice:

- Initial compiler/spec/performance review found the insertion-order identity
  bug, unchecked ID conversions, and transient-capacity stats being returned
  after their owner was dropped. The batched repair checks per-polarity source
  IDs, uses checked conversions, and keeps only logical fields in
  `FlatNormalizationStats`.
- The follow-up specification review passed the non-shipping API boundary,
  treating complete physical-lane/co-resident-peak reconciliation as the
  explicitly later §15 resource gate. It requested stronger compound counter
  parity; the additional unshared compound and permutation fixtures close that
  minor test gap.
- The follow-up performance review passed this fixture-only, production-unused
  helper. It classifies the additional input/output/work/scratch lanes,
  `O(N+E+B)` copy/traversal work (in addition to ranking), and shared-child
  worklist scheduling as later measurement/accounting obligations, not as
  evidence of a measured support envelope.
- A compiler review argued that an arbitrary isolated pre-normalization node
  must not change key-write counters. Primary disposition: rejected. §36
  counters count normalization work actually performed on supplied nodes, and
  §2 explicitly compacts after normalization; adding a different raw node set
  therefore changes actual key-generation work without changing the final
  scheme. This is not the required same-input/root/member permutation
  invariance. The final fixtures instead keep every raw node reachable before
  deduplication and test the specified post-dedup compaction.

This is only a fixture-backed building block, not completion of §7's first
producer-boundary gate: production still uses the boxed path, and producers,
replay, substitution, materialization, error cleanup, and ordinary draft drop
have not moved to `FlatDraft`. `FlatNormalizationStats` is logical-only and
must not be used as the production resource ledger. No candidate resource,
scale, or capacity probe or benchmark ran; physical lane capacities,
co-resident peaks, and any numeric boundary remain unmeasured and unset. The
next implementation slice must continue the producer-side migration without
adding implementation detail to `lib.rs`; `yu-types` indexed finalization
remains later in the §7 order.

Focused verification: `cargo test -p yu-solver flat_tests --lib --
--test-threads=1` passed (3 tests), `cargo fmt --check` passed, and
`git diff --check` passed. The broad F5c/F5e and workspace suites remain
deferred to their coherent gate boundaries.

## 17. Occurrence-preserving flat summary materializer checkpoint (2026-09-25)

The next non-shipping candidate slice adds a private summary-ID-to-`FlatDraft`
materializer in `crates/yu-solver/src/f5c_materialization.rs`. It keeps the
existing boxed production materializer active and leaves `lib.rs` unchanged.
The new path uses an explicit task/value worklist, appends polarity-specific
flat IDs in child-before-parent order, preserves Function argument/result and
Union/Intersection child order, keeps the existing pure Function effects, and
records alias incidence before descending without emitting an alias node.
Checked invalid IDs, forward/self/cyclic summary edges, polarity mismatches,
and failed growth return the existing `IdentityExhausted` path. On checked
error, the six append-only `FlatDraft` vectors return to their entry lengths;
capacity growth is retained. Callback side effects are caller-owned, and the
caller must discard candidate mark/order/conflict state after `Err`.

Primary adjudication of the cache-versus-counter finding: the design requires
flat ownership through producer construction and error cleanup, but does not
require summary-DAG sharing before normalization. Existing counter semantics
and per-occurrence incidence order are preserved by expanding each summary
occurrence. Canonical normalization and root compaction then deduplicate and
reuse IDs in the surviving normalized graph. This is the route consistent
with §§2 and 4 without adding a virtual occurrence counter or changing public
counter behavior; no new user decision or authority change was required.

The corresponding cost is material and remains a hard later gate. A recorded
synthetic binary summary DAG with 13 unique nodes and 24 stored child edges
expands to 8,191 flat nodes and 8,190 edges at depth 12. Work and output size
scale with the path-expanded occurrence graph, which can grow exponentially in
the compact DAG size. The candidate currently has checked fallible growth but
no selected numeric admission threshold or complete physical-lane ledger.
Before production connection, implement the §5 solve-wide draft-size and
repeat-work admission, prepare and independently review the §15 measurement
plan, then measure raw output, work, scratch/co-resident peak, and retained
capacity on success and failure. Do not add a structural-depth cap.

Both-polarity raw `Variable(u32)` nodes were added for summary rows;
`normalize_flat` explicitly rejects an unresolved Variable rather than
inventing an extreme or panicking. Focused tests compare the same summary
fixture with the boxed path for complete shallow structure and ordered
incidence traces, exercise a late checked failure and logical append rollback,
reject self/mutual/forward cycles, and compare all five logical normalization
counters for repeated summary edges. Primary closed the remaining minor
malformed-ID-fixture request by direct invariant inspection: root lookup is
checked, every child must be earlier than its in-range parent (implying range
validity and acyclicity), and kind/polarity mismatches return `IdentityExhausted`;
no counterexample was found, and the focused tests already cover cycle and
late-failure rollback.

The M2 delta review used `compiler_referee` and `performance_auditor`; no
blocking or major finding remains for this uncalled candidate helper. The
performance report keeps path-expanded repeat work, flat/normalizer lane
overlap, temporary Union/Intersection child copies, retained capacity, and
numeric admission as production/resource-gate obligations, not certified
properties. The helper adds substantial isolated code while the old boxed path
still exists; after parity and producer migration, remove superseded boxed
materialization rather than keeping two authorities.

Verification: `cargo test -p yu-solver flat_tests --lib -- --test-threads=1`
passed (8 tests), `cargo fmt --check` passed, and `git diff --check` passed.
No broad suite, scale/resource/capacity probe, benchmark, or §15 measurement
plan was run; measurement budget consumed remains zero. The first §7
producer-boundary gate, indexed `yu-types` finalizer, physical resource
certification, F5c/F5e completion, Function-product behavior, and §44 rollback
remain open.

## 18. Fixture-only flat binder substitution checkpoint (2026-09-26)

The next uncalled candidate helper is `substitute_flat` in
`crates/yu-solver/src/f5c_binder_substitution.rs`. It walks from the predicate
and each recursive bound's lower then upper root using an explicit stack and
per-polarity visited flags. It preflights every reachable Variable before
writing, then applies R → Q → polarity-specific elimination, preserving node
IDs, spans, roots, insertion order, and all non-Variable nodes. Shared nodes
are scheduled once; no boxed tree is rebuilt. Checked ID conversions,
node lookup, span arithmetic, and stack growth use the existing availability
error. `lib.rs` and production callers are unchanged.

The focused fixture compares positive/negative Function and
Union/Intersection behavior with the boxed substitution oracle, exercises
bound-only roots and shared subgraphs, proves that an unmapped reachable
Variable leaves every logical draft field unchanged, and shows that an
unreachable unmapped Variable remains untouched. M2 compiler/performance
review closed the candidate-local findings. Primary removed duplicated
insertion-order/topology validation: `normalize_flat` owns that validation,
while visited flags already guarantee this substitution walk terminates on a
malformed cycle. A non-test `cargo check` caught the expected unused candidate
helper; it is explicitly marked unused while it remains unconnected.

This helper is not yet composable with `normalize_flat` on a draft that retains
unreachable Variable scratch: the helper correctly ignores it, but
`normalize_flat` currently scans every inserted node and rejects Variables
before root compaction. Before any producer connection, add or establish a
selected-root isolation/compaction step before normalization, and compare
normalization counters with the boxed selected-root path. Preserve the
post-normalization compaction required by §2; do not feed the helper's raw
orphan-bearing draft directly to `normalize_flat`.

Verification: `cargo test -p yu-solver f5c_binder_substitution --lib --
--test-threads=1` passed (6), `cargo fmt --check`, `git diff --check`, and
`cargo check -p yu-solver --message-format short` passed. No broader suite or
resource/scale/capacity probe ran; measurement budget consumed remains zero.
The successful-path walk is O(N+E+B) for N stored nodes, E reachable
incidences, and B retained bounds, with O(N) flags and at most O(N) stack
slots. Its physical/co-resident peak, repeat-work admission, practical-input
margin, and numeric support boundary remain later §5/§15 gates. This is one
module-owned candidate slice, not closure of the first §7 producer gate.

## 19. Fixture-only selected-root normalization handoff (2026-09-26)

`normalize_flat` now composes with the fixture-only `substitute_flat` result,
which may retain unreachable raw Variable scratch. It marks the predicate and
every recursive-bound lower/upper root, then uses one reverse pass over the
topological insertion order to select their structural children. The existing
per-polarity source maps carry both selection state and the eventual normalizer
ID; this avoids a second pair of reachability arrays and avoids a traversal
worklist. The forward source pass still verifies every insertion ID and every
node edge against its insertion prefix, including orphan nodes, before
unselected nodes are omitted from ranking. Reachable Variables remain invalid.

This is the narrow §18 selected-forest case, not a reversal of §16's counter
decision: raw binder scratch outside the predicate/bound forest is validated
but does not enter the normalizer or its five logical counters. Nodes in the
selected forest retain the boxed selected-root counter schedule. The existing
post-normalization compaction from §2 remains unchanged.

The composed fixture has a positive Function predicate with a two-member
normalized Union, positive and negative Function bound endpoints, and an
unreachable compound containing raw Variables. It compares all five logical
normalization counters with the boxed selected-root oracle and asserts the
complete flat node arrays, child arrays, predicate, and bound roots. Separate
malformed witnesses cover orphan/selected Union and Intersection spans and
both Function edge polarities. M2 compiler-referee and performance-auditor
delta reviews found no blocking or major issue.

Static cost is O(N+E+B) across the selected-root reverse pass, full source
topology/insertion validation, and selected-node conversion. The two source
maps are sized to all raw nodes, even when few are selected; their co-resident
peak with normalizer and compaction lanes remains a §5/§15 resource obligation.
No benchmark or resource measurement ran. The candidate remains disconnected
from production; `lib.rs` is unchanged. The change adds a substantial isolated
helper and test fixture, so later producer integration should remove the
superseded boxed route once parity is established rather than keep both
authorities.

Verification: `cargo test -p yu-solver --lib f5c_ -- --test-threads=1`
passed (176, 1 ignored); `cargo test -p yu-solver flat_tests --lib --
--test-threads=1` passed (9); `cargo test -p yu-solver
f5c_binder_substitution --lib -- --test-threads=1` passed (7);
`cargo check -p yu-solver --tests --message-format short`, `cargo fmt --check`,
and `git diff --check` passed. A full single-threaded yu-solver library run was
started, reached the unrelated F4 scale matrices, then was interrupted after
the 4k bounded-cycle case passed and the F4 chain matrix began; no failure was
reported before interruption. This leaves the full library suite unverified.
Measurement budget consumed remains zero. Continue the producer-side flat
candidate with replay; the §5/§15 resource gate, production acceptance,
indexed finalizer, F5e Function products, and §44 rollback remain open.

## 20. Fixture-only flat replay candidate (2026-09-26)

Added an uncalled `replay_flat` candidate in `crates/yu-solver/src/f5c_replay.rs`.
It reads the same immutable source draft on every call, since the R fixed point
replays bounds and predicate under changing candidate masks. Each source edge
occurrence emits its own output occurrence; this preserves boxed replay order
and does not memoize shared DAG nodes. Function effect fields retain the same
replay defaults as the boxed helper. Explicit enter/finish/leave tasks avoid
recursive traversal and reject reachable cycles. Checked failure truncates all
five appended node/child/order lanes; existing destination capacity and
memoized lane request counters are not rolled back.

Fixtures directly compare both root polarities with boxed replay, cover a
repeated shared edge within one root, check elimination/protected-variable and
Function/Union/Intersection order, exercise depth 4,096 on a 64 KiB thread
stack, and force a reachable positive↔negative Function cycle after a child
Union has completed. The failure witness compares quantifier count, predicate,
both node arrays, both child arrays, recursive bounds, and insertion order
before and after rejection. `lib.rs` and production call sites remain
unchanged.

M2 compiler-referee and performance-auditor review converged with no blocker
to accepting this disconnected fixture checkpoint. The reviewer findings are
not production clearances: each invocation allocates and initializes two
active-node arrays sized to the entire source (`O(V)` even for a small selected
root), and occurrence-preserving expansion can be exponential in a shared DAG
and multiplies across candidate masks. The existing replay task/value lanes do
not account for these arrays or output-draft growth. The production path must
include those costs in §5 size/repeat-work admission and §15 co-resident peak
evidence before wiring this helper; failed truncation also retains destination
capacity. No reuse strategy, numeric bound, or resource margin is selected by
this candidate review.

Verification: `cargo test -p yu-solver --lib f5c_flat_replay --
--test-threads=1` passed (4), `cargo test -p yu-solver --lib f5c_replay --
--test-threads=1` passed (6), `cargo fmt --check`, and `git diff --check`
passed. No broad suite, benchmark, or resource probe ran. Measurement budget
consumed: zero. This remains a fixture-only replay candidate, not completion
of §7's first producer gate or of F5c/F5e. Next: compose the candidate with
flat substitution and selected-root normalization against the boxed oracle
before connecting production callers.

## 21. Composed replay/substitution/normalization fixture (2026-09-26)

The fixture-only composition now runs flat replay for the predicate and both
recursive-bound endpoints, then `substitute_flat`, then `normalize_flat`. A
boxed path starts from the same flat source expanded by the existing test
helper and applies the same masks, Q/R maps, elimination sets, and boxed
normalizer. It compares the final predicate, lower/upper roots, quantifier
count, bound ordinal, and all five normalization counters.

The witness uses repeated positive Union and negative Intersection members,
Q row 2 → Q0, R row 3 → R1, and distinct positive/negative rows that survive
replay and are removed by the binder-substitution elimination phase. Before
normalization it asserts repeated source edges became distinct flat output
IDs. After normalization it checks every emitted node and child entry is
reachable from the predicate or retained bound roots, output IDs are dense,
duplicate members are absent, and canonical R1 nodes are shared between
roots.

That last assertion exposed a candidate defect: ranking had already assigned
equal normalized nodes the same `(height, rank)`, but flat rebuild still
emitted one output ID per source node. The rebuild now scans the already
allocated `sort_scratch` in height/rank order to record each key's first node,
then reuses that output ID across roots. This adds one O(N) pass and constant
map checks/writes; it adds no allocation or recursive walk. The selected-root
normalization fixture's expected arrays were updated from duplicate leaf IDs
to canonical shared IDs. M2 compiler-referee and performance-auditor delta
review found no actionable issue.

Verification: `cargo test -p yu-solver --lib flat_tests --
--test-threads=1` passed (10), `cargo test -p yu-solver --lib f5c_replay --
--test-threads=1` passed (6), and `cargo test -p yu-solver --lib
f5c_binder_substitution -- --test-threads=1` passed (7). `cargo check -p
yu-solver --tests --message-format short`, `cargo fmt --check`, and
`git diff --check` passed. No full suite, benchmark, or resource probe ran;
measurement budget consumed remains zero. Production wiring, §5/§15 admission
and peak certification, indexed finalization, F5e products, and §44 rollback
remain open. Next: compose flat summary materialization with this downstream
candidate pipeline before production wiring; review the exact §15 plan before
any resource probe.
