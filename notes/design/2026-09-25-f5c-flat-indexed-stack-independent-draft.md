# F5c flat indexed draft and stack-independent finalization

Status: Architecture reviewed; first-stage investigation approved (2026-09-25); primary source charge-site extension awaits focused review; numeric resource boundary and implementation approval remain open
Scope: F5c structural-depth stack use from live expansion through closed-scheme finalization and cleanup
Related authority: F5 §§14–16, 24–26, 32–36, 43–44; F5b closed-finalization accounting amendment §§2, 6, 9
Decision: investigate flat solver-owned drafts and a `yu-types`-owned indexed finalization transaction; no production implementation or API approval
Supersedes: proposes to replace the bounded boxed-draft candidate in `2026-09-24-f5c-bounded-boxed-draft-gate-draft.md` and the conditional Boundary A preference in §9 of `2026-09-23-f5c-indexed-finalization-accounting-boundary-draft.md`; no existing authority is superseded before user approval

## 1. User direction and decision boundary

The user chose to investigate support for structurally deep F5c schemes using
explicit stacks rather than a fixed structural-depth threshold. This is
authorization to prepare and review a design, not approval of a new `yu-types`
API or production implementation.

On 2026-09-25, the user approved the first-stage investigation of this
direction: inspect practical source inputs, source charge sites, and focused
scale behavior. This does not approve the proposed public API for implementation,
select numeric resource limits, or authorize production code.

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

  The meter's accumulation lifetime is not selected yet: a solve-wide meter
  gives a hard per-invocation ceiling but can reject a large collection of
  individually small components; resetting per component preserves those
  components but leaves aggregate work proportional to component count. The
  resource subgate must choose and test this observable boundary together with
  the numeric cap. Do not reset implicitly at a root or component boundary.

The 2026-09-25 architect adjudication found the prior `k!` alpha-permutation
concern stale: the authoritative producer-order addendum removed that ranking
path, and current-source search found no `unordered_root_keys`. Do not add a
budget lane for deleted work. Closed normalization retains its authoritative
§34 `O(N + Σ k log(k+1))` comparison contract; with node/edge admission
limits, its work is bounded by the admitted normalized graph. The indexed
finalizer must validate and build each supplied node/edge a bounded constant
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
all-member draft vector. This is a minimum inventory to verify against every
constructor, nested payload, transfer, `collect`, clone, failed reserve, and
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

The source map now makes the meter units explicit, but its accumulation
lifetime is a separate observable choice. A solve-wide meter gives one hard
per-invocation ceiling and may reject many individually small components; a
per-component reset preserves such workloads but leaves aggregate work
proportional to component count. Select and test this together with the numeric
threshold; do not infer a reset boundary from implementation convenience.

After the exact proposed §24 API, producer/finalizer ownership and parity
obligations, failure-epoch rules, and accounting boundary have passed
independent design review, present the user with two distinct gates. First,
the user may approve the flat-draft ownership
boundary, indexed API shape, and deterministic draft-size/repeat-work
mechanism while numeric thresholds remain deferred. That approval authorizes
only the practical-source, charge-site, and scale investigation in the
resource subgate; it does not authorize production code, prototypes on a
shipped path, or any claim of a deterministic practical-work ceiling or
pathological-work rejection. The resource subgate must select numeric limits,
show their practical-input margin and scale behavior, identify any F5 clause
that needs supersession, and pass focused independent review. Only after the
user separately approves that completed support boundary may this proposal
become implementation-authoritative and production code begin.

The approved first-stage investigation scope is:

1. the indexed cross-crate transaction and flat-draft ownership boundary;
2. the proposed draft-size and charged-work mechanism, with numeric thresholds
   deferred to the resource subgate (none are selected by this Draft);
3. any F5 §14/§24/§26/§34 clauses to supersede (none are silently superseded
   by this Draft).

This records authorization to investigate the architecture direction only.
It does not make the Draft implementation-authoritative; the numeric resource
boundary must pass independent review and receive separate user approval
before production code changes.

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
thresholds remain intentionally unresolved. This Reviewed proposal may be
presented for architecture/API approval only; it cannot authorize production
implementation or claim pathological-work rejection until the separate
resource subgate is closed and approved.

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

Primary disposition: mark this proposal Reviewed. The user's later
authorization for first-stage investigation is recorded in §12; numeric
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
limit:

| Family | Current owner/evidence | Repeat-work charge | Separate admitted-size charge |
|---|---|---|---|
| Summary DAG build and maintenance | `F5cComponentExpansionMemo::{push_node,push_children,admit,seed_row,propagate_active_row,invalidate_row}` and `materialize_summary` in `lib.rs` | Each attempted queue admission, work-item pop, child/incidence/root-edge/reverse-parent edge inspected, conflict-journal entry copied, and summary child actually expanded. Repeated propagation/invalidation traversals count again. | Each memo node/child edge, root/parent incidence, materialized flat node/edge, and work-lane slot before growth. Memoized size alone does not bound unshared output. |
| Root-local expansion and census | `F5cGeneralizer::walk`, `record_reentry`, and `f5c_tree_analysis::Walker` | Each task popped; direct lower/upper row or exact endpoint examined; child/member incidence visited; active-frame comparison; trace hop copied or inspected; eligibility/order/set entry visited. Short-circuit scans charge only reached entries. | Flat nodes/edges, Q/R census/order entries, traces/hops, direct-target and task/value/frame lanes. |
| Direct-bound deduplication | `F5cGeneralizer::walk` plus `structural_equal` | Each incoming-vs-prior candidate pair, plus every structural comparison task popped for that pair, including the mismatching task. This is potentially quadratic in distinct direct endpoints and multiplied by compared structure size. | Candidate/direct-target entries and comparison stack slots. |
| Tree analysis and non-generic closure | `f5c_tree_analysis::{Walker, incidences_*, references_*, occurrences_*, guarded_bound_survives}` and `F5cGeneralizer::non_generic_closure` | Each task/node and child incidence visited; each bounds row/endpoint examined; each adjacency incidence inserted or checked; each frontier pop and neighbor/reference checked. Repeated calls count again. | Adjacency entries, seen/frontier entries, and traversal scratch lanes. |
| R fixed point and trace filtering | `F5cGeneralizer::build_inner`, `guarded_trace_path_survives`, and post-convergence passes | Each round; each copied candidate owner; each owner at each retain/reachability stage; each trace record and examined hop; each lower/upper replay and guard-analysis visit; each frontier/reference; each bound and retained trace revisited after convergence. The monotone candidate set gives at most `C + 1` rounds, not a bound on cost per round. | Candidate/survivor/reachability sets, raw/retained bounds, Q/R maps, trace arrays, and frontier lanes. |
| Replay, substitution, and raw-bound materialization | `f5c_replay::replay`, `f5c_binder_substitution::substitute`, `f5c_materialization::materialize_iterative`, and callers in `build_inner` | Each task/source-node visit and examined edge/member; each emitted flat node/edge; each leaf/container/output element copied. Repeated replay calls charge independently. | Output node/edge arrays, maps, and task/value/parts lanes before growth. |
| Closed normalization and compaction | `f5c_normalization::{flatten,rank_all,rebuild}` and proposed root-reachability compaction | Preserve exact §34 comparison/counter semantics. §34's bounded sorting work is protected by node/child/descriptor admission limits; charge any separate graph/compaction traversal task and incidence per visit. | Raw/intermediate/final nodes, stored child IDs, logical incidences, descriptor words, roots, maps, and sort/dedup/compaction lanes. |
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
amended above. The detailed charge-site map above is a primary source-audit
result; it has not received a fresh independent review. Its accumulation
lifetime (solve-wide or component-local), numeric limits, and resource evidence
remain open. No F5 clause is superseded, no API or numeric boundary is
approved, and production implementation remains unauthorized. Next: get a
focused independent review of the completed charge-site map and proposed
metering units, then resolve the meter lifetime and numeric support envelope
with the user before implementation.
