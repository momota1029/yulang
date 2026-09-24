# F5c indexed finalization accounting boundary options

Status: Draft; not approved for implementation
Scope: solver-owned iterative draft scratch during closed scheme finalization
Related authority: F5 §§7–8, 14–15, 24–26, 32–34, 36, 43–44; F5b closed-finalization accounting amendment §§2, 6, 9
Decision: none
Supersedes: none

## Current authority note (2026-09-23)

This Draft preserves the options and review findings as they stood when it was
written. The later authoritative
[`F5c producer-order and failed-route sampling addendum`](2026-09-23-f5c-producer-order-and-failed-route-sampling-addendum.md)
resolves the former exact-alpha/source-order choice in favor of first-surviving
producer encounter and authorizes one conditional O(1) sample after complete
incoming-route rollback when a physical capacity or counted-owner transition
occurred. Those decisions supersede this Draft's older exact-alpha and
no-post-route-sampling assumptions; this Draft does not reopen or implement
them. Producer parity and bounded/stack-safe normalization, the mixed-height
§25/§36 canonical-order clarification, full failed-route lane accounting, and
Candidate B's API approval remain separate open gates.

## 1. Problem

F5c's iterative row/Term walker still materializes recursively owned
`F5cPositive`/`F5cNegative` trees. A useful stack-safe path must retain typed
indexed nodes through summary registration, root-local generalization, and
`finalize_generalization_draft_raw`. The finalizer callback creates
transaction-scoped `Draft*Id<'tx>` handles whose values are needed to connect
parent nodes to child nodes.

The current F5b accounting boundary gives `yu-types` ownership of closed
finalizer storage and lets `yu-solver` combine a result-attached
`ClosedTypeAccountingCheckpoint` with frozen solver baselines. The callback may
read a prepared draft, but may not allocate, clear, or mutate solver-owned
resource lanes. F5b §9 requires return to design if a cross-crate accounting
callback, a live getter, or another forbidden surface is needed. F5 §24 fixes
the exposed API shape. No implementation may weaken this boundary by treating
`doc(hidden)` as private.

The stack-safe finalizer needs a way to retain the source-node to
transaction-handle mapping while preserving exact simultaneous peak
accounting. An architect review found that preallocated result slots still
need writes during the callback; it is not yet established that the
higher-ranked callback can safely store invariant `Draft*Id<'tx>` values in
solver-owned preallocated storage.

## 2. Invariants shared by any option

- `yu-types` remains the owner of closed arena nodes, transaction-scoped
  handles, validation, and atomic finalization.
- The solver baseline is frozen before finalization. The result checkpoint is
  combined with that fixed baseline using checked arithmetic; unrelated peaks
  are never added.
- Failure or unwind publishes no scheme, partial component, or incoming route.
  Transaction-only handles do not escape and scratch is released or retained
  only under the existing accounting rules.
- Preserve the current F4 aggregate counter meanings and all current F5
  semantics, including exact alpha/permutation behavior, guarded R/Q
  classification, and §44's canonical first-member public Union
  representative with remaining members as private transactional constraints.
- Do not add post-route sampling, public detailed F5e resource accessors, or
  F5e scale claims.

## 3. Rejected candidate: solver-owned result slots

Do not amend F5b §6 to permit solver-owned result-map writes inside its current
`for<'tx>` callback. `Draft*Id<'tx>` values are privately constructed and
invariant in the transaction lifetime. A typed slot allocated outside the
callback cannot safely hold them; fixed capacity does not solve the lifetime
boundary. Lifetime erasure, unsafe conversion, raw-index reconstruction, or a
new hidden accessor is not authorized by this draft. Independent M2 review
found no safe construction under the current API.

The fixed-baseline peak equation would be valid only if the external capacity
remained constant during the callback. That observation does not close the
handle-lifetime problem or the required failure/unwind accounting, so it is not
an implementation option.

## 4. Proposed Candidate: yu-types-owned indexed construction

Add one doc-hidden method to the exact §24 surface:

```rust
pub fn finalize_indexed_scheme(
    &mut self,
    input: IndexedSchemeRef<'_>,
) -> Result<ClosedSchemeFinalization, ClosedTypeFinalizeError>;
```

The exact proposed doc-hidden public item set is one method and seven input
types: two polarity-specific node-ID types, `IndexedChildSpan`, two node enums,
`IndexedRecursiveBound`, and `IndexedSchemeRef`. The input items have public fields so
`yu-solver` can construct them without a builder or callback. Their exact
declarations and trait contracts are:

```rust
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct IndexedPositiveNodeId(pub u32);

#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct IndexedNegativeNodeId(pub u32);

#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IndexedChildSpan {
    pub start: u32,
    pub len: u32,
}

#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IndexedPositiveNode {
    Bottom,
    Int,
    Quantified(u32),
    Recursive(u32),
    Union(IndexedChildSpan),
    Function {
        argument: IndexedNegativeNodeId,
        result: IndexedPositiveNodeId,
    },
}

#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IndexedNegativeNode {
    Top,
    Bottom,
    Int,
    Quantified(u32),
    Recursive(u32),
    Intersection(IndexedChildSpan),
    Function {
        argument: IndexedPositiveNodeId,
        result: IndexedNegativeNodeId,
    },
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

There are no new public traits, error variants, handle accessors, or accounting
getters. The tuple IDs, span, and bound record have exactly the derived traits
shown above; node enums derive `Copy + Clone + Debug + Eq + PartialEq`, and the
borrowed input derives `Copy + Clone + Debug`. Positive and negative IDs index
only their matching node arrays. Union and Intersection spans index the
matching polarity's child-ID array. Function effect fields are fixed
internally to the existing closed pure pair and are not present in the input.
No transaction handle or final closed-arena index crosses the boundary.

`yu-solver` would own five immutable indexed input arrays: positive and
negative nodes, positive and negative child IDs, and recursive bounds. The
quantifier count and predicate ID are scalar fields, not arrays. The arrays
must remain alive and unchanged through finalization, with their actual
capacities reconciled to the solver-owned resource ledger. F5 §26 authorizes
O(1) samples at actual capacity growth and when all drafts coexist. The
current SCC path has neither a growth-event ledger spanning these owners nor
an all-drafts sample before first finalization: its `DraftMember` sample
follows each successful finalization, and the prior F4 sample omits the local
SCC copies and root-local member drafts.

The proposed private ledger keeps checked `semantic_current` and
`session_current` totals, with semantic storage included exactly once in
session storage, plus each aggregate's maximum simultaneous total. A
capacity-owner account stores its class totals and live byte sum; each
capacity-managed lane stores requested slots, observed capacity, slot size,
and its current contribution. Every reserve wrapper reconciles the lane after
`try_reserve` returns, including `Err`, before propagating the error or
appending. It replaces that lane's previous contribution with checked
`capacity * size_of::<slot>()` and updates peaks from same-time totals. Moving
an entire account or lane moves its accounting state without changing global
totals; release subtracts the cached live contribution once. Reclassification
must be explicit and apply a checked delta to each affected total. No event
scans sibling lanes/drafts or adds a historical owner peak. §26 O(1) samples
read maintained totals rather than reconstructing them.

For one lane transition, compute the old/new byte delta with checked
arithmetic, update the lane record, its owner's cached semantic/session sums,
and the corresponding global current totals, then raise peaks. A semantic lane
updates both global totals; a session-only lane updates only the session
total. Owner release subtracts its two cached sums once. The global update
must be complete before an append or an error escapes; a scope guard consumes
the already validated owner sums during unwind, and a moved owner transfers
the guard/account exactly once. Fixed owner/account fields are not additional
capacity-managed lanes, consistent with the F4 byte model.

The event update is O(1) per changed lane and does not require O(1) physical
destruction: dropping nested buffers may take time proportional to their
contents, but ledger release uses the owner's cached live sum. A scope guard
must release each owner exactly once on normal scope exit or unwind; moving an
owner disarms the source guard and transfers its cached account with the
buffers. Any grouped account is valid only if every nested lane updates it on
growth/release and the independent test ledger separately enumerates the
physical lanes. This ownership wrapper/guard mechanism is a design proposal;
its fit across the current root-local containers and its own fixed control
storage still need source-level review.

The physical-owner inventory and proposed classification are:

| Owner | Proposed accounting |
|---|---|
| Local `components`, `internal_uses`, `members`, and `incoming_uses` scheduling copies | Session-only: these copy F2/SCC scheduling data and carry no independent scheme/generalization payload; F4 §13 includes the live F0/F2 plan in total session storage while semantic storage remains a subset. This is an ownership inference to verify at each constructor. |
| Outer `generalization_drafts` vector | Semantic and session: F5 §§14, 26 require draft coexistence/accounting and F4 §13 includes draft scratch in semantic storage. Account outer slots independently of nested member storage. |
| Each member draft's five indexed arrays and active partial root graph/maps/frames | Semantic and session: they are the F5 generalization draft/scratch representation. Account every physical lane at growth. A completed draft moves to the outer vector with its aggregate byte account; a partial graph-to-draft transfer moves only the affected lane/account without recounting. |
| Component-expansion memo and all root-local walker lanes | Semantic and session: F5 §26 names `generalization_scratch`; retain their actual contribution while live and include overlap with prior drafts. On the current memo `clear()` release, subtract capacities actually released, not its historical peak. |
| Root-local key, replay, incidence, eligibility, normalization, and compaction maps/worklists/buffers | Semantic and session as generalization scratch. Register every capacity-managed lane, including nested temporary buffers, then transfer or release at the physical ownership transition. Allocation/error/unwind cleanup performs the same ledger transition. |
| `self.drafts` and existing solver semantic lanes | Semantic and session. `self.drafts.clear()` retains its outer capacity; register slot growth separately. Any existing lane that can grow during this phase must feed the same event-time totals. |
| Existing F4 semantic lanes | Preserve the current classification: bound tables/payload, typed pairs/payload, typed frontier, diagnostic scratch, scheme table, routed provenance, `self.drafts` slots, instantiation scratch, closed bytes, exact bounds, inference-term storage, and route journal contribute to semantic and session totals. |
| Existing F4 session-only lanes | Preserve the current classification: store containers, solver errors, reported-error/cross-kind/routed-use indexes, and F2 batch storage contribute to session totals only. |
| `yu-types` finalization session | Represented in the solver only by `current_closed_retained_bytes`; private lanes and within-call peak remain owned by `yu-types` and arrive through the result checkpoint. |

This table applies approved aggregate meanings to new F5c owner groups; it is
not evidence that the current source observes every allocation. The
generalization-scratch and member-draft classifications follow F5's named
family/draft ownership and F4 §13's semantic subset. The SCC-copy
classification follows F4 §13's F0/F2-plan ownership: copied component,
definition, and use IDs carry scheduling identity, not independent scheme or
generalization payload. If a future constructor adds such payload, that lane
follows its actual semantic owner instead. A source audit must enumerate
every `Vec`, `HashMap`, `HashSet`, and `VecDeque` field and reachable local
constructor in the SCC path, including nested buffers, clones, `collect`,
`to_vec`, transfers, and drops. Current examples include generalizer frames,
sets, path/order/reentries; walker task/value/edge/target/parts/comparison
buffers; normalization keys, adjacency sets and frontier; memo containers and
eleven walker lanes; SCC scheduling copies; indexed member arrays; `self.drafts`;
and incoming-use copies. Trace every existing F4 owner that can grow during
this phase to an event hook, or prove it immutable for the whole phase.

The current source inventory that the indexed path must replace or explicitly
carry forward is:

- `F5cComponentExpansionMemo`: `roots`, `nodes`, `children`, `parent_heads`,
  `reverse_parents`, `incidence_heads`, `incidences`, `root_heads`,
  `root_edges`, `root_edge_marks`, `invalidated_root_edges`, `active_rows`,
  `active_conflicts`, `work`, `conflict_journal`, and `visit_epochs`; plus the
  eleven walker lanes whose actual task/value/edge/target/comparison/parts/
  materialization vectors and set are local to `walk` and its helpers.
- `F5cGeneralizer`: `frames`, `uncacheable_seen`, `provisional_recursive_rows`,
  `admitted_keys`, `active`, `active_set`, `path`, `order`, `order_seen`, and
  `reentries`; each guarded trace owns a nested path vector.
- `build_inner`: raw bounds map and cloned nested bound rows; completed-owner
  set; owner-to-trace map with nested index vectors; non-generic closure and
  worklist; positive/negative incidence and elimination sets; candidate and
  previous/fixed-point sets; replayed/retained trees; reachability/frontier and
  reference sets; retained-bound maps; grouped key forest and owner-bound key
  outputs; surviving-owner/trace sets; retained trace vectors and per-owner
  cloned/sorted traces; recursive/Q/R vectors, sets and maps; first-occurrence
  path map; and final recursive-bound vector. Recursive Function children,
  Union/Intersection children, and canonical key trees also own boxed/vector
  allocations that are not visible in outer-container capacity.
- `F5cKeyForest` and normalization: key `nodes`, `variables`, and
  `variable_set`; branch child vectors; each permutation and label map; the
  unfolded canonical trees and sorted/cloned root keys; normalization key,
  value, and zipped-pair vectors; and incidence/reference traversal outputs.
- SCC staging: copied dependency-order `components`, each component's
  `internal_uses`, `members`, and `incoming_uses`; outer
  `generalization_drafts`; each member's recursive tree; and `self.drafts`.

The future indexed producer is intended to remove recursive owned trees,
materialized canonical trees, and per-node remapping clones. It still needs an
explicit owner for each surviving ID graph, worklist, map, key/ranking state,
bound/trace container, child-span buffer, and temporary. The inventory above
lists named current struct fields and principal `build_inner` families, not
every replacement allocation site. Before Candidate B approval, complete the
following owner/event matrix for the proposed path; after approval, verify
every row against actual code and the independent test ledger:

| Owner group | Initial-capacity registration | Growth and partial transfer | Release, error, and baseline |
|---|---|---|---|
| SCC scheduling copies (`components`, `internal_uses`, `members`, `incoming_uses`) | Register observed capacity immediately after each fallible clone/fill constructor; avoid untracked `collect`/`to_vec`. | Every later reserve updates its lane and session total. | Release at the end of its actual scope. Register `incoming_uses` even though it is created after scheme installation. No copy is live at a finalizer baseline unless its scope overlaps that boundary. |
| Component memo and walker buffers | Memo starts empty or registers any pre-capacity; local walk task/value/edge/target/parts/comparison/materialization owners register as they become live. | Every reserve records actual capacity after `Ok` or `Err`; memo ownership moves between `component_generalization_draft` and `F5cGeneralizer` without changing totals. | Scope guards release temporary walker owners. Memo `clear()` releases all physically dropped memo lanes before the all-drafts sample; producer error/unwind releases each surviving owner once. |
| Root-local analysis and key/ranking owners | Register every map/set/vector at construction, including nonzero-capacity constructors and nested per-owner/path buffers. | Replay/fixed-point/key phases update each actual growth. Transfer graph lanes to compaction/draft owners individually; no untracked deep clone, `collect`, or box reconstruction. | Drop temporary analysis/key owners after their final consumer; their release updates current totals. Class and lifetime are carried to the draft or released before sampling. |
| Per-member indexed draft and outer draft vector | Register the outer slot vector and each of five member arrays as soon as their actual capacity exists. | Array growth updates the member account even if the outer vector does not grow. Moving the complete member account into `generalization_drafts` preserves totals; any partial transfer moves only its lane account. | All five input arrays remain unchanged/live throughout their member's finalizer call and, as required by the approved sample, all component drafts coexist before the first call. Release each draft only after its finalization input is no longer borrowed. |
| Existing F4 session/semantic lanes | Seed current totals from an existing permitted F4 O(1) sample at phase entry. | Generalization receives immutable `&self`; prove which existing lanes therefore cannot grow during draft generation. Hook any lane that can grow during internal/incoming routing or finalization staging to its existing growth boundary and the same totals. | The all-drafts sample precedes the first finalizer. The successful `DraftMember` sample refreshes after checkpoint-after bytes and `self.drafts` slot growth; scheme install/incoming samples keep existing F4 semantics. |
| `yu-types` finalization session | Existing session lanes are retained and counted at their checked capacities; new maps/colors/frames join the private `Scratch` ledger. | Reconcile each reserve and keep solver-owned inputs immutable during the call. | `Scratch::clear()` retains capacity. A successful-call peak is `max(before, after)` only if every lane is monotone and no local capacity is untracked; otherwise `yu-types` maintains its own same-time call peak. Failure returns no checkpoint and causes no solver post-failure sample. |

This six-group matrix is closed by the following design invariant, independent
of the exact alpha-ranking algorithm: the indexed producer path has no raw
capacity-managed container or nested dynamic payload. Every `Vec`, map, set,
deque, and other capacity-managed lane (including nested fields) is created
through a tracked fallible owner, has its own lane ticket, and can grow only
through the shared capacity-event gateway. There is no untracked `clone`,
`collect`, `to_vec`, or recursive `Box` reconstruction. Hash map/set insertion
must reserve through that gateway before insertion. The ticket carries its
semantic/session class and current observed capacity as the allocation moves.
Partial moves transfer only the affected ticket; whole-owner moves carry the
cached sum; nested lanes always retain separate tickets. Normal drop and
unwind use the same exactly-once release gateway.

For every matrix row, the gateways are: fallible construction/register actual
initial capacity; reserve/observe actual capacity on both `Ok` and `Err`;
ticket transfer for moves; release on clear/drop; and the row's listed
baseline. Current F4 owners that cannot grow during root generalization are
proven fixed there because `component_generalization_draft` receives an
immutable session reference; internal/incoming routing remains on existing
F4 sampling boundaries or connects any growth to the same totals. Key and
ranking work stays separate from ledger update cost: the current exact
algorithm evaluates `k!` label permutations for `k` distinct non-owner
variables, and any replacement must state its own visit/comparison count after
the alpha decision. This closes the accounting interface without claiming
that every future allocation site is implemented or that producer work is
bounded.

Every constructor that can create capacity (`with_capacity`, clone, collect,
`to_vec`, and nested payload construction) must register the observed capacity
before another fallible operation or publication. Production constructors
must be fallible where allocation failure maps to
`SolveAvailabilityError::IdentityExhausted`; infallible clone/collect paths
are not an acceptable substitute. Every reserve wrapper observes capacity
after the call whether it succeeds or fails, updates checked owner/global
totals, and only then appends or propagates the allocation error. A partial
transfer moves the affected lane account and its cached bytes; source-owner
release excludes that lane. Whole-owner release uses cached totals exactly
once. Physical drop work may scale with nested allocations; the ledger update
per lane/owner transition remains O(1).

If observed `capacity * slot_size`, an owner sum, or a global aggregate
overflows, abort this one-shot solve with the existing
`SolveAvailabilityError::IdentityExhausted`. Do not saturate, fabricate a
total, sample from stale state, or continue finalization. The solve consumes
the session, returns no `SolvedModule` or counters, and performs no later
sample or scheme/route publication; no persistent solver poison state or F5b
failure epoch is added. During error cleanup, physically drop the owners
without arithmetic against an unrepresentable total. Representable failed
reserves keep their observed contribution until the owner releases it. During
unwind, preserve the original panic; guards release exactly once if
accounting remains representable, otherwise they skip aggregate math as the
whole solve is unwinding.

During member production, record actual growth while earlier member drafts,
the memo, and partial-root lanes coexist. Record temporary-to-draft transfers
before local owners disappear. On any producer failure or unwind, release
local owners through the same transitions and return without another resource
sample or publication. Account the memo's physical `clear()` releases, then
take the §26-authorized all-drafts-coexist O(1) sample immediately before the
first finalization. Freeze current solver totals minus
`current_closed_retained_bytes` exactly once to obtain semantic/session
baselines. No solver-owned lane may change during the `yu-types` finalization
call. On success, require checkpoint before-bytes to equal the scalar; combine
each frozen baseline with the checkpoint's within-call peak; replace the
scalar with checkpoint after-bytes; push into `self.drafts` and account any
actual slot growth; then take the existing `DraftMember` sample to refresh the
next baseline from current totals. Every transfer/release/growth between these
boundaries updates the ledger immediately, so a later baseline cannot be
stale. Production failure returns without a post-failure sample; none is
needed or newly authorized.

Required proof before treating this as exact includes an independent event
trace with lane identity, owner, classification, requested length, observed
capacity, slot size, growth, transfer, release, and same-time semantic/session
totals. Tests reconcile those events against independent lane enumeration for
memo/walker overlap with earlier drafts, later-draft growth after memo release,
nested-array growth while the outer vector is fixed, compaction transfers,
multiple finalizations with intervening changes, failed reserve, normal and
unwind release, and finish. Every failed reservation must reconcile observed
capacity before returning. No O(number-of-drafts) scan may be added to an event
or sample. New classifications remain pending until the audit maps every
owner to F4's semantic/session sets; new `yu-types` lanes must reconcile
independently and retain monotone capacity during successful calls or track an
internal same-time checkpoint peak.

This representation is intended to replace boxed recursive draft
materialization through generalization and finalization; it must not be
converted back into recursively boxed trees between those stages. The
producer-side ID-preserving path, pruning/normalization remapping, R/Q
assignment, compact graph construction, and proof that every node is reachable
are not specified by this candidate. Current production still emits boxed
trees and normalizes predicate and recursive bounds in separate passes; a
finalizer-only adapter would preserve the stack risk.

Inside the finalization session, `yu-types` owns every source-ID-to-draft
index map, visitation state, explicit postorder frame/worklist, temporary
child-index range, and commit scratch. No `Draft*Id<'tx>` is stored outside
`yu-types` or escapes the call. The proposed private reusable `Scratch` lanes
are `Vec<u32>` visitation colors, `Vec<Option<u32>>` positive and negative
source-to-draft maps, and an explicit frame lane containing polarity, source
index, and next-child position as `u32` values. Helpers reconstruct typed draft
handles only inside the active `yu-types` transaction from validated indices;
there is no lifetime erasure or raw-handle reconstruction in `yu-solver`.
Private indexed Union/Intersection and scheme-setting helpers append mapped
child indices directly to existing draft child lanes in source order. They
use the existing checked reservation, failure injection, poison, validation,
planning, and commit paths, without a local typed-handle vector. New lanes are
cleared but retain capacity under the existing `Scratch::clear` rule.

The entire input is validated within the finalization attempt before creating
any transaction handle. Every positive/negative node ID, child span and child
ID, Q ordinal, R ordinal, and array/count conversion uses checked arithmetic.
`quantifier_count` is representable as a draft-lane count. Q references are
exactly in `[0, quantifier_count)`. The recursive-bound array has exactly the
R binders: entry `i` has ordinal `quantifier_count + i`, checked for overflow,
and every R reference names one listed entry. Function effects are
implicitly the permitted closed pure pair. The full structural child graph
must be acyclic; shared DAG nodes and repeated child edges are valid. Every
node in either node array must be reachable from the predicate or a recursive
lower/upper root; unreachable nodes are rejected as `InvalidDraft`. Recursive
references are binder leaves, not structural child edges, so guarded
recursion through an R reference is valid. Every child-array ID is validated,
including entries not selected by a node span.

Build order is deterministic: visit recursive-bound roots by R ordinal, each
lower before its upper, then the predicate. Within Function, visit argument
before result; within Union/Intersection, visit children in span order. An
iterative gray/black walk rejects a gray structural child as a cycle and reuses
the mapped result for a black shared node. Each reachable source node is built
once. The existing closed normalizer receives Union/Intersection members in
input order and remains authoritative for canonical output; source IDs,
encounter order, and hash iteration do not define normalized order. Create Q
and R binders before bounds, process R bounds by ordinal and each lower before
its upper, then build the predicate and set the scheme once.

Indexed-input validation, reachability marking/compaction, and the `yu-types`
source-ID construction traversal target `O(P + N + C₊ + C₋ + R + Q)` work and
`O(P + N + C₊ + C₋ + R + Q + D)` indexed/finalizer slots, where `P`/`N`
count polarity nodes, `C₊`/`C₋` count child-ID entries, `R` counts recursive
bounds, `Q` is the quantifier count, and `D` is maximum explicit DFS frame
depth. Each node/edge in these passes must be processed a bounded constant
number of times. These bounds exclude root-local R fixed-point/replay work,
structural deduplication, alpha/permutation ranking, normalization, and commit;
their costs need separate bounds and must not be presented as one linear
producer/finalizer claim. The full stack-safe path must still avoid recursive
Rust calls, reconstruction of recursively boxed trees, per-node cloning, and
unbounded occurrence-path duplication. Exact alpha/permutation ranking is a
separate unresolved contract: `unordered_root_keys` currently enumerates
`k!` label permutations for `k` distinct non-owner variables. This does not
change the current F5 §36 finalizer contract: closed canonical normalization
retains its `O(N + W + C)` descriptor-ranking bound, and commit retains its
existing separate cost. The factorial alpha-label search discussed here is in
the solver-side producer, not `yu-types` finalization.

Malformed supplied IDs, spans, Q/R references, cycles, or orphan nodes return
`InvalidDraft`. A producer-side source count or ID/span endpoint that cannot be
represented in the indexed input requires an explicit solver availability
mapping before the input is constructed; it is not a malformed finalizer
input. Exhaustion of a valid `yu-types` draft lane, allocation, or checked byte
total returns `IdentityExhausted`. Each error after a finalization attempt
begins in a valid session follows the existing failure-epoch transition and
publication rollback; terminal accounting exhaustion advances the epoch once
and poisons the session, while later poisoned calls keep their current
short-circuit behavior. A producer failure before the call does not advance
the yu-types-owned failure epoch.

All growing `yu-types` maps, worklists, visitation arrays, child-index
buffers, overlays, and commit scratch are private capacity-accounted lanes.
The explicit new lanes are positive/negative source maps (`Option<u32>`),
visitation colors (`u32`), and DFS frames (polarity tag and two `u32` fields),
in addition to existing draft, plan, and permanent lanes. Extend both
`Scratch::checked_capacity_bytes` and session retained-byte reconciliation for
every new lane. Reconcile every actual capacity growth before the next
fallible operation or append. No lane may be omitted because it is private or
transient. Input arrays remain solver-owned and simultaneously live.

The exact checkpoint peak requires every `yu-types` physical lane to be
accounted at each capacity change. The simplest compatible implementation
keeps each lane allocated and only clears its length during the call, with no
untracked temporary capacity; then capacities are monotone and
`max(retained_bytes_before, retained_bytes_after)` is sufficient. If any lane
can release or transfer capacity during a successful call, its private
checkpoint accounting must instead maintain a same-time call peak across that
transition. The current code does not yet enforce or prove either condition
for the proposed validation/indexed helpers. The solver-side frozen baseline
also requires the §26-authorized coexistence sample and event ledger to cover
every member and temporary owner without scanning. Until these are proved,
the aggregate peak formula below remains a target, not demonstrated exactness:

```text
semantic candidate = frozen semantic baseline excluding closed storage
                   + checkpoint.peak_bytes_during_call
session candidate  = frozen session baseline excluding closed storage
                   + checkpoint.peak_bytes_during_call
```

Each physical lane is counted once; capacities from different owners are
combined only while their lifetimes overlap, and peaks from different times
are not added. Malformed supplied input returns `InvalidDraft`; exhaustion of
a valid draft lane, allocation/capacity, or checked-byte accounting returns
`IdentityExhausted`. A failure from an invocation that begins in a valid
session follows the existing single failure-epoch transition; terminal
accounting exhaustion poisons the session and advances the epoch once, while
later poisoned calls retain the existing short-circuit behavior. An unwind
rolls back logical publication and resumes unwinding under existing
transaction behavior. Failures return no checkpoint or scheme and publish no
component slot, incoming route, or partial `SolvedModule`. A failed
reservation may retain `yu-types` capacity for direct retry; the next
successful checkpoint includes that retained capacity. In production,
`IdentityExhausted` maps to the existing solve-availability error and
`InvalidDraft` remains an internal-invariant failure. Production solve failure
returns before scheme installation or later sampling. Successful candidates
remain invisible until the whole component is finalized and atomically
installed.

This is a new public construction API despite `doc(hidden)`. It changes F5 §24
and needs explicit user approval after independent review. The exact proposed
surface and some input contracts are stated, but safe index-to-handle
construction, full input provenance (including the no-orphans invariant),
retained-capacity peak equality, producer compatibility, and lane accounting
remain unresolved. Independent M2 review and architect adjudication found that
this candidate is not ready for user approval or implementation. No
implementation or compilation proof exists.

## 5. Defer

Keep current F5b/F5 authority unchanged and leave the indexed finalizer and
F5c stack-safety gate open. Do not claim F5c closure or F5e certification.

## 6. Review, evidence, and approval gates

The initial M2 review rejected solver-owned callback result slots as unsafe
under the existing higher-ranked API and found the first indexed API proposal
underspecified. A fresh M2 delta review must establish exact §24/F5b
conformance and challenge every lane, capacity-growth point, failure path,
producer compatibility, and aggregate peak before Candidate B is presented
for user approval.

Required implementation evidence after any approval includes deep alternating
Functions through ordinary generalization and finalization; guarded R and
shared-summary cases; exact node/edge counts; wide Union/Intersection fanout;
shared DAGs; Q/R and lower-before-upper ordering; per-lane requested lengths,
actual capacities, growths and transfer points; bounded clones/reconstruction;
injected validation, reservation, error and unwind paths; failure atomicity;
shallow output parity; and independent per-lane plus semantic/session peak
reconciliation. Depth-only evidence is insufficient.

## 7. M2 review outcome (2026-09-23)

Fresh independent specification and performance reviews found Candidate B not
ready for user approval. The primary accepts these blockers; follow-up
architect review confirmed that the §26 coexistence sample is already
authorized and proposed a private event-time solver ledger. This resolves the
accounting design direction, not its source-level completeness or proof, and
does not reopen approved F5/F5b authority.

- The current producer emits boxed trees, normalizes predicate and R bounds in
  separate passes, assigns R/Q during root-local processing, and hands boxed
  trees to recursive finalization. The indexed producer has no specified
  pruning/remapping/compaction path that preserves Q/R identity and yields a
  reachable, orphan-free graph. A finalizer-only adapter would reconstruct
  boxes and retain the stack risk.
- The five input arrays and every simultaneously live member-draft owner are
  not included in the current F4 sample used as the first finalization
  baseline. F5 §26 explicitly authorizes O(1) samples at actual capacity
  growth and when all drafts coexist. A single end-of-build sample cannot
  recover an earlier peak; summing separate owner peaks combines different
  times; and a `DraftMember` snapshot becomes stale after any growth/release.
  The proposed event-time ledger in §4 updates same-time totals at each lane
  transition, accounts memo `clear()` releases, samples before first
  finalization, and refreshes after each successful checkpoint. A performance
  delta review must still verify every physical owner and event, including
  failed reserves and semantic/session classification. Production failure
  returns without a post-failure sample.
- The first draft had inconsistent public-type/array counts, mixed indexed
  linear-work claims with F5 §34 closed-normalization cost, and did not make
  the complete new-lane growth/reconciliation sequence enforceable. The
  statements above correct the count and separate costs, but do not resolve
  producer or accounting blockers.
- Malformed supplied indices map to `InvalidDraft`; producer-side source-range
  overflow must be classified before constructing the input; valid finalizer
  lane/allocation/accounting exhaustion maps to `IdentityExhausted`. Only
  errors after a finalization attempt begins advance the yu-types failure epoch.

A follow-up architect sketched the producer as four phases, still unproved:
(1) carry polarity-typed IDs from `walk`, importing completed root-neutral
summary DAGs through separate ID maps while preserving exact-bound/direct-row,
Function, and first-seen traversal order; (2) run guarded R analysis,
incidence, replay, eligibility, and fixed-point classification over root-local
IDs; (3) preserve current alpha/permutation ranking and separate predicate/R
normalization, then assign Q by the same first-occurrence paths and rewrite
live-row leaves; (4) mark from predicate plus retained R lower/upper roots,
compact in deterministic postorder, remap every polarity edge and child span,
and rebuild child arrays without orphan entries. The current boxed walk,
summary materialization, replay, key forest, and finalizer have not been
replaced or parity-proved.

The unresolved invariant is exact equivalence between existing unfolded
alpha-normal tree keys / owner-context R ranking / Q first-occurrence paths and
one shared indexed graph. A shared node can occur under multiple paths and
owner contexts; one graph key or visitation may not preserve tree semantics.
The candidate must not claim linear producer work until fixed-point replay,
structural dedup, and alpha-key costs are separately bounded. No code or tests
changed in this follow-up.

The stack-safety gate remains open during a bounded architecture repair of the
end-to-end producer and capacity ledger. Candidate B remains Draft; this work
does not approve its new public API. Any implementation still requires a clean
M2 review and explicit user approval. The all-drafts-coexist sample boundary
is already authorized by §26; a new authority decision is needed only if exact
accounting cannot be established with these growth events and coexistence
samples and requires post-failure sampling or another unlisted boundary. The
event ledger, owner classifications, `yu-types` call-peak lifecycle, and
end-to-end producer parity still need independent proof. No implementation,
tests, measurements, or authority changes were made in this review round.
Exact alpha/order and failed-route sampling remain separate pending decisions;
§44's first-member projection, current F4 counters, and F5e resource deferrals
remain unchanged. Even an approved addendum and indexed-finalizer slice do not
by themselves close the remaining F5c rescan/rollback gates or certify F5e.

### M2 event-ledger review and architect adjudication (2026-09-23)

A second independent M2 review found that the event-time mechanism was
plausible but its accounting classes, owner/event coverage, and post-reserve
overflow state were still underspecified. The all-drafts baseline and
checkpoint equation do conform to F5 §26 and F5b §§5–7 when every solver lane
is stable during the finalizer call. The review distinguishes those design
gaps from source-level implementation evidence, which belongs after approval.

A follow-up architect adjudication established the proposed classification
rationale from existing authority: F5 §26's `generalization_scratch` family,
F5 §§14/26/34's draft and physical-lane requirements, and F4 §13's semantic
subset place root generalization scratch, member drafts, and their five input
arrays in both semantic and session totals. F4 §13 includes the live F0/F2 plan
in total session bytes and defines semantic storage as a subset; local
`components`, `internal_uses`, `members`, and `incoming_uses` copies are
therefore proposed as session-only scheduling storage, provided the constructor
audit finds no semantic payload in those owners. These are applications of
approved ownership, not a new sample-boundary choice; any mismatched owner
must follow its actual payload owner.

The adjudicated transition contract now requires registration of observed
initial capacity for every constructor, including fallible clone/fill instead
of untracked `collect`/`to_vec`; post-reserve capacity reconciliation on both
success and error before append/propagation; lane-account transfer on partial
moves; exactly-once cached-account release on normal drop/unwind; and a
terminal unpublishable `IdentityExhausted` state if observed bytes or aggregate
totals overflow. It must never saturate totals or sample/checkpoint from stale
state. The authorized all-drafts sample precedes first finalization;
successful checkpoint-after bytes and `self.drafts` growth feed the existing
`DraftMember` refresh. No solver post-failure sample is authorized or needed.

Before Candidate B approval, the proposal needs a complete
constructor-level owner/event matrix: constructor group, physical lane and
parent owner, semantic/session class, initial-capacity path, growth paths,
transfer/release point, success/error/unwind disposition, and the baseline
that includes it. Instrumented line-by-line hooks, independent event traces,
and reconciliation tests remain after-approval implementation evidence. The
matrix in §4 is a first specification of that requirement, not a claim that
every future producer allocation is already enumerated. A fresh M2 delta review
must confirm whether it is sufficient.

A separate architect follow-up found that occurrence-context IDs could
preserve tree-sensitive behavior in principle, but this does not establish an
acceptable work bound. The current `unordered_root_keys` enumerates `k!`
label permutations for `k` distinct non-owner variables; an O(d)-node shared
Function DAG can have `2^d` occurrence paths if duplicated per path. Those are
counterexamples to the proposed method/bound, not proof that no exact bounded
algorithm exists. The exact-alpha decision remains with the user: preserve
unrestricted exact alpha behavior and approve an explicit revised worst-case
complexity contract; retain a bounded contract by restricting/proving the
production forest class; or explicitly weaken alpha/order independence. No
change to F5 §25/§34 or §44 is proposed here.

Candidate B remains Draft and unapproved. No code, tests, benchmarks, or
commits changed in this review/adjudication round.

### Closed-world accounting delta (2026-09-23)

A third M2 delta review still found the six owner groups too abstract while
the document permitted arbitrary new allocation sites. The remaining design
gap was narrowed to the completeness of the owner interface, not to the
all-drafts sample or the same-time peak equation. It also asked whether
post-reserve solver accounting overflow required a persistent state beyond
the existing availability error.

The primary source/authority adjudication confirms the class split: root
generalization scratch is the F5 §26 `generalization_scratch` family and F4
§13 semantic subset; member drafts and the five arrays carry that same semantic
ownership; local scheduling copies hold only SCC/definition/use IDs copied
from F2, so they contribute to session-only storage. The current ID types
contain ordinals/occurrence identity and an `Arc` artifact token, not scheme or
generalization payload. If an owner later carries semantic payload, that lane
inherits the semantic class. F5b's terminal poison/epoch rule applies to its
reusable `yu-types` session, not to the one-shot solver.

For the solver ledger, `InferenceSession::run` consumes the session and
propagates `execute_scc_plan` failure. Therefore checked byte/aggregate
overflow aborts the one-shot solve through existing
`SolveAvailabilityError::IdentityExhausted`, emits no counters/result, and
has no later sample or publication; it needs no persistent solver poison state
or F5b failure epoch. During unwind, preserve the original panic and do not
sample stale totals.

The current §4 revision now closes the six lifecycle groups with a
closed-world rule: every dynamic lane, including nested payloads, uses a
tracked fallible owner/ticket; no raw allocation, deep clone, `collect`,
`to_vec`, map/set insertion without tracked reserve, or recursive Box
reconstruction is allowed in the indexed producer. Each ticket carries class
and observed capacity through partial/whole moves; all initial-capacity,
reserve-Ok/Err, clear/drop, and unwind transitions use common gateways. The
matrix specifies parent groups, classes, gateways, failure behavior, and
baseline inclusion. This design rule is independent of the exact alpha
algorithm, though the chosen algorithm must use it and separately state its
work/resource bounds.

Fresh independent M2 specification and performance delta reviews found no
preapproval blocker within this accounting design slice. The closed-world
owner/ticket rule, six lifecycle groups, class rationale, one-shot overflow
mapping, and §26/F5b baseline sequence are sufficient as a design contract.
Exact constructor hooks, physical-lane enumeration, reserve-`Err`/unwind
reconciliation, and the `yu-types` checkpoint peak remain postapproval source
and test proof, not closed implementation evidence. These reviews do not
approve Candidate B's new §24 API or resolve producer/alpha parity.

An architect follow-up found two concrete worst-case mismatches relevant to
the producer/alpha decision: the current `F5cKeyForest::unordered_root_keys`
evaluates `k!` permutations for `k` distinct non-owner variables, and
path-expanding an O(d)-node shared Function DAG can produce `2^d` visits. These
counterexamples invalidate the current method/bound; they do not establish
that every exact bounded algorithm is impossible. The user must choose whether
to preserve unrestricted exact alpha with a revised worst-case contract,
preserve a bounded contract by restricting/proving the production forest, or
weaken alpha/order independence. The separate failed-route physical-accounting
choice also remains open: narrow conditional post-rollback O(1) sample,
journal/reconcile under the existing sample whitelist, or defer that resource
gate.

Candidate B remains Draft; do not seek API approval or implement it until the
producer/alpha decision is resolved and the complete candidate receives a
clean M2 review. The §26 all-drafts-coexist sample boundary is authorized; no
additional post-failure boundary is proposed by this Draft. No code, tests,
benchmarks, commits, or pushes changed in this design-review continuation.

## 8. Property-oriented boundary comparison (2026-09-24)

Status: proposal-only clarification; primary-authored; not independently
reviewed; no implementation or §24 API change is approved by this section.

This section compares what the three finalization boundaries preserve and what
they cannot guarantee. It does not supersede the prior M2 findings or present
Candidate B as ready for approval. The authoritative 2026-09-24 producer-order
and normalization addenda remain in force: Q/R encounter order, height-major
normalization, and §44's first-canonical-member public Union representative
are not reopened here. Pending alpha/order and failed-route statements in the
older dated review sections are historical and do not override those later
decisions.

For this gate, “stack-safe” means more than using loops while visiting nodes.
The complete success and failure paths must also release every owned deep
draft without recursive destruction. A nested boxed tree still recursively
drops its children even when the algorithm that built or inspected it used an
explicit worklist. Partial task/value trees on checked error exits count too.

| Boundary | Preserves | Costs or changes | Cannot guarantee |
|---|---|---|---|
| **A. Current recursive callback** | Exact §24 API, transaction-scoped handles, and overlay rollback on callback error. | Recursive finalizer traversal; boxed drafts remain owned through finalization. | Stack-safe traversal or success/error destruction. Callback-local temporary-vector accounting also remains unresolved below. |
| **B. Worklists inside the callback** | Existing method signature; handles stay within the HRTB lifetime; overlay rollback; traversal order can be made explicit. | Solver-owned heap worklists overlap finalizer storage; the current checkpoint has no exact joint-peak value, and F5b freezes those solver lanes. | Stack-safe destruction of the still-boxed input, or exact co-resident accounting under the current boundary. |
| **C. `yu-types` indexed transaction + flat solver drafts** | Transaction ownership of handles, validation, and publication; atomic commit/rollback can remain. With producer parity, it can preserve scheme semantics, Q/R order, canonical normalization, and §44 projection. | Adds a public `#[doc(hidden)]` construction API, changes §24, and requires tracked flat arrays/maps/worklists. Indexed-pass bounds do not bound replay, R fixed-point, normalization, or the whole producer. | Safe destruction if used only as an adapter over boxed drafts; no stack-safety claim until the producer and error cleanup are flat end-to-end. |

One additional source/authority mismatch is visible in the present
`finalize_generalization_draft_raw`: its callback-local `Vec`s coexist with
`yu-types` finalizer storage, while the F5b checkpoint measures only the
latter. The reviewed authority contains no explicit exclusion for those
capacities. This section records that as an accounting question to adjudicate,
not as a claim that the current counter is wrong or permission to alter F5b.
Any selected design must either place such storage under an already authorized
accounting owner or obtain a reviewed, explicit boundary decision.

The least scope-changing choice is to keep §24 unchanged and leave deep
finalization/destruction open; this preserves the approved API but does not
close stack safety. The only currently specified route that could combine
iterative transaction construction with flat, non-recursively-dropped drafts
is Candidate C or an equivalent `yu-types`-owned boundary. Pursuing it is a
design-only step: first reconcile callback-local accounting, then complete
producer parity/reachability and flat cleanup, obtain independent M2 review,
and only then ask for explicit §24 approval. This section itself grants none
of those approvals. It also does not shrink or refactor `lib.rs`; any later
implementation should place the indexed producer/finalizer bridge behind a
dedicated module boundary rather than growing the already large entrypoint.

## 9. Delegated product priority and bounded-path recommendation (2026-09-24)

Status: proposal; the user delegated technical path selection under the product
priorities now recorded in `rules/design-authority.md`; this section is not an
approval of a concrete limit or implementation.

The user prioritizes Oracle-compatible behavior for practical inputs and a
lightweight implementation/success path. Deterministic rejection of
pathologically deep, large, or resource-intensive inputs is acceptable when
the boundary is explicit and preserves memory safety, accepted-input solver
invariants, and atomic publication. This permits a bounded supported-input
envelope; it does not authorize silently changing results within that envelope.

The primary's provisional direction is a bounded version of Boundary A: keep
the current §24 callback and boxed representation, and reject drafts that
exceed a conservative structural-depth limit before any over-limit box is
created. Add a constructed-node/work budget only where the source audit shows
that it is needed to prevent materialization or product expansion from
creating disproportionate work/storage. This is preferred over a new public
indexed API and end-to-end graph rewrite because it can preserve the existing
transaction owner and ordinary-input semantics with less machinery. Boundary
B is not selected: an iterative callback worklist does not itself solve boxed
draft destruction or joint peak accounting. Candidate C remains the fallback
if the bounded path cannot cover every producer and error exit without
disproportionate machinery.

A primary-requested Sol architect review recommended this same bounded path,
subject to an exact source audit. It identified the critical placement rule:
the limit must be checked before the first over-limit owned tree is built,
then maintained through replay, binder substitution, materialization,
normalization, and finalization. A late pre-finalizer rejection is unsafe
because dropping the rejected draft can itself recurse. The review also
flagged callback-local Q/R handle arrays, recursive-bound storage, and product
child vectors whose capacities overlap `yu-types` finalizer storage; F5b's
current checkpoint has no joint-peak field and the source needs accounting
reconciliation. A bounded stack-only representation may resolve this, but that
is an unverified possibility, not a design fact. No threshold or mechanism is
yet chosen, and no code, test expectation, §24 API, or F5b authority changes in
this section.

The next gate is a producer/error-exit audit that determines whether depth and
work bounds can be enforced before allocation at every owning transition,
without adding an unbounded scan or changing successful behavior below the
limit. It must identify how an over-limit input is reported and verify that
partial walker values, earlier component drafts, and finalizer overlays leave
no publication behind. Only after a concrete boundary is drafted and
independently reviewed should implementation begin; if an existing
Authoritative F5 contract changes, the approval and supersession gate in
`rules/design-authority.md` still applies.
