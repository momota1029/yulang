# F5b closed finalization and Term-owner lifecycle amendment

Status: Authoritative; implementation in progress
Scope: F5b inter-crate closed-type construction and ConstraintStore/TermArena
ownership only
Approved-by: user-selected sealed finalization, batch-bound store, logical
clone-owner boundary, and fixed 256-slot Term pages on 2026-09-22
Decision input: user selected sealed `yu-types` finalization and batch-bound
ConstraintStore construction on 2026-09-22
Supersedes: F5 §§24, 32, and 36 only where they require `yu-types`-private
construction from `yu-solver` or permit standalone `ConstraintStore`
construction

## 1. Purpose

Rust has no friend-crate visibility. Raw closed-arena mutation must remain
inside `yu-types`, but `yu-solver` must finalize F4 Bottom/Int schemes and later
F5c schemes. Separately, collected Terms must retain their exact arena through
the public fact store, so a store cannot be constructed from HIR alone.

This amendment changes neither Function algebra, levels, extrusion,
generalization, source collection, diagnostics, normalization, nor later F5
boundaries. F5a Lambdas continue to emit zero source Function facts until F5d.

## 2. Closed-type construction boundary

`yu-types` exclusively owns raw arena storage, handle construction and
validation, node insertion, scheme closure validation, rollback, and borrowed
observation. `yu-solver` owns inference drafts, finalization request order,
dense definition slots, availability mapping, and atomic component publication.

The public observation surface remains the F5 §32 handles/views plus:

```rust
impl QuantifierId { pub const fn ordinal(self) -> u32; }
impl RecursiveBinderId { pub const fn ordinal(self) -> u32; }
impl ClosedRecursiveBound {
    pub const fn binder(self) -> RecursiveBinderId;
    pub const fn bounds(self) -> NeutralValueId;
}
impl ClosedTypeArena {
    pub fn scheme_view<'a>(
        &'a self,
        scheme: &'a ClosedValueScheme,
    ) -> Result<ClosedValueSchemeView<'a>, ClosedTypeLookupError>;
}
```

`scheme_view` validates both arena brand and root handle. `ClosedValueScheme`
and handles remain opaque; raw constructors and arena vectors remain private.

`yu-types` exposes this high-level, transaction-scoped gateway. It is public
because Rust cannot make it selectively visible to `yu-solver`; capability
types are opaque, unconstructible, and `#[doc(hidden)]`.

```rust
pub enum ClosedTypeFinalizeError { IdentityExhausted, InvalidDraft }

#[doc(hidden)] pub struct ClosedTypeFinalizer<'arena> { /* private */ }
#[doc(hidden)] pub struct PendingClosedValueScheme { /* private */ }

impl ClosedTypeArena {
    #[doc(hidden)]
    pub fn new_for_finalization() -> Result<Self, ClosedTypeFinalizeError>;

    #[doc(hidden)]
    pub fn finalize_scheme(
        &mut self,
        build: impl FnOnce(
            &mut ClosedTypeFinalizer<'_>,
        ) -> Result<PendingClosedValueScheme, ClosedTypeFinalizeError>,
    ) -> Result<ClosedValueScheme, ClosedTypeFinalizeError>;
}
```

The finalizer has no public constructor and cannot escape the call. Pending
schemes have neither constructor nor observer and carry a private transaction
identity. A pending result from another invocation is `InvalidDraft`.

The gateway exposes exactly the structural constructors below; each validates
all handle arguments against the current arena and returns checked failure.

```text
quantifier(ordinal), recursive_binder(ordinal)
positive_bottom, positive_int, positive_quantified, positive_recursive,
positive_function(argument, argument_effect, result_effect, result),
positive_union(children)
negative_top, negative_bottom, negative_int, negative_quantified,
negative_recursive,
negative_function(argument, argument_effect, result_effect, result),
negative_intersection(children)
positive_effect_bottom, negative_effect_empty
neutral_bounds(lower, upper), recursive_bound(binder, bounds)
scheme(quantifier_count, recursive_bounds, predicate)
```

`scheme` validates Q ordinal bounds, unique and listed R binders, Q/R
disjointness, closed references, and same-arena ownership. `InvalidDraft` is an
availability failure, never a source type error. `finalize_scheme` snapshots all
arena and index lanes before invoking its closure; closure error, invalid
pending result, validation error, allocation failure, and unwind restore that
exact snapshot. Success commits one closed scheme atomically.

`SolveAvailabilityError` gains `ClosedTypeFinalizationFailed`. Map
`IdentityExhausted` to the existing availability exhaustion and `InvalidDraft`
to the new error. Neither publishes a partial slot or `SolvedModule`.

## 3. TermArena lifecycle

Each `ConstraintBatch` creates one private `TermArena`. Leaf/Component interning
is crate-private. Before consuming the batch it is the only public Term lookup
owner:

```rust
impl ConstraintBatch {
    pub fn term_view(&self, term: Term) -> Result<TermView<'_>, TermLookupError>;
    pub fn term_kind(&self, term: Term) -> Result<ComponentKind, TermLookupError>;
}
```

Remove `ConstraintStore::new(Arc<HirModule>)`. Replace standalone store creation
with exact batch consumption:

```rust
impl ConstraintStore {
    pub fn from_batch(batch: ConstraintBatch) -> Self;
    pub fn term_view(&self, term: Term) -> Result<TermView<'_>, TermLookupError>;
    pub fn term_kind(&self, term: Term) -> Result<ComponentKind, TermLookupError>;
}
```

`from_batch` moves the exact HIR and Term arena without rebranding or remapping,
drops planning state, and initializes fact/canonical/provenance/receipt lanes
with zero requested capacity. `SolvedModule::solve` privately performs the same
arena transfer while retaining frozen SCC/recipe state. It never reconstructs
Terms from HIR. After either consuming path, the store is the sole public lookup
owner.

Callers clone required occurrences before consuming a batch:

```rust
let occurrence = batch.occurrences()[0].clone();
let mut store = ConstraintStore::from_batch(batch);
let receipt = store.transaction().admit(&occurrence)?;
```

`ConstraintBatch::Clone` retains its existing immutable-artifact contract. A
clone has the same collection token, SCC plan, query counters, Term arena brand,
and collected prefix handles. Each consumed clone owns an independent
solve-time arena snapshot. A matching-brand index absent from a sibling snapshot
is `InvalidHandle`; another collection is `ArenaMismatch`. Receipt brands remain
store-specific. If same-index solve-time allocation could diverge between
identical clones, return to design.

`ConstraintTransaction::admit` validates both handles through the store first.
Wrong artifact remains `ArtifactMismatch`; a matching-brand absent index is an
internal invariant failure with no receipt, fact, provenance, bounds mutation,
or counter admission; cross-kind stays local.

## 4. F4 compatibility

Remove `ClosedPositiveValue`, public `ClosedValueScheme::new`, and `.body()`.
`InferenceSession` owns one `ClosedTypeArena`; F4 creates Bottom/Int schemes
through `finalize_scheme`, stores non-Copy opaque schemes in dense slots, and
observes them via `scheme_view`. Incoming routing and `root_value_for` preserve
Bottom → Never, Int → Int, and future structured → Unknown behavior. This does
not change F4 facts, causes, SCC or route order, provenance, or projection.

Standalone store tests migrate from `ConstraintStore::new(hir)` to cloned
occurrences plus `ConstraintStore::from_batch(batch)`. Foreign tests collect a
separate batch. No test constructs a Term directly.

## 5. Required evidence and non-decisions

`yu-types` proves opaque traits/constructors, lookup foreign/invalid cases,
transaction rollback, pending cross-transaction rejection, Q/R closure,
Function field order, and alpha-equivalence. `yu-solver` proves pre-consume
batch lookup, exact post-transfer lookup, clone behavior, foreign/invalid
lookup/admission, distinct receipts, F4 schemes/routes/projection, injected
finalization failure atomicity, and F5a's zero Function fact.

This amendment does not authorize live Function rows, levels, extrusion,
diagnostic completion, Q/R generalization, instantiation, source Function
collection, closed normalization, or F5e certification. Return to design if
implementation needs public raw arena mutation, a second closed storage owner,
Term rebranding/reconstruction, retained standalone store construction, or a
source Function fact before F5d.

## 6. Review-repaired finalizer and clone contract

This section replaces conflicting or less-specific wording in §§2–5. It closes
the first M3 review findings without changing the user-selected boundaries.

### 6.1 Generative draft overlay

No permanent public arena handle may be created during a transaction callback.
Otherwise copied `*ValueId` handles could survive rollback and alias a later
reused permanent index. The callback uses only generative draft handles:

```rust
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[doc(hidden)] pub struct DraftQuantifierId<'tx> { /* private */ }
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[doc(hidden)] pub struct DraftRecursiveBinderId<'tx> { /* private */ }
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[doc(hidden)] pub struct DraftPositiveValueId<'tx> { /* private */ }
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[doc(hidden)] pub struct DraftNegativeValueId<'tx> { /* private */ }
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[doc(hidden)] pub struct DraftPositiveEffectId<'tx> { /* private */ }
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[doc(hidden)] pub struct DraftNegativeEffectId<'tx> { /* private */ }
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[doc(hidden)] pub struct DraftNeutralValueId<'tx> { /* private */ }
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[doc(hidden)] pub struct DraftRecursiveBound<'tx> { /* private */ }
#[doc(hidden)] pub struct ClosedTypeFinalizer<'tx> { /* private, !Send, !Sync */ }
```

Draft handles have private invariant `'tx` markers, no constructors, accessors,
ordering, serialization, or conversion to permanent handles. The finalizer is
neither `Clone` nor `Copy`. Its only public creation site is the higher-ranked
callback below; draft handles cannot escape safe Rust.

```rust
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClosedTypeFinalizeError { IdentityExhausted, InvalidDraft }

impl ClosedTypeArena {
    #[doc(hidden)]
    pub fn try_new_for_finalization() -> Result<Self, ClosedTypeFinalizeError>;

    #[doc(hidden)]
    pub fn finalize_scheme<F>(
        &mut self,
        build: F,
    ) -> Result<ClosedValueScheme, ClosedTypeFinalizeError>
    where
        F: for<'tx> FnOnce(
            &mut ClosedTypeFinalizer<'tx>,
        ) -> Result<(), ClosedTypeFinalizeError>;
}
```

The callback returns only `()`. Exactly one `set_scheme` call records the
private candidate. Zero/multiple calls, absent draft references, foreign draft
references, or failed Q/R closure return `InvalidDraft`.

```rust
impl<'tx> ClosedTypeFinalizer<'tx> {
    pub fn quantifier(&mut self, ordinal: u32) -> DraftQuantifierId<'tx>;
    pub fn recursive_binder(&mut self, ordinal: u32) -> DraftRecursiveBinderId<'tx>;

    pub fn positive_bottom(&mut self) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn positive_int(&mut self) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn positive_quantified(&mut self, binder: DraftQuantifierId<'tx>) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn positive_recursive(&mut self, binder: DraftRecursiveBinderId<'tx>) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn positive_function(&mut self, argument: DraftNegativeValueId<'tx>, argument_effect: DraftNegativeEffectId<'tx>, result_effect: DraftPositiveEffectId<'tx>, result: DraftPositiveValueId<'tx>) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn positive_union(&mut self, children: &[DraftPositiveValueId<'tx>]) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError>;

    pub fn negative_top(&mut self) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn negative_bottom(&mut self) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn negative_int(&mut self) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn negative_quantified(&mut self, binder: DraftQuantifierId<'tx>) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn negative_recursive(&mut self, binder: DraftRecursiveBinderId<'tx>) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn negative_function(&mut self, argument: DraftPositiveValueId<'tx>, argument_effect: DraftPositiveEffectId<'tx>, result_effect: DraftNegativeEffectId<'tx>, result: DraftNegativeValueId<'tx>) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn negative_intersection(&mut self, children: &[DraftNegativeValueId<'tx>]) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError>;

    pub fn positive_effect_bottom(&mut self) -> Result<DraftPositiveEffectId<'tx>, ClosedTypeFinalizeError>;
    pub fn negative_effect_empty(&mut self) -> Result<DraftNegativeEffectId<'tx>, ClosedTypeFinalizeError>;
    pub fn neutral_bounds(&mut self, lower: DraftPositiveValueId<'tx>, upper: DraftNegativeValueId<'tx>) -> Result<DraftNeutralValueId<'tx>, ClosedTypeFinalizeError>;
    pub fn recursive_bound(&mut self, binder: DraftRecursiveBinderId<'tx>, bounds: DraftNeutralValueId<'tx>) -> Result<DraftRecursiveBound<'tx>, ClosedTypeFinalizeError>;
    pub fn set_scheme(&mut self, quantifier_count: u32, recursive_bounds: &[DraftRecursiveBound<'tx>], predicate: DraftPositiveValueId<'tx>) -> Result<(), ClosedTypeFinalizeError>;
}
```

All draft constructors accept references produced earlier in the same overlay;
all slices are borrowed for the call only. After callback success, `yu-types`
validates the overlay, computes the permanent-index mapping, fallibly reserves
all affected permanent arena/index lanes in a fixed order, then commits under a
logical rollback guard. Only then are permanent Copy handles and one
`ClosedValueScheme` constructed.

Callback/validation failure drops the overlay: permanent nodes, indexes,
schemes, and logical allocation/admission counters remain unchanged. Checked
index arithmetic or `try_reserve` failure returns `IdentityExhausted`. A failed
reservation may retain physical capacity already acquired in earlier lanes;
that capacity and peak growth remains recorded, but no logical state becomes
observable. Unwind during callback drops the overlay. Unwind during commit
truncates appended logical lanes and removes new index entries, then resumes;
capacity may remain and logical counters are applied only after commit. Process
or allocator abort has no rollback guarantee and returns no compiler result.

`InvalidDraft` is a direct `yu-types` gateway error. In `yu-solver`, an
`InvalidDraft` after prior draft validation is an invariant failure: it returns
no module and is not mapped to a new `SolveAvailabilityError`. Only
`IdentityExhausted` maps to the retained existing availability variant. This
preserves F4's exhaustive four-variant availability API.

### 6.2 Logical Term lineage ownership

The user approved the narrow replacement for F5 §36's literal one-Rust-object
owner rule. Ownership is one logical TermArena lineage:

- Pre-consumption `ConstraintBatch` clones are read-only aliases of one
  collection lineage, with the same immutable collected prefix and Term brand.
  A collected handle is valid through every alias.
- Consuming an alias gives its `ConstraintStore` sole mutable/full ownership of
  that branch. Surviving batch aliases remain read-only owners of the shared
  prefix.
- Each consumed branch receives disjoint post-prefix indexes from a shared
  checked lineage allocator. Storage is segmented/sparse; it must not allocate
  densely up to another branch's high-water mark.
- Another collection lineage returns `TermLookupError::ArenaMismatch`. A
  same-lineage handle absent from the queried branch returns
  `TermLookupError::InvalidHandle`.
- Receipt brands remain store-specific. If identical clones could allocate a
  different semantic Term at one post-prefix index, implementation returns to
  design; reuse is forbidden.

This narrowly supersedes F5 §36's stale-owner wording and permits the retained
F2 `ConstraintBatch::Clone` contract without handle remapping or a fallible
clone API. `ConstraintStore::new` remains removed; `from_batch` remains the
infallible exact-transfer API in §3.

### 6.3 Required repair evidence

Compile probes prove exact finalizer traits, inaccessible constructors,
non-escaping generative draft IDs, and inability to mix transaction drafts.
Unit tests inject callback error, validation error, reservation failure, and
caught commit unwind; they prove no permanent-handle revival, committed-handle
survival, logical rollback, and retained capacity/peak accounting. They also
prove the F4 availability enum remains exhaustive and unchanged.

Term tests prove collected handles through batch aliases, transfer preservation,
surviving-alias prefix lookup, distinct post-prefix branch indexes,
same-lineage `InvalidHandle`, distinct-lineage `ArenaMismatch`, receipt
separation, branch allocator exhaustion, and unchanged F2 clone counters.

## 7. Fixed Term pages and reusable finalization staging

This section supersedes §6 where post-prefix Term storage and finalizer staging
were unspecified. The user approved `TERM_PAGE_SLOTS = 256` on 2026-09-22.

### 7.1 Term page identity and storage

`Term` remains an opaque Copy pair of arena lineage brand and `u32` index. For
one lineage, `0..collected_len` is the immutable prefix; post-prefix identity
starts at `align_up(collected_len, 256)`. The alignment gap is below 256 and is
never valid.

```rust
const TERM_PAGE_SLOTS: u32 = 256;

struct TermLineage {
    brand: TermArenaBrand,
    collected: Arc<[TermNode]>,
    first_postfix_page: u32,
    next_postfix_page: AtomicU32,
}

struct BranchTermArena {
    lineage: Arc<TermLineage>,
    pages: Vec<TermPage>,
    page_positions: HashMap<u32, usize>,
}

struct TermPage { base: u32, nodes: Vec<TermNode> }
```

Every page base is 256-aligned; node capacity is exactly 256 on creation and
length never exceeds 256. A lookup masks `base`/`offset`, performs one
`page_positions` probe, and bounds-checks the offset. Missing page/offset is
`InvalidHandle`; another lineage is `ArenaMismatch` before the probe. No lookup
scans pages or allocates to a sibling's high-water index.

A branch fallibly reserves descriptor/directory slots, allocates its exact
256-slot buffer, then checked-CAS claims an aligned page and publishes with the
reserved storage. Failure before claim changes no identity state. A claimed
page is never reused; unwind after claim may burn it. Page overflow maps to the
existing `IdentityExhausted`. CAS retries are non-semantic observations.

```text
pages(N)    = ceil(N / 256)
reserved(N) = 256 * pages(N)
slack(N)    = reserved(N) - N
0 <= slack(N) < 256
total_reserved <= sum(N_b) + 255 * branch_count
```

Add one alignment gap below 256 to the total. Page index allocation cannot
control source/SCC/function/scheme/diagnostic order. F5b has no new public
page counters; test-only observations record claims, reserved slots, committed
nodes, directory probes, alignment gap, slack, and non-deterministic CAS
attempts. F5e integrates prefix, page descriptors, directory, and page buffers
under `inference_type_arena`; fixed `Arc`/atomic/header fields are not capacity
lanes.

### 7.2 Reusable closed-finalization session

`ClosedTypeFinalizationSession` replaces direct finalization mutation on the
observational `ClosedTypeArena`:

```rust
#[doc(hidden)] pub struct ClosedTypeFinalizationSession { /* private */ }
impl ClosedTypeFinalizationSession {
    #[doc(hidden)]
    pub fn try_new() -> Result<Self, ClosedTypeFinalizeError>;
    #[doc(hidden)]
    pub fn finalize_scheme<F>(&mut self, build: F)
        -> Result<ClosedValueScheme, ClosedTypeFinalizeError>
    where F: for<'tx> FnOnce(&mut ClosedTypeFinalizer<'tx>)
        -> Result<(), ClosedTypeFinalizeError>;
    #[doc(hidden)]
    pub fn scheme_view<'a>(&'a self, scheme: &'a ClosedValueScheme)
        -> Result<ClosedValueSchemeView<'a>, ClosedTypeLookupError>;
    #[doc(hidden)]
    pub fn finish(self) -> Result<ClosedTypeArena, ClosedTypeFinalizeError>;
}
```

The session owns arena construction, indexes, reusable scratch, and staging
accounting. `finish` requires no active transaction, drops scratch, and moves
the observational arena without cloning/rebranding nodes.

Scratch has separate lanes for every draft node family, recursive bounds,
scheme header, draft-to-final maps, and rollback entries. A transaction clears
all lengths before callback and after success/ordinary error but retains
capacity. Thus D equal Bottom/Int drafts grow scratch only through their first
maximum. Scratch is transient `closed_type_arena` staging, never
`generalization_scratch`.

The fixed order is: clear scratch; callback; validate; plan; reserve permanent
lanes; commit positive value, negative value, positive effect, negative effect,
neutral value, recursive bound, scheme header; construct scheme; commit logical
counters; clear scratch. Draft ordinal orders every family; hash-consing never
reorders it. Permanent handles appear only after scheme construction.

### 7.3 Deterministic failure evidence

Under `cfg(test)`, failure injection is event based:

```rust
enum FinalizationFailureEvent {
    OverlayWrite { lane: FinalizationLane, ordinal: usize },
    ArenaReserve { lane: FinalizationLane, ordinal: usize },
    CommitWrite { lane: FinalizationLane, ordinal: usize },
}
```

Events fail before their writes. Ordinals are zero-based per transaction and
lane/commit order is fixed above. Reserve injection maps to
`IdentityExhausted`; overlay/commit injection is test-only `InvalidDraft`.
Attempts, successes, rollback, scratch peak, and actual capacity changes are
test-only. Public logical node counters count only committed work.

F5b tests are bounded: 255/256/257 prefix and 1/256/257/513 post-prefix cases,
exact page formulas, interleaved two-branch claims, sibling/different-lineage
lookup, branch high-water isolation, 64 Bottom schemes with only first-maximum
scratch growth, a larger draft, every failure event, retained capacity after a
later reservation failure, commit rollback, and successful retry equivalence.
The isolated 1k/2k/4k resource matrix and multi-process certification remain
F5e work.

Return to design if implementation needs a shared mutable global Term directory,
a lock or lineage scan on ordinary lookup, dense high-water allocation, a reused
claimed page, page identity in semantics, fresh overlay vectors per definition,
permanent pre-commit handles, public F5b counters, or F5e certification in F5b.

## 8. Exact session and fixed-page repair

This section supersedes the older `ClosedTypeArena::{try_new_for_finalization,
finalize_scheme}` declarations in §§2 and 6, the F4-compatibility wording in
§4, and any `Vec<TermNode>` page backing in §7. `InferenceSession` owns exactly
one `ClosedTypeFinalizationSession` for its complete solve. Only
`session.finish()` yields the observational `ClosedTypeArena`; neither an arena
nor a new per-scheme session finalizes schemes directly.

```rust
#[doc(hidden)]
pub struct ClosedTypeFinalizationSession {
    /* private; !Clone, !Copy, !Debug, !Send, !Sync */
}

impl ClosedTypeFinalizationSession {
    #[doc(hidden)]
    pub fn try_new() -> Result<Self, ClosedTypeFinalizeError>;

    #[doc(hidden)]
    pub fn finalize_scheme<F>(&mut self, build: F)
        -> Result<ClosedValueScheme, ClosedTypeFinalizeError>
    where
        F: for<'tx> FnOnce(&mut ClosedTypeFinalizer<'tx>)
            -> Result<(), ClosedTypeFinalizeError>;

    #[doc(hidden)]
    pub fn scheme_view<'a>(&'a self, scheme: &'a ClosedValueScheme)
        -> Result<ClosedValueSchemeView<'a>, ClosedTypeLookupError>;

    #[doc(hidden)]
    pub fn finish(self) -> ClosedTypeArena;
}
```

`finish` is infallible: no transaction can remain active outside the
higher-ranked callback, scratch clearing/drop cannot produce a recoverable
error, and the arena has already passed all finalization checks. Compile probes
prove the exact session trait set, inaccessible construction, and removal of
the superseded arena finalizer methods. F4 Bottom/Int finalization is always
performed through the one session, then observes schemes through its
`scheme_view` until finish.

`TermPage` uses fixed backing, not `Vec` capacity:

```rust
struct TermPage {
    base: u32,
    initialized: u16,
    nodes: Box<[MaybeUninit<TermNode>; 256]>,
}
```

`initialized <= 256`; construction uses a fallible exact boxed-array
allocation. The page has exactly 256 logical physical slots regardless of
allocator byte rounding, which is excluded from the F5 capacity model like
allocator metadata. `reserved(N)` and `slack(N)` in §7 are therefore exact slot
counts. A page buffer is dropped only with exactly its initialized prefix;
commit/unwind guards destroy that prefix before releasing the page.

Prefix alignment is computed while collection creates `TermLineage`, before a
batch is observable. Checked `align_up(collected_len, 256)` overflow maps to
the existing `CollectionAvailabilityError::ComponentIdentityExhausted`; this
is the established collection-index capacity category and adds no public enum
variant. A deterministic test-only collected-length seam proves the maximum
aligned success, the overflowing failure, and no partially returned batch.

The bounded F5b evidence in §7 additionally proves exact 256-slot backing,
session reuse across 64 schemes, the session's trait/removal compile probes,
and prefix-alignment overflow mapping. F5e remains responsible for full
physical resource certification.
