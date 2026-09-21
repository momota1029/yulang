# F5b closed-finalization accounting boundary amendment

Status: Authoritative; implementation complete
Scope: result-attached byte accounting from yu-types closed finalization to the
existing F4 aggregate counters in yu-solver
Approved-by: user, 2026-09-22
Decision: return only byte values required for existing F4 aggregate memory
accounting; defer detailed closed-type counters to F5e
Drafted-by: primary from the user decision and architecture repair
Reviewed-by: M2 specification and resource-accounting delta review, 2026-09-22
Supersedes: the F5b closed-finalization amendment §§7.2 and 8 only at the
finalize_scheme/finish return declarations named in §2; §7.3 only to permit
the narrow result-attached byte boundary below

## 1. Problem and non-goals

yu-types owns closed nodes, permanent indexes, reusable overlay capacity, and
the immutable closed arena. yu-solver owns F4's existing aggregate
ProductionCounters: semantic-arena and inference-session retained/peak byte
totals. Direct live session retained/staging byte queries leak session internals
across the crate boundary.

The user selected the smallest result-attached replacement. It exposes five byte
values total, solely to compose those four existing F4 aggregate fields. It
creates no detailed public F5b counter and exposes no raw lane, node, handle,
index, scratch layout, allocator detail, or live arena/session getter. It changes
neither inference, scheme closure, publication, failure mapping, F4
scheme_table meanings, nor F5e resource certification.

## 2. Narrow sealed result API

This amendment supersedes only these declarations in the F5b closed-finalization
amendment:

- §7.2's finalize_scheme -> Result<ClosedValueScheme, ...> and
  finish -> Result<ClosedTypeArena, ...> declarations;
- §8's finalize_scheme -> Result<ClosedValueScheme, ...> and
  finish -> ClosedTypeArena declarations.

All other §7.2/§8 ownership, staging, failure, ordering, session-trait, and
scheme_view requirements remain Authoritative.

    #[doc(hidden)] pub struct ClosedSchemeFinalization { /* private */ }
    #[doc(hidden)] pub struct ClosedTypeAccountingCheckpoint { /* private */ }
    #[doc(hidden)] pub struct ClosedTypeFinalizationOutput { /* private */ }
    #[doc(hidden)] pub struct ClosedTypeAccountingReceipt { /* private */ }

    impl ClosedTypeFinalizationSession {
        #[doc(hidden)]
        pub fn try_new() -> Result<Self, ClosedTypeFinalizeError>;

        #[doc(hidden)]
        pub fn finalize_scheme<F>(
            &mut self,
            build: F,
        ) -> Result<ClosedSchemeFinalization, ClosedTypeFinalizeError>
        where
            F: for<'tx> FnOnce(
                &mut ClosedTypeFinalizer<'tx>,
            ) -> Result<(), ClosedTypeFinalizeError>;

        #[doc(hidden)]
        pub fn scheme_view<'a>(
            &'a self,
            scheme: &'a ClosedValueScheme,
        ) -> Result<ClosedValueSchemeView<'a>, ClosedTypeLookupError>;

        #[doc(hidden)]
        pub fn finish(self) -> ClosedTypeFinalizationOutput;
    }

    impl ClosedSchemeFinalization {
        #[doc(hidden)]
        pub fn into_parts(self) -> (
            ClosedValueScheme,
            ClosedTypeAccountingCheckpoint,
        );
    }

    impl ClosedTypeAccountingCheckpoint {
        #[doc(hidden)] pub const fn retained_bytes_before(&self) -> usize;
        #[doc(hidden)] pub const fn retained_bytes_after(&self) -> usize;
        #[doc(hidden)] pub const fn peak_bytes_during_call(&self) -> usize;
    }

    impl ClosedTypeFinalizationOutput {
        #[doc(hidden)]
        pub fn into_parts(self) -> (
            ClosedTypeArena,
            ClosedTypeAccountingReceipt,
        );
    }

    impl ClosedTypeAccountingReceipt {
        #[doc(hidden)] pub const fn retained_bytes_before_finish(&self) -> usize;
        #[doc(hidden)] pub const fn retained_bytes_after_finish(&self) -> usize;
    }

No public F5b API exposes closed-node allocation counts, requested slots,
actual capacity, capacity growth, per-lane bytes, staging-only bytes, finalizer
counters, or physical storage topology. Those are private yu-types test evidence
until F5e. No accounting getter exists on the live session, finalizer, arena,
scheme, closed handle, or closed view. Values are observable only on a
result-attached checkpoint or receipt.

## 3. Exact trait contract

All four result/accounting types have private fields and no public constructor;
they implement Debug + Send + Sync, and do not implement Clone, Copy, Hash, Ord,
Default, or serialization. Checkpoint and receipt additionally implement
Eq + PartialEq; the two owning envelopes have no equality contract. into_parts
consumes its envelope, so the envelope cannot be retained while its scheme or
arena is independently extracted.

The existing session contract remains unchanged:

    ClosedTypeFinalizationSession: !Clone + !Copy + !Debug + !Send + !Sync

No auto-trait promise exists beyond the result types' explicit Send + Sync.

## 4. Byte accounting domain

Every checkpoint and receipt counts all capacity-managed yu-types
closed-finalization storage: committed permanent closed nodes and indexes,
reusable overlay, draft-to-final maps, commit planning, rollback storage, and
any other session-owned staging. Allocator metadata, fragmentation, and
fixed-size owner fields are excluded, matching F4's existing capacity-byte
convention. All sums are checked; overflow returns the existing
ClosedTypeFinalizeError::IdentityExhausted before a successful result exists.
The session maintains both byte totals as checked private state. Every capacity
change computes and stores replacement totals before that change becomes
observable; overflow aborts the active fallible finalize_scheme with
IdentityExhausted and rolls back its logical publication. finish only transfers
these prevalidated totals and performs no fallible aggregation.

For a successful finalization:

    peak_bytes_during_call >= retained_bytes_before
    peak_bytes_during_call >= retained_bytes_after

For finish:

    retained_bytes_after_finish <= retained_bytes_before_finish

retained_bytes_after_finish excludes dropped finalization staging and includes
only storage retained by the returned immutable ClosedTypeArena.

## 5. Failure epochs and checkpoint continuity

The session owns a private, monotonically ordered failure epoch. It starts at
zero, advances on every unsuccessful finalize_scheme invocation, and tags each
successful checkpoint with its current epoch. The epoch has no public accessor
and remains yu-types test-only.

Within an uninterrupted success epoch:

    checkpoint[n].retained_bytes_before
        == checkpoint[n - 1].retained_bytes_after

A failed reservation may retain capacity, so the first later successful
checkpoint may have a different retained_bytes_before; it belongs to a later
failure epoch. Failure returns neither scheme nor checkpoint and publishes no
logical work. Retained failed-attempt capacity appears in a later successful
checkpoint and final receipt only when a direct caller retries.

Production yu-solver returns on any finalization failure. Thus every checkpoint
seen by one successful solve is in one uninterrupted epoch and the solver's
continuity assertion is exact.

## 6. Solver-owned current closed retained bytes

InferenceSession owns one private scalar:

    current_closed_retained_bytes: usize

It starts at zero: try_new creates no capacity-managed closed storage. Before
each finalization, solver forms checked semantic and session totals excluding
closed finalization. The callback may read a prepared draft but cannot allocate,
clear, or mutate a non-yu-types resource lane, so those baselines remain
constant for that call.

After a successful finalization, solver asserts the checkpoint's before equals
the scalar, calculates checked call-peak candidates by adding
peak_bytes_during_call to each baseline, and updates the scalar from the
checkpoint's after value. From that point to the next successful finalization
or finish, every existing F4 resource sample includes the scalar once:

    sampled_semantic_retained =
        sampled_semantic_without_closed + current_closed_retained_bytes
    sampled_session_retained =
        sampled_session_without_closed + current_closed_retained_bytes

Semantic storage remains a subset of session storage and the closed value is
never added twice. Finalization failure returns before later resource sampling,
scheme installation, incoming routing, finish, or partial SolvedModule
publication.

## 7. Finish and final-output coexistence

Immediately before session consumption, the scalar still equals all retained
closed-finalization storage. finish returns the receipt; solver asserts its
retained_bytes_before_finish equals the scalar, then replaces the scalar with
retained_bytes_after_finish.

Final semantic/session retained totals each add the post-finish scalar once.
The final-output coexistence candidate adds that same scalar and the separately
computed finish-output retained bytes. All additions are checked. Final peaks
are the maximum of prior F4 samples, all successful-call candidates, post-finish
retained coexistence, and final-output coexistence. The receipt deliberately
has no whole-session peak: adding a local peak to an unrelated solver peak is
forbidden because their maxima may happen at different times.

## 8. Exact F4 ProductionCounters mapping

This boundary writes only these existing fields, indirectly through the checked
temporal formulas in §§6–7:

    semantic_arena_retained_bytes
    semantic_arena_peak_bytes
    inference_session_retained_bytes
    inference_session_peak_bytes

No result value maps to a closed-node allocation field, closed-arena requested
slots/capacity/retained/peak/growth field, or any other nonexistent F5 counter.
scheme_table continues to describe only dense Option<ClosedValueScheme> slots.
F5e owns detailed closed-node and closed-arena resource counters.

## 9. Required proof

Compile probes prove all four types are unconstructible and Send + Sync;
checkpoint/receipt equality; absent Clone, Copy, Hash, Ord, Default, and
serialization; consuming into_parts; and absence of every live accounting getter.
yu-types tests prove peak inequalities, same-epoch continuity, failure-epoch
advance, failed-attempt retained capacity, failure without a checkpoint, finish
before/after accounting, staging drop, private physical-lane reconciliation, and
overflow without an envelope.

yu-solver tests prove zero initial closed retained storage; every later F4 sample
includes the latest closed retained value; frozen-baseline call peaks; post-finish
and final-output composition; semantic subset/session total; no double counting;
failure-before-later-sampling/publication; unchanged F4 Bottom/Int
routes/projections/availability variants; unchanged scheme_table; and F5a's zero
Function facts. F5e retains the 1k/2k/4k resource matrix and all public detailed
accounting.

Return to design if implementation needs a direct live-storage getter, an
additional public counter, a cross-crate accounting callback, per-lane public
topology, unchecked aggregate arithmetic, or changed F4 counter meaning.
