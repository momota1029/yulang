# F5b terminal accounting-exhaustion amendment

Status: Authoritative; implementation pending
Scope: only the closed-finalization accounting state required to report an
unrepresentable exact capacity total without partial publication
Approved-by: user, 2026-09-22
Decision: make finish fallible using the existing IdentityExhausted error;
do not broaden F5b accounting, counters, storage, or measurement
Drafted-by: primary from M2 finding and architecture recovery
Reviewed-by: M2 specification and resource-safety delta review, 2026-09-22
Supersedes: the accounting-boundary amendment §§2, 4, and 7 only where they
require unconditional/infallible finish output or checked capacity state before
allocator-observed capacity exists; retained F5b §8 only at its infallible
finish statement and reasoning

## 1. Narrow reason

The accounting-boundary amendment correctly requires actual Vec capacity, not
requested capacity. Vec reservation may produce more capacity than requested.
The exact sum can therefore become unrepresentable only after fallible
reservation succeeds. An infallible finish has no sound way to report that
state without fabricating bytes, panicking, or publishing a partial result.

This amendment does not change the five-byte success boundary, existing F4
aggregate counter meanings, the ordinary successful path, Term storage,
language semantics, or F5e. Detailed lane counters, resource certification,
and broad accounting evidence remain deferred.

## 2. Exact API replacement

Replace only the accounting-boundary amendment's finish signature with:

    impl ClosedTypeFinalizationSession {
        #[doc(hidden)]
        pub fn finish(
            self,
        ) -> Result<ClosedTypeFinalizationOutput, ClosedTypeFinalizeError>;
    }

No new public error variant exists. Terminal accounting exhaustion maps to the
existing ClosedTypeFinalizeError::IdentityExhausted.

## 3. Accounting state and transaction order

The session owns private state equivalent to:

    enum AccountingState {
        Valid {
            retained_bytes: usize,
            arena_retained_bytes: usize,
        },
        Exhausted,
    }

The accounting-boundary amendment's pre-capacity-change replacement-total rule
is superseded only for capacity that Rust's allocator reveals after a reservation
returns. After every reservation return, whether success or error, and before
pushing a node, inserting an index, constructing a scheme, or disarming commit
rollback, yu-types reads the actual affected capacities and recomputes the
complete checked byte totals.

- A representable total replaces Valid state before later logical commit.
- A reservation failure may retain capacity. yu-types reconciles that
  representable capacity, advances the private failure epoch, returns the
  existing failure, and permits retry.
- An unrepresentable actual total changes state to Exhausted, advances the
  private failure epoch, returns IdentityExhausted, and leaves arena logical
  lengths/indexes/schemes unchanged.
- An Exhausted session rejects later finalize_scheme calls without running their
  callbacks. This terminal rejection has no possible later checkpoint, so it
  narrowly supersedes the accounting-boundary amendment §5 rule requiring a
  new failure epoch for every rejected invocation.
- Once post-reservation reconciliation succeeds, commit performs no
  capacity-growing operation.
- Callback or commit unwind restores logical state, reconciles representable
  retained capacity and advances the private epoch before resuming the original
  panic. If reconciliation detects terminal exhaustion, it records Exhausted
  but preserves that original panic.

The failure epoch remains private and test-only. Checkpoint Debug and
PartialEq/Eq are implemented manually over their three byte fields only; epoch
is absent from their public formatting and equality behavior.

## 4. Finish and solver publication

finish transfers a Valid state's prevalidated values into its result envelope.
On Exhausted it returns IdentityExhausted and yields no arena or receipt.
Dropping either state remains safe; all raw storage and unpublished handles stay
session-owned.

InferenceSession maps that error through the existing availability mapping and
returns before final result construction. It publishes no ClosedTypeArena,
receipt, SolvedModule, new F4 counter state, or partial scheme slot. The
ordinary successful receipt still writes only the existing aggregate semantic
and session retained/peak counters.

## 5. Minimal required evidence

Focused tests prove:

- a test-only actual-capacity observation seam can force terminal excess after a
  successful reservation, yielding IdentityExhausted before logical commit and
  no checkpoint/envelope;
- finish on that terminal session returns the same error;
- a representable failed reservation retains capacity and can retry;
- an unwind restores logical state and preserves the original panic, including
  a deterministic terminal-excess-during-unwind seam whose later finish returns
  IdentityExhausted;
- solver finalization/finish exhaustion publishes neither SolvedModule nor
  final aggregate counters.

Runtime evidence uses internally made equal-byte/different-epoch checkpoints to
prove public Debug omits epoch and equality ignores it; compile probes retain
the type/constructor/trait surface checks. No F5e scale matrix, detailed lane
counter, new resource report, or storage redesign enters this amendment.

Return to design if the repair needs a new error variant, a fabricated/saturated
byte total, requested-capacity accounting, an infallible terminal receipt, a new
public counter, or a custom exact-capacity storage redesign.
