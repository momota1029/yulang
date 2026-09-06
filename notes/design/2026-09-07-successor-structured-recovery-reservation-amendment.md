# Successor structured-recovery reservation amendment

Status: Authoritative

Date: 2026-09-07

Drafted-by: primary after architect adjudication

Reviewed-by: M3 compiler/recovery, specification, and performance review in two
rounds on 2026-09-07

Approved-by: user

Approved-at: 2026-09-07

Scope: one ordered structured `Error > TypeExpression` recovery needed by the
successor polymorphic-variant tag-name owner during O3a.

Depends-on:

- `2026-09-06-successor-typed-output-recovery-amendment.md`;
- `2026-09-04-yu-syntax-pv-nt8-same-slot-trivia-amendment.md`;
- `2026-09-03-yu-syntax-gate4-6-scc-amendment.md`;
- `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md` PV1 and RB-PV/RB-T.

## 1. Reason for the amendment

O2 deliberately restricts `ErrorRunOutput` to lexical/current-Item forward
emission. The O3a inventory found one existing recovery that cannot use that
surface: a wrong-kind polymorphic-variant tag is represented as
`PolymorphicVariantTag > Error > TypeExpression`. The nested TypeExpression may
itself commit recovery, for example a missing parenthesized close.

Retrospective Rowan checkpoint wrapping preserves the CST but would publish an
inner TypeExpression record before the earlier-starting outer tag-name Error.
That violates diagnostic source order and increasing ID order. Tokenizing the
nested type, suppressing its recovery, inserting or sorting records, replaying
source, buffering events, or using a second builder violates existing
Authoritative decisions.

The outer structured Error must therefore reserve its ordered diagnostic
position after the PV owner commits and before the nested TypeExpression runs.

## 2. Narrow supersession

This amendment supersedes the typed-output amendment only where §§3–4 require
every recovery vector element to be complete at append time and prohibit every
node-producing Error body. The existing sealed `ErrorRunOutput` remains the
only API for lexical or malformed-Item runs. One separate structured operation
is added for a total nested grammar body whose outer recovery must precede
inner records.

All other output ownership, source-free/range-free Item, rollback, frozen
reconciliation, Error-run, SCC, boundary, and public-cutover decisions remain
unchanged.

## 3. Ordered slot representation

`RewriteOutput` replaces its internal complete-record vector with:

```rust
enum RecoverySlot<'frozen> {
    Reserved(StructuredReservation<'frozen>),
    Complete(CommittedRecoveryRecord),
}

struct RewriteOutput<'frozen> {
    builder: GreenNodeBuilder<'static>,
    recoveries: Vec<RecoverySlot<'frozen>>,
    diagnostics: DiagnosticSequence<'frozen>,
    active_structured: Option<usize>,
}
```

The reserved slot stores its assigned ID, an optional borrowed
`&'frozen CommittedRecoveryRecord`, known static recovery specification, start
coordinate, and the previous active reservation index. A private affine token
identifies the slot. Beginning a nested structured recovery links to the
current active index; finishing must be LIFO and restores that link in `O(1)`.

Ordinary `commit_recovery` appends a `Complete` slot. On finalization every
slot must be complete and every structured reservation must be closed. One
checked `O(R)` pass consumes the slots into a newly allocated public
`Vec<CommittedRecoveryRecord>` without cloning any record or evidence,
insertion, sorting, or a second publication. Finish therefore temporarily
retains `O(R)` slots plus `O(R)` final records while moving records between the
two buffers. Valid input has zero slots and performs no extraction allocation.

`Vec::new()` still performs no valid-input heap allocation. The active index is
constant-size state; slot allocation occurs only after committed recovery.

## 4. Diagnostic reservation and frozen reconciliation

After owner commitment, structured begin atomically reserves the next
diagnostic identity and appends one ordered reserved slot before nested grammar
emits anything.

- In fresh mode it consumes the next checked ID.
- In reconciliation mode, while a next frozen record exists, it borrows and
  consumes exactly that position, reuses that record's ID, and immediately
  checks every already-known field: role, Error kind, range start, unexpected
  category, expected syntax, expectation sources, and primary index.
- After the frozen slice is exhausted, including when it was empty, reservation
  allocates the next checked fresh ID after the frozen maximum and stores no
  frozen reference. The frozen cursor remains at the slice end. This is the
  exact two-branch analogue of ordinary `publish`.
- The nested grammar then publishes ordinary or structured recoveries into
  later slots and later frozen positions.
- Structured finish supplies the exact nonempty range end, constructs the full
  draft, checks it against emitted extent and the reserved frozen record, and
  replaces that exact slot with `Complete`.

A mismatch, overflow, non-LIFO finish, invalid range, or panic invalidates and
discards the current output. As in O2, no unwind reuse or Rowan rollback is
promised. No reservation occurs on a speculative or `None` path, so
`Recover::Mark` remains unit and the existing RB invariants remain unchanged.

## 5. Grammar-facing capability

Add one private total helper, conceptually:

```rust
emit_structured_recovery_error(
    i,
    start,
    static_spec,
    total_nested_body, // ordinary RewriteIn, returns result and exact end
)
```

The helper reserves first, opens exactly one `SyntaxKind::Error`, runs the
already-committed nested body with ordinary `RewriteIn`, closes the node, and
completes the reserved slot before returning. The reservation token and slot
operations never enter grammar modules. This helper is not a replacement for
lexical `emit_recovery_error_run` and may not be selected where the sealed
Error-run surface suffices.

The initial authorized caller is only the O3a polymorphic-variant wrong-kind
tag-name branch. Any later caller needs a ledgered structured-owner row and
compiler/specification review.

## 6. PV range, record, and boundary contract

The malformed-prefix NT-8 Error, when present, commits first. The same-line
candidate's leading trivia is then emitted directly under the already-open
`PolymorphicVariantTag`, exactly as the 2026-09-04 amendment requires.

The structured tag-name Error begins at the remaining/payload start of the
wrong-kind candidate. Its end is derived immediately after the nested
TypeExpression from the threaded successor coordinate and the returned pending
Item's remaining start, or the current coordinate when no pending bytes exist.
The pending outer close and its leading bytes are excluded. No source/root
slice, stored Item range, CST walk, replay, or fragment-carrier range is used.

The completed record is exactly:

- role: `GrammarRole::Type(TypeRole::PolymorphicVariantTagName)`;
- kind: `RecoveryKind::Error`;
- site, unexpected Token, and expectation range: the same nonempty derived
  range;
- unexpected category: `UnexpectedCategory::OtherCharacter`;
- expected: `ExpectedSyntax::Identifier`;
- sources: `ExpectationSources::COMMITTED_RECOVERY_RULE`;
- primary expectation: `0`.

Record and ID order is outer-before-inner: any NT-8 prefix record, then the
reserved tag-name record, then nested TypeExpression records, then later PV
payload/close records.

## 7. Required evidence

Infrastructure tests cover fresh and frozen reservation, exact completion,
nested LIFO reservations, ordinary publication inside a reservation, empty
frozen and nonempty-frozen-exhausted fresh-ID fallback, mismatch, overflow,
unfinished reservation rejection, no duplicate publication, and zero
valid-input recovery capacity. Exhaustion tests include nested ordinary and
structured publication.

The decisive PV fixture is `:{@ (A}`. It must produce one tag with Error `@`,
direct whitespace, and a tag-name Error containing a
TypeExpression/ParenthesizedTypeGroup with Missing `)`. The actual `}` remains
PV-owned. Ordered records and IDs are exactly:

1. `Type(PolymorphicVariantTag)`, Error, `2..3`, primary `Identifier`, ID 0;
2. `Type(PolymorphicVariantTagName)`, Error, `4..6`, primary `Identifier`, ID 1;
3. `ClosingDelimiter(ParenthesizedTypeGroup, Parenthesis)`, Missing, `6..6`,
   primary punctuation close `)`, ID 2.

Every tuple has one expectation with
`ExpectationSources::COMMITTED_RECOVERY_RULE` and primary index 0. The two
Error tuples have one `UnexpectedSyntax::Token` over their exact range with
`UnexpectedCategory::OtherCharacter`; the Missing tuple has no unexpected
evidence.

The reachable recursive fixture `:{:{123}}` must exercise two real structured
reservations. Its outer tag-name Error contains the complete inner
PolymorphicVariantType and owns `2..8`, ID 0, primary `Identifier`; the inner
tag-name Error owns `4..7`, ID 1, primary `Identifier`. The first `}` closes the
inner PV inside the outer Error, while the second `}` remains pending for and
closes the outer PV outside that Error. Assert exact CST ancestry, both complete
record fields, LIFO completion, exact frozen reuse/order, and no duplicate or
missing record.

Also prove `:{123}` as one structured tag-name Error, ordinary `:{A}` with no
recovery, caller-owned close handoff, NT-8 same-slot trivia cases, exact frozen
reuse/mismatch, and a seeded rejected PV candidate preserving CST, records,
ID/cursor, remainder, and Item identity.

## 8. Performance and implementation gate

Valid input retains no recovery allocation, no new traversal, and the same
single Rowan builder. Recovered input adds `O(R)` slot storage and one final
`O(R)` consuming extraction; begin/ordinary publish/finish remain amortized
`O(1)` excluding exact `O(E_record)` evidence checks. There is no insertion,
sorting, map, source clone, replay, event buffer, or second builder.

Implementation spans an output prerequisite and the first narrow O3a
construction checkpoint:

1. before O3a owner migration, change output storage and diagnostic
   reservation;
2. before O3a owner migration, add the private structured helper and
   infrastructure tests;
3. as the first O3a construction checkpoint, migrate the one PV wrong-kind
   branch and decisive fixtures; this is not Type/PV owner certification and
   admits no other O3 owner;
4. continue the already-approved O3a Type/PV migration;
5. run compiler and specification review for O3a, plus a performance delta
   review for slot storage/extraction.

Pre-approval M3 review uses compiler/recovery, specification, and performance
roles, at most three rounds. Static review has a zero timing budget unless it
finds material uncertainty.

## 9. Rejected alternatives and approval requested

Rejected alternatives are retrospective publication, record insertion or
sorting, an invalid sentinel `CommittedRecoveryRecord`, nested event buffers,
source replay, a second Rowan builder, suppressed nested recovery, and widening
the lexical Error-run capability into a general unreserved builder surface.

Approval authorizes exactly one ordered structured-recovery reservation
mechanism in `RewriteOutput` and its initial PV tag-name caller. It does not
authorize public dispatch, a general speculative diagnostic transaction,
recovery state in `Recover`, or any other O3 owner migration beyond the already
approved typed-output amendment.
