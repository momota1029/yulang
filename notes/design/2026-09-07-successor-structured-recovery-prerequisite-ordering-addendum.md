# Structured-recovery prerequisite-ordering addendum

Status: Authoritative

Date: 2026-09-07

Drafted-by: primary after implementation-preflight contradiction

Reviewed-by: M3 compiler/recovery, specification, and performance review;
three review/repair rounds plus one documented successor-rollback evidence
exception delta on 2026-09-07

Approved-by: user

Approved-at: 2026-09-07

Scope: only the recovery-publication ordering and the already-required
ParenthesizedTypeGroup close-CST correction needed to make the approved
structured PV tag-name caller and its unchanged three-record evidence reachable.
No public dispatch, legacy cutover, local-mismatch close migration, or broader
Type/PV certification is in scope.

Depends-on:

- `2026-09-07-successor-structured-recovery-reservation-amendment.md`;
- `2026-09-07-successor-structured-recovery-extent-validation-addendum.md`;
- `2026-09-06-successor-typed-output-recovery-amendment.md`;
- `2026-09-04-yu-syntax-pv-nt8-same-slot-trivia-amendment.md`;
- `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md` T4c, PV1, RB-T, and
  RB-PV.

Supersedes: reservation amendment §8.3 only where its first-checkpoint
exclusion would forbid the two named prerequisite recovery producers and the
four-owner delimiter discriminator below, and §8.3–8.4 only where their phase
order places the structured caller before records which mandatory §7 evidence
requires to precede/follow it. Every other O3 owner, cause, and migration
remains excluded from the checkpoint.

## 1. Finding

The structured-reservation amendment's §7 requires the fresh and frozen record
stream for `:{@ (A}` to be, in order:

1. `Type(PolymorphicVariantTag)`, Error, `2..3`, ID 0;
2. `Type(PolymorphicVariantTagName)`, Error, `4..6`, ID 1;
3. `ClosingDelimiter(ParenthesizedTypeGroup, Parenthesis)`, Missing, `6..6`,
   ID 2.

At the completed output prerequisite, production rewrite still emits all
recovery CST nodes through raw `emit_error_item` / `emit_missing`; no production
grammar caller publishes a typed record. Migrating only the tag-name caller
would reserve the first frozen position for TagName while the required frozen
stream begins with the prefix Tag record. It cannot satisfy the approved
fixture, its source/ID order, or frozen reconciliation.

The current successor also hands an outer-owned non-`)` close from a
ParenthesizedTypeGroup back without the matrix-required Missing CST node. T4c
already requires that group-owned Missing before the pending `}`. The required
direct-CST correction is therefore part of reaching the pre-existing Type
contract, not a license to migrate local mismatched-close Error recovery.

The contrary phase order is therefore a false premise, not permission to weaken
the fixture or construct a provisional record stream.

## 2. Decision: exact prerequisite order

Before the one structured tag-name caller, migrate exactly these two named
recovery causes. They retain existing handoff, Item ownership, and rollback
behavior; §2.2 adds only the matrix-required ParenthesizedGroup Missing CST
immediately before an outer-owned close handoff.

### 2.1 PV NT-8 malformed-prefix Error

In the existing `PolymorphicVariantTag > Error` malformed-prefix scanner, use
the sealed lexical Error-run output for the complete contiguous NT-8 run. Its
one typed record has:

- `GrammarRole::Type(TypeRole::PolymorphicVariantTag)`;
- `RecoveryKind::Error`;
- the Error-run's exact nonempty contiguous range for site, singleton Token
  unexpected fact, and singleton expectation;
- `UnexpectedCategory::OtherCharacter`, `ExpectedSyntax::Identifier`,
  `ExpectationSources::COMMITTED_RECOVERY_RULE`, and primary expectation 0.

For `:{@ (A}`, this is exactly `@`, `2..3`, ID 0. The established NT-8
same-slot rule remains unchanged: the subsequent same-line candidate's leading
trivia is emitted directly under the same tag, never as part of this Error
range.

### 2.2 Parenthesized Type-group close Missing

Replace private `TypeDelimitedOwner::{Generic, BracketRow}` with the explicit
four-owner discriminator `{Call, ParenthesizedGroup, EffectRow, BracketRow}`
and route the existing three Generic call sites accordingly. This only reveals
existing ownership; it does not alter their CST or boundary behavior.

Only `ParenthesizedGroup` may publish a typed **close** Missing in this
addendum. Every branch that recovers that owner's missing close—initial or
post-head boundary/caller-boundary/EOF, malformed-item retry, and separator
continuation—must select the same owner-specific close publication. Missing
item or separator slots remain raw. Call, EffectRow, and BracketRow recovery
slots remain raw, including BracketRow's existing special behavior.

For `ParenthesizedGroup`, the close classifier has this fixed precedence in
each of those paths:

1. matching `)` is consumed normally and publishes no recovery;
2. a non-`)` close satisfying `is_type_outer_close(item, incoming_outer_closes)`
   publishes exactly one close Missing and hands back the same Item;
3. a non-`)` close not owned by `incoming_outer_closes` remains the existing
   raw, unconsumed successor handoff and publishes no close Missing or other
   typed record here;
4. EOF, an abstract payload boundary, or a non-close active caller boundary
   publishes exactly one close Missing and hands the pending boundary back;
5. ordinary candidate and separator behavior remains unchanged.

The unmodified `incoming_outer_closes` value must thread through every
`retry_type_delimited_item_normalized` and `type_after_separator_normalized`
call and their recursive edge. The nested TypeExpression alone receives
`with_type_outer_close(incoming_outer_closes, close)`; passing that augmented
value to a container helper would falsely classify its own `)` as outer-owned.
Close classification precedes generic caller-boundary classification for a
closing token.

The direct-CST correction emits the Missing before returning an outer-owned
close, but does not consume, retag, or move that close. It introduces no new
trivia action: each path emits exactly the leading trivia the previous path
emitted, anchors at the pending Item's remaining start after that action, and
returns the same payload, successor coordinate, line entry, remainder, and
post-existing leading state.

Each such close record has:

- `GrammarRole::ClosingDelimiter { owner: ConstructRole::ParenthesizedTypeGroup,
  delimiter: Delimiter::Parenthesis }`;
- `RecoveryKind::Missing`, no unexpected evidence, and a zero-width range at
  the existing pending Item's remaining start after the current owner has
  emitted the same leading trivia it emitted before this addendum;
- singleton `ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
  Delimiter::Parenthesis))`,
  `ExpectationSources::COMMITTED_RECOVERY_RULE`, and primary expectation 0.

T4c retains its exact `before("}")` contract. In `:{@ (A}`, the pending PV
`}` remains unconsumed and PV-owned; the group gains the required Missing CST
immediately before that handoff and its close record is `6..6`, ID 2.

### 2.3 Structured tag-name caller after both prerequisites

Only after 2.1 and 2.2 are in place, migrate
`type_polymorphic_variant_tag_after_wrong_kind_normalized` to the private
structured helper already approved by the reservation and extent-validation
addenda. It reserves the TagName record after the NT-8 record and before the
nested TypeExpression, so the nested Parenthesized close publishes after it.

The §7 decisive fixtures, ranges, IDs, CST ancestry, direct same-slot trivia,
actual-PV-close handoff, recursive LIFO case, and fresh/frozen reconciliation
remain exactly as already approved. A TagName-only record stream, shortened
frozen input, synthetic placeholder, insertion/sorting, suppressed nested
recovery, or any other provisional evidence boundary is forbidden.

## 3. Boundary, rollback, and performance

This is a prerequisite-order correction within O3a, not certification of any
Type/PV family. It authorizes no recovery causes beyond the two named producers,
the stated ParenthesizedGroup outer-close Missing correction, and the one
already-approved structured caller. It adds no source retention, Item range
state, replay, event buffer, second builder, general transaction, or public API.

The enum discriminator is Copy-sized routing state. Valid input has no typed
recovery allocation or final extraction; recovered prefix/close sites use the
already-approved O2 Error-run or Missing publication, and the tag-name uses the
already-approved structured slot. There is no new traversal, lookup, sort,
clone, or asymptotic change. Static performance review decides whether a timing
sample is needed.

Rollback restores the production migration work to `813521af` while retaining
that completed output prerequisite if any required record cannot preserve CST,
trivia, pending `}`, remainder, Item identity, source/ID order, or exact frozen
reconciliation.

## 4. Required evidence

Before claiming this narrow checkpoint complete, prove:

- fresh and frozen exact three-record `:{@ (A}` evidence, including all tuple
  fields, IDs `0, 1, 2`, CST ancestry, direct whitespace, and PV-owned `}`;
- fresh and frozen recursive `:{:{123}}` outer/inner structured records with
  exact ranges `2..8` / `4..7`, IDs `0, 1`, and LIFO completion;
- `:{123}`, ordinary `:{A}`, T4c, NT-8 same-slot trivia, caller-close handoff,
  and named `rb_pv_rejected_candidate_preservation` / `rb_t_parenthesized_close`
  witnesses for Item identity, remainder, line entry, and CST/trivia stability;
- named `parenthesized_close_initial`, `parenthesized_close_post_head`,
  `parenthesized_close_malformed_retry`, and
  `parenthesized_close_after_separator` outer-close/local-mismatch fixture
  pairs. Each outer case asserts the complete typed tuple and one Missing; each
  local control asserts byte-exact CST plus the same unconsumed Item, payload,
  remainder, line entry, and leading state, with no close Missing or other
  typed record. Add individual `parenthesized_close_matching`,
  `parenthesized_close_eof`, `parenthesized_close_abstract_boundary`, and
  `parenthesized_close_nonclose_caller_boundary` cases for classifier arms
  1 and 4: matching `)` has no recovery; each missing-close boundary has one
  complete typed tuple and preserves its pending boundary. Include a
  trivia-prefixed outer-close anchor case and prove Call, EffectRow, and
  BracketRow controls retain their raw/no-record recovery behavior after
  routing discrimination;
- each `rb_t_parenthesized_close` and `rb_pv_rejected_candidate_preservation`
  witness translates the matrix rollback obligations at the successor boundary:
  seed an independent output control, finish both trees, and compare Rowan
  output, recovery slots/complete records, diagnostic next-ID/frozen cursor,
  input remainder, Item identity/payload/leading state, successor coordinate,
  and line entry. It also proves the same operator-table reference and the
  existing operator-only `Recoverable::Mark = ()` surface; it introduces no
  legacy `ParseLocal`, sink, cut, or persistent recovery-log carrier;
- frozen mismatch rejection independently at prefix, TagName, and close
  positions before cursor advance/slot replacement; as in the governing
  reservation contract, mismatch then panics and discards the current output,
  not a reusable rollback transaction;
- focused Type/PV tests, `cargo check -p yu-syntax`, formatting, and diff
  check. Broad suites remain at their O4/O7 barrier.

## 5. Rejected alternative and approval record

The rejected alternative is a provisional TagName-only checkpoint with an ID 0
stream that deliberately conflicts with the final three-record stream. It
would make frozen artifacts temporarily incompatible with the approved contract
and would require a later semantic replacement.

User approved the prerequisite ordering, the two precisely named typed recovery
publications, and the matrix-required ParenthesizedGroup outer-close Missing
correction above on 2026-09-07, followed by the already-approved structured PV
tag-name caller and unchanged final fixture.
