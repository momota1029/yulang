# Successor PV payload-admission capability amendment

Status: Draft

Date: 2026-09-07

Drafted-by: primary after payload-adapter architecture re-entry

Scope: a proposed private capability prerequisite for conditional malformed
polymorphic-variant payload admission.  It authorizes no source, test
expectation, or public behavior change.

Depends-on:

- `2026-09-07-successor-pv-wrong-kind-primary-completion-amendment.md` §6;
- `2026-09-07-successor-structured-recovery-reservation-amendment.md` §§4–7;
- `2026-09-07-successor-structured-recovery-extent-validation-addendum.md`
  §2;
- `2026-09-03-yu-syntax-gate4-6-scc-amendment.md` §4.3; and
- direct legacy evidence `4ff97ddc` in
  `crates/yu-syntax/src/grammar/type_expr.rs`.

## 1. Confirmed owner and compatibility table

The primary-completion construction proved that its primary boundary is causal,
but refuted its payload premise.  After `:{123}` completes as a wrong-kind PV
tag head, successor `type_polymorphic_variant_tag_payloads_after_head_normalized`
does not admit an unspaced `::` payload boundary.  It hands that Item back to
outer tag recovery.  Direct legacy instead makes payload admission conditional
on a later retry primary and distinguishes the following cases:

| following surface | direct legacy disposition |
| --- | --- |
| owner boundary, physical newline, native close, or EOF | stop payload admission without consuming it; owner/caller handles the boundary |
| adjacent admissible primary | ordinary payload; an unspaced adjacency has a missing payload boundary |
| unspaced invalid run with a non-ambient admissible retry primary | payload-boundary Error over the invalid run, then a retried payload expression |
| unspaced invalid run with no retry primary | decline payload admission; outer tag recovery owns the run |
| unspaced invalid run whose retry has an ambient owner claim | decline payload admission; outer caller ownership wins even without an active stop bit |
| spaced invalid run | payload-owned whitespace boundary, payload Type Error over the invalid run, then retry only when one is admissible |

`legacy_polymorphic_variant_conditional_payload_admission_is_execution_pinned`
records twelve exact rows: valid and wrong-kind `::`/`->` retries, valid and
wrong-kind dangling `::`, an ambient `else` retry rejection with no active
`Else` stop, spaced recovery, a recovered payload followed by ordinary payload,
newline, native close, and EOF.  It fixes AST slots/ranges, complete direct CST
preorder/token extents, ordered recovery records/evidence, close ownership,
payload shape, caller remainder, and ambient-context balance.  The nested-PV
external-tail row `:{:{A}(B)}` is separately pinned at `b6349f9c`.

For example, `:{123::T}` requires TagName Error `2..5`, then a sibling
`PolymorphicVariantPayload` with PayloadBoundary Error `5..7` and payload `T`
at `7..8`, then native PV close.  The trial primary-completion candidate got
the first range right but created a second `PolymorphicVariantTag` Error at
`5..7`.  No trial source or expectation was integrated.

The payload judge is shared by valid and wrong-kind tag heads.  A wrong-kind
only repair would duplicate the responsibility and leave the pinned valid-name
rows divergent.

## 2. Current capability mismatch

The current direct route owns one already-scanned invalid `Item`.  Its payload
decision must know whether a potentially later primary is admissible and free
of an ambient owner claim before that Item is emitted.  No existing successor
facility can provide that fact under current rules:

1. advancing through `current_item` creates owned Items; declining afterward
   loses intervening bytes unless it re-scans completed Items or retains a run;
2. output checkpointing wraps CST but cannot roll back output, and lexical
   transactions cannot access output; `Recover::Mark` is unit;
3. existing source-only probes inspect one prospective token/trivia fact, not
   an arbitrary malformed run and its retry eligibility; and
4. the payload interface receives stops, type-ML, delimiters, and fence, but
   no ambient-owner claim independent of stops.  The pinned `else` row proves
   such a claim is semantically material.

Deleting the leading-trivia guard, handling `::`/`->` specially, unconditionally
consuming a malformed run, or making the rule wrong-kind-only violates at least
one §1 row.  Retrospective CST wrapping/splitting, emitted-output rollback,
Item cloning, retaining a run/source slice, and replay are likewise forbidden.

## 3. Proposed capability boundary

This Draft proposes a prerequisite, not a construction authorization.  If it
can be reviewed soundly, the shared PV payload judge may receive two private,
non-owning observations before it emits a malformed current Item:

1. a source-only malformed-suffix admission witness, starting at the live raw
   suffix after the current invalid Item and returning only a finite decision:
   `RetryNonAmbient`, `NoRetry`, or `AmbientRetry`; and
2. an explicit ambient payload-owner claim threaded from the owning Type/PV
   context, distinct from active punctuation stops.

The witness may read raw bytes while its lexical transaction is live but must
not advance the live cursor, construct or complete an Item, touch recovery or
output, return an offset/spelling/source slice, retain a cache/run, or assign
CST/trivia/diagnostic ownership.  It is not a general lexer and cannot consume
the current invalid Item.  Ordinary scanning remains solely responsible for
the subsequent actual run emission and payload retry.

The shared payload judge would then retain the §1 order:

```text
outer/physical boundary -> raw handoff
ordinary candidate -> existing payload admission
invalid + empty trivia + NoRetry/AmbientRetry -> tag/caller handoff
invalid + empty trivia + RetryNonAmbient -> boundary Error + retry payload
invalid + nonempty trivia -> payload Type Error, retry only when applicable
```

This does not authorize a particular raw recognizer, a context carrier layout,
or any payload-loop implementation.  The SCC amendment permits only its named
candidate-token/prospective-trivia re-observation.  Therefore extending it to
an arbitrary malformed-suffix traversal, and representing the ambient claim,
are both new decisions that require explicit approval.  An inability to prove
them under the following gates rejects this proposal rather than weakening the
legacy table.

## 4. Required capability proof and cost gate

Before this Draft can become Reviewed, its construction route must prove:

1. a finite raw-witness grammar that matches `consume_invalid_run`'s exact
   stop/retry boundaries without allocating Items or mutating input/recovery/
   output; direct legacy evidence must first cover every newly named
   multi-token, comment, CRLF/fence, and retry-classification row;
2. the complete ambient-claim provenance map for every reachable PV payload
   caller, including the visible-no-stop `else` control, and why normal stops
   are neither overloaded nor silently reinterpreted;
3. no completed Item, source slice, run, offset, cache, recovery record, or
   output checkpoint crosses the probe boundary; decline preserves the current
   Item and all cursors, while a committed frozen mismatch retains the existing
   discard-only reservation contract;
4. an aggregate work bound for repeated payloads and declines.  The witness
   plus ordinary consume may traverse the same malformed run twice; it must
   account for every such traversal and prove no unbounded re-probe of the
   same live bytes across owner transitions; and
5. fresh/frozen exact proof for all §1 rows, prefix/malformed tag/recursive
   reservation controls, Parenthesized/EffectRow extents, valid-name siblings,
   original three `::Next` controls, caller/outer boundary handoff, and
   rejection/mismatch invariants.

The direct parser is hot.  A new arbitrary raw traversal and unknown aggregate
frequency trigger independent performance review.  Timing budget is zero until
static analysis establishes a concrete implementation and a timing result could
change a decision; no benchmark is authorized by this Draft.

## 5. Scope and alternatives

If later authorized, construction may be limited to the shared PV payload
adapter, its immediate lexical/context dependencies, and focused private
successor evidence.  It must preserve the primary-completion policy,
structured Error endpoint/byte validation, record ordering, valid primary
owners, raw close/caller handoff, and all delimiter scopes.  It may not alter
legacy parser behavior, public/root dispatch, AST/HIR, fixtures/goldens,
O6/public certification, or implement a broad lexer/cache/replay facility.

Option 1 (recommended only if §§3–4 close): approve a narrowly specified
source-only witness and ambient-claim prerequisite, then allow a subsequent
shared payload-adapter construction gate.  This restores the legacy conditional
admission table without a wrong-kind exception.

Option 2: retain intentional successor divergence after the primary boundary.
This leaves unspaced malformed payloads tag-owned, prevents integration of the
primary-completion/delimited interaction through those rows, and requires a
cutover reconciliation decision.

This is a material recovery, context, and hot-path traversal decision.  The
recorded recommendation delegation and the blocked primary-completion approval
do not authorize it.  Independent compiler/recovery, specification, and
performance review must close a concrete capability design before a fresh user
choice; until then this Draft authorizes no implementation.
