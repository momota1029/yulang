# Successor T4 inherited type-ML correction amendment

Status: Draft

Date: 2026-09-07

Drafted-by: primary after the T4P §5 architecture return

Scope: correct only the inherited outer-TypeApply type-ML premise that
invalidated the approved T4 correction amendment's Parenthesized and EffectRow
separator evidence.  It defines no new Error terminal, CST topology exception,
or public interface.  It does not authorize implementation or expected-output
changes before M3 review and a fresh user decision.

Governing sources:

- `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md` §§2, 3.3, Gate 5,
  rollback, and review;
- `2026-08-20-yu-syntax-chasa-architecture.md` Type ML scope and layout
  composition, Type-delimited call and Parenthesized-group layout,
  ParenthesizedTypeGroup recovery, and EffectRow composition/recovery;
- `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md` T3, T4, T7c, §5b,
  and RB-T;
- `2026-09-07-successor-t3-typecall-recovery-amendment.md` §2.2, only for
  its bounded Call construction and the supersession named below; and
- `2026-09-07-successor-t4-delimited-register-correction-amendment.md` §§1,
  4--6.

## 1. Confirmed false premise and narrow supersession

The suspended T4 amendment correctly rejects standalone `(A B)` and `'[A B]`
as separator-recovery witnesses: each is one valid TypeApply item with zero
recovery.  It incorrectly extends that fact into a nested outer-TypeApply
context.  The legacy parser's `type_ml_arg` scope stops a nested type before
every nonempty trailing trivia cluster; the enclosing delimited owner then sees
the remaining valid primary and emits its own separator Missing.

The executed legacy controls are therefore:

| source | required direct record | required continuation |
| --- | --- | --- |
| `(F A)` | none | one Parenthesized item, TypeApply `F A` |
| `'[F A]` | none | one EffectRow item, TypeApply `F A` |
| `G (F A)` | `Type(ParenthesizedSeparator)` Missing `5..5` | outer Apply argument has two Parenthesized items; matching `)` is consumed |
| `G (F\n  A)` | `Type(ParenthesizedSeparator)` Missing `7..7` | newline and indent are Parenthesized-owned trivia; two items; matching `)` is consumed |
| `G (F\r\n  A)` | `Type(ParenthesizedSeparator)` Missing `8..8` | CRLF is one Newline child, indent is Whitespace; two items; matching `)` is consumed |
| `G '[F\n  A]` | `Type(EffectRowSeparator)` Missing `8..8` | outer Apply argument has two EffectRow items; matching `]` is consumed |
| `G '[F\r\n  A]` | `Type(EffectRowSeparator)` Missing `9..9` | CRLF is one Newline child, indent is Whitespace; two items; matching `]` is consumed |

The existing no-trivia witnesses remain additional, not replacement, cells:
`(A{})` has ParenthesizedSeparator Missing `2..2`, and `'[A{}]` has
EffectRowSeparator Missing `3..3`.  Each has two complete items and no other
recovery.  The former still needs the direct legacy baseline already required
by T4 §4.

If approved, this amendment supersedes only:

1. T4 §1's assertion that `G (F A)` and `G '[F\n  A]` are zero-recovery
   controls, and its treatment of `(A{})` / `'[A{}]` as the sole T4P2/T4E2
   witnesses;
2. T4 §4 evidence wording derived from that assertion; and
3. T3 §2.2's exclusion only insofar as it would prohibit a Parenthesized or
   EffectRow owner from observing the already-active, outer-TypeApply
   type-ML scope.

T3 remains Call-only for its own construction credit, typed Call records, and
seventh Error terminal.  This correction does not broaden Call behavior or
give any other owner that terminal.  It does not change T4P1/P3, T4E1/E3,
T4B, T4A, T7c, the eighth terminal's eligibility, direct-child topology, or
any public/Yumark/legacy-production surface.

## 2. Scoped context and recovery ownership

TypeApply alone establishes and restores inherited type-ML scope.  A
ParenthesizedGroup or EffectRow primary entered while that scope is active must
pass the same scoped context into each immediate delimited item parse.  It is
not a new owner flag, global mode, or TypeApply-side recovery special case.

When a first item stops at that inherited type-ML frontier and the same
delimited owner sees a valid next Type primary after nonempty trivia, that
owner must, in this exact order:

1. emit the still-owned physical trivia outside any Error node, preserving
   native Whitespace, Newline, LineComment, or BlockComment token boundaries;
2. publish exactly one committed-rule Missing with the owner's separator role,
   expected `DelimitedSequenceSeparator`, primary index zero, and the
   un-emitted next Item's remaining-start; and
3. retry that unchanged Item as the owner's next complete TypeExpression.

For `G (F A)`, the Parenthesized owner emits the space `4..5`, publishes the
Missing at `5..5`, then retries `A`.  For `G '[F\n  A]`, the EffectRow owner
emits Newline `5..6` and Whitespace `6..8`, publishes at `8..8`, then retries
`A`.  The CRLF witnesses use one Newline child at `5..7` and start the Missing
after indentation.  No Error node, `OtherCharacter` fact, or close record is
created by these successful separator episodes.

Actual matching close always outranks a possible separator.  Thus
`G (F\n  )` and `G '[F\n  ]` retain their matching-close path with no
separator Missing.  Active caller/outer/abstract boundaries remain unconsumed.
The direct owner, rather than outer TypeApply, retains delimiter frame, Item
frontier, trivia, Missing record, and retry ownership.

The correction applies only to ParenthesizedGroup and EffectRow.  It must not
propagate into standalone delimiters, Call beyond T3's existing behavior,
NamedRecord, PolymorphicVariant, BracketRow, BracketRowArrow, or a nested
TypeExpression that is not directly carrying the outer TypeApply scope.
BracketRow may have an analogous edge, but it is an explicit T4B preflight
audit item rather than authority for this amendment.

## 3. Ordered construction and evidence

T4P remains the first construction slice, but cannot begin until this Draft is
Authoritative.  Its direct legacy baseline first execution-pins `(A{})`, then
adds fresh and frozen successor proof for all Parenthesized witnesses in §1.
T4E remains a later ordered slice and execution-pins the EffectRow witnesses
when it begins.  T4B and T4A do not receive construction authority.

For each affected owner, local O3/O4 evidence must prove:

- exact AST/CST source order: owner-owned trivia, Missing node, then second
  TypeExpression, with the matching close afterward;
- same-line, LF, CRLF, block-comment, and line-comment inherited-context
  controls, including native trivia kinds and shifted origins;
- fresh/frozen equality of record ID/order, role, range, expectation, primary
  index, item frontier, line entry, delimiter/stop-frame restoration, and
  lossless remainder;
- actual-close, caller stop, outer close, EOF, and abstract-boundary priority
  controls with no separator record or boundary consumption; and
- standalone `(A B)` / `'[A B]` zero-recovery controls plus unchanged T1--T3,
  Call, named-record, forall, PV, and valid TypeApply cases.

The aggregate T4/T7c matrix remains Open.  O6 must later execute real
successor Yumark for both inherited-context witnesses, compare actual embedded
facts with successor records in source order, prove frame pop and exact
trivia/Missing topology, and parse a clean following `\ref(C)`.  Embedded
offsets remain unverified until those direct legacy baselines execute.

## 4. Cost, rollback, and review gate

The required propagation is an existing scoped boolean/context branch.  It
adds no source retention, scan, allocation, clone, split, replay, buffer,
builder, cache, worklist, or dynamic dispatch.  Valid input adds no traversal;
recovery work and the already-approved eighth terminal remain unchanged.
Timing budget is zero unless review identifies a material resource change.

Return to architecture without implementation if direct legacy execution
contradicts a listed witness, propagation requires a global or non-immediate
context, a caller/outer boundary is consumed, the separator is published by
TypeApply rather than its delimited owner, an Error/topology exception leaks,
or the T4B audit finds a dependency that cannot remain excluded.  Any
implementation returns to clean commit `b70951c2` while retaining this Draft.

This Draft requires M3 compiler/recovery, specification, and performance
review.  Because the false premise is material, their Reviewed recommendation
must present the corrected behavior and remaining alternatives to the user for
a fresh approval before any T4P/T4E implementation or expected-output change.
