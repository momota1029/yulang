# Successor T4 inherited type-ML correction amendment

Status: Draft

Date: 2026-09-07

Drafted-by: primary after the T4P §5 architecture return

Scope: correct only the inherited outer-TypeApply type-ML premise that
invalidated the approved T4 correction amendment's Parenthesized and EffectRow
separator evidence.  It defines one private provenance-bearing context required
to preserve that scope, but no new Error terminal, CST topology exception, or
public interface.  It does not authorize implementation or expected-output
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

The legacy execution-pinned and source-derived control register is:

| source | evidence state | required direct record | required continuation |
| --- | --- | --- | --- |
| `(F A)` | source-derived; legacy baseline pending | none | one Parenthesized item, TypeApply `F A` |
| `'[F A]` | source-derived; legacy baseline pending | none | one EffectRow item, TypeApply `F A` |
| `G (F A)` | legacy execution-pinned | `Type(ParenthesizedSeparator)` Missing `5..5` | outer Apply argument has two Parenthesized items; matching `)` is consumed |
| `G (F\n  A)` | legacy execution-pinned | `Type(ParenthesizedSeparator)` Missing `7..7` | newline and indent are Parenthesized-owned trivia; two items; matching `)` is consumed |
| `G (F\r\n  A)` | source-derived; legacy baseline pending | `Type(ParenthesizedSeparator)` Missing `8..8` | Newline `4..6`, Whitespace `6..8`, two items, matching `)` `9..10` |
| `G '[F A]` | source-derived; legacy baseline pending | `Type(EffectRowSeparator)` Missing `6..6` | Whitespace `5..6`, two EffectRow items, matching `]` `7..8` |
| `G '[F\n  A]` | legacy execution-pinned | `Type(EffectRowSeparator)` Missing `8..8` | outer Apply argument has two EffectRow items; matching `]` is consumed |
| `G '[F\r\n  A]` | source-derived; legacy baseline pending | `Type(EffectRowSeparator)` Missing `9..9` | Newline `5..7`, Whitespace `7..9`, two items, matching `]` `10..11` |

The existing no-trivia witnesses remain additional, not replacement, cells:
`(A{})` has ParenthesizedSeparator Missing `2..2`, and `'[A{}]` has
EffectRowSeparator Missing `3..3`.  Each has two complete items and no other
recovery.  The latter is legacy execution-pinned; the former and its exact
direct CST remain a required legacy baseline under T4 §4.

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

## 2. Provenance-scoped context and recovery ownership

The existing `type_ml: bool` is insufficient: non-TypeApply positional
declaration and polymorphic-variant paths also require the tail-stop behavior.
This amendment therefore defines one private by-value context type:

```text
TypeMlContext := Inactive | NonTypeApplyScoped | OuterTypeApply
```

`type_apply_argument_normalized` alone constructs `OuterTypeApply` for its
one argument TypeExpression.  Existing declaration/PV positional entries
construct `NonTypeApplyScoped`; all ordinary entries construct `Inactive`.
Both active states preserve the established nonempty-trivia tail stop, so T3
Call still receives only `is_active()` behavior.  A pair of bools is forbidden,
because it permits impossible active/origin combinations.

The value is lexical and by-value: it is not stored in `Item`, `Recover`,
`NormalizedExit`, session-local state, a record, or output.  Every probe and
exit restores it by construction.  Only a ParenthesizedGroup or EffectRow
primary entered with `OuterTypeApply` may pass that value to immediate
delimited item parses.  It remains available through a direct
Parenthesized/EffectRow-to-item-to-Parenthesized/EffectRow chain, so the
source-derived controls `G ((F A))` and `G ('[F A])` must be execution-pinned
before successor expectations.  Call, arrow RHS, forall, NamedRecord,
PolymorphicVariant, declaration payload, BracketRow, and every other
independent owner downgrade it to `NonTypeApplyScoped`; crossing any such
owner is a return-to-architecture condition.

After each completed item stops at active inherited type-ML, the direct
delimited owner applies this exact priority before a separator Missing:

1. un-emitted caller, outer, and abstract boundaries hand off unchanged;
2. the owner emits eligible owned trivia outside any Error node, preserving
   native Whitespace, Newline, LineComment, or BlockComment token boundaries;
3. a literal comma or semicolon, actual/local/outer close, or qualifying
   implicit-newline boundary wins with no separator Missing; then
4. only a `None` or `DeeperNewline` gap with an unconsumed valid next Type
   primary publishes one committed-rule Missing with the owner's separator role,
   expected `DelimitedSequenceSeparator`, primary index zero, and the
   un-emitted next Item's remaining-start; and
5. the owner retries that unchanged Item as its next complete TypeExpression.

For `G (F A)`, the Parenthesized owner emits the space `4..5`, publishes the
Missing at `5..5`, then retries `A`.  For `G '[F\n  A]`, the EffectRow owner
emits Newline `5..6` and Whitespace `6..8`, publishes at `8..8`, then retries
`A`.  The Parenthesized CRLF witness has Newline `4..6` then Whitespace
`6..8`; the EffectRow CRLF witness has Newline `5..7` then Whitespace `7..9`.
No Error node, `OtherCharacter` fact, or close record is created by these
successful separator episodes.

The required no-Missing controls are `G (F , A)` / `G '[F , A]` for an
explicit separator, `G (F\nA)` / `G '[F\nA]` and equal/shallow LineComment
forms for qualifying implicit boundaries, and `G (F\n  )` / `G '[F\n  ]`
for actual close.  Active caller/outer/abstract boundaries remain unconsumed.
The direct owner, rather than outer TypeApply, retains delimiter frame, Item
frontier, trivia, Missing record, and retry ownership.

The `OuterTypeApply` origin applies only to ParenthesizedGroup and EffectRow.
It must not extend into standalone delimiters, Call beyond T3's existing
active-stop behavior, NamedRecord, PolymorphicVariant, BracketRow,
BracketRowArrow, or a nested TypeExpression that is not a direct P/E chain.
`NonTypeApplyScoped` declaration/PV controls prove unchanged current successor
state, output, records, Item frontier, and line entry; their legacy parity is
not asserted here and remains separately characterizable.  BracketRow may have
an analogous edge, but it is an explicit T4B preflight audit item rather than
authority for this amendment.

## 3. Ordered construction and evidence

T4P remains the first construction slice, but cannot begin until this Draft is
Authoritative.  Before successor expectations, it execution-pins every
source-derived Parenthesized tuple in §1--2, including `(F A)`, `(A{})`, CRLF,
priority, and direct P/E-chain controls.  T4E remains a later ordered slice
and first execution-pins all its source-derived EffectRow tuples, including
same-line `G '[F A]`, CRLF, priority, and direct P/E-chain controls.  T4B and
T4A do not receive construction authority.

For each affected owner, local O3/O4 evidence must prove:

- exact AST/CST source order: owner-owned trivia, Missing node, then second
  TypeExpression, with the matching close afterward;
- same-line, LF, CRLF, block-comment, and line-comment inherited-context
  controls, including native trivia kinds and shifted origins;
- fresh/frozen equality of record ID/order, role, range, expectation, primary
  index, Item frontier, line entry, `TypeMlContext`, delimiter/stop/episode/
  outer-boundary restoration, and lossless remainder;
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

The private by-value context replaces a bool through the existing normalized
TypeExpression cone.  It adds no source retention, scan, allocation, clone,
split, replay, buffer, builder, cache, worklist, or dynamic dispatch.  Valid
input adds one constant state branch per existing immediate item and no
traversal; recovery work and the already-approved eighth terminal remain
unchanged.  Timing budget is zero unless review identifies a material resource
change.

Return to architecture without implementation if direct legacy execution
contradicts a listed witness, propagation requires a global or non-immediate
context, `OuterTypeApply` leaks across a downgrade owner or into an exit value,
a caller/outer boundary is consumed, the separator is published by TypeApply
rather than its delimited owner, an Error/topology exception leaks, or the T4B
audit finds a dependency that cannot remain excluded.  Any implementation
returns to clean commit `b70951c2` while retaining this Draft.

This Draft requires M3 compiler/recovery, specification, and performance
review.  Because the false premise is material, their Reviewed recommendation
must present the corrected behavior and remaining alternatives to the user for
a fresh approval before any T4P/T4E implementation or expected-output change.
