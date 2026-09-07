# Successor T4 inherited type-ML correction amendment

Status: Authoritative; T4P local construction complete

Date: 2026-09-07

Drafted-by: primary after the T4P §5 architecture return

Reviewed-by: M3 compiler/recovery, specification, and performance review;
three bounded repair rounds, architecture return for the retained T3 Call
transition, and clean targeted specification closure

Approved-by: user (narrow outer-TypeApply-only option)

Approved-at: 2026-09-07

Scope: correct only the inherited outer-TypeApply type-ML premise that
invalidated the approved T4 correction amendment's Parenthesized and EffectRow
separator evidence.  It defines one private provenance-bearing context required
to preserve that scope, but no new Error terminal, CST topology exception, or
public interface.  It authorizes only T4P local construction after the required
direct legacy baselines in §3.  T4E remains an ordered later gate, and no local
checkpoint authorizes owner-complete T4, O4, public/Yumark, or production
expected-output changes.

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
declaration and polymorphic-variant paths also require the tail-stop behavior,
while an OuterTypeApply provenance must remain live across a whole nested
argument even when a nonreactive owner lies between it and a P/E item.  This
amendment therefore defines one private by-value context type with two private
semantic axes:

```text
TypeMlContext {
  provenance: None | NonTypeApply | OuterTypeApply,
  stop_here: bool,
}
```

Private constructors/transitions, rather than loose bool parameters, guarantee
the required dormant `{ OuterTypeApply, false }` state.  Only committed
`type_apply_argument_normalized` enters `{ OuterTypeApply, true }` for its one
argument TypeExpression.  Standalone PV and Enum/Error positional payload
scopes enter `{ NonTypeApply, true }`; ordinary entries are inactive.  A
NonTypeApply scope entered while OuterTypeApply is live retains the latter
provenance and restores the caller value on lexical return.  A nested
TypeApply inside NonTypeApply temporarily enters OuterTypeApply and restores
NonTypeApply afterward.  `stop_here` retains the existing nonempty-trivia tail
stop.  Call is provenance-blind and phase-preserving: it captures its incoming
`TypeMlContext` and passes that identical value to every immediate CallArgument
attempt and retry.  Thus active `{ OuterTypeApply, true }` retains T3's
authorized CallArgumentSeparator behavior, while dormant
`{ OuterTypeApply, false }` does not reactivate solely from provenance.

The value is lexical and by-value: it is not stored in `Item`, `Recover`,
`NormalizedExit`, session-local state, a record, or output.  Every probe and
exit restores it by construction.  Provenance is threaded unchanged through
every nested owner for the full lexical outer-TypeApply argument; a nonreactive
owner carries dormant OuterTypeApply provenance rather than erasing it.  Only
ParenthesizedGroup and EffectRow derive `stop_here = true` for their immediate
delimited item parsing when that provenance is OuterTypeApply.  Call preserves
its captured context for each direct CallArgument under its existing T3 rule;
after an argument returns it never adopts a child-derived phase.  Other
nonreactive owners forward dormant provenance so a later nested P/E can react.
No Call role, trigger, range, or terminal is added by this amendment.  Candidate
probes never construct OuterTypeApply, and every outer continuation retains its
pre-argument value.

After each completed item stops at active inherited type-ML, the direct
delimited owner applies this exact priority before a separator Missing:

1. un-emitted caller, outer, and abstract boundaries hand off unchanged;
2. the owner emits eligible owned trivia outside any Error node, preserving
   native Whitespace, Newline, LineComment, or BlockComment token boundaries;
3. a literal comma or semicolon, actual matching close, or owner-local mismatch
   wins with no separator Missing; then
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
for actual close.  Abstract/ASOB/caller boundaries and outer-owned closes are
classified before any trivia/frontier/output mutation; their pending leading
and payload are untouched for the caller.  EOF is distinct: a locally owned
Item may emit eligible leading before its close-Missing path.  The direct owner,
rather than outer TypeApply, retains delimiter frame, Item frontier, trivia,
Missing record, and retry ownership.

Only ParenthesizedGroup and EffectRow newly act on `OuterTypeApply` provenance
by activating an immediate item stop and publishing their own separator Missing.
Call retains its already-authorized T3 behavior: whenever its incoming
`stop_here` is active, it may publish the existing CallArgumentSeparator and
Call slots using the unchanged T3 priority.  NamedRecord, PolymorphicVariant,
BracketRow, BracketRowArrow, arrow, forall, and declaration owners remain
nonreactive while forwarding dormant provenance.  In particular, `G T[F A]->U`
gains no BracketRowSeparator under this amendment, though its provenance must
reach any nested P/E.

Legacy global `type_ml_arg` may make P/E react to a standalone NonTypeApply
PV/declaration origin too.  This amendment deliberately does not claim that
parity: `:{Tag (F A)}`, `:{Tag '[F A]}`, `enum E = Tag X (F A)`, and
`enum E = Tag '[F A]` are source-derived characterization controls.  Their
legacy baselines must run before any semantic expectation is assigned.  They
remain Open for a later reviewed scope expansion; consequently this amendment
can authorize only T4P local construction, never owner-complete T4 or O4
certification.  BracketRow's own analogous reaction remains a T4B preflight
audit item rather than authority here.

## 3. Ordered construction and evidence

T4P is the authorized first construction slice.  Before successor expectations,
it execution-pins every
source-derived Parenthesized tuple in §1--2, including `(F A)`, `(A{})`, CRLF,
priority, `G ((F A))` (inner ParenthesizedSeparator `6..6`),
`G T((F A))` (ParenthesizedSeparator `7..7`, Call publishes nothing), and
`G T[(F A)]->U` (ParenthesizedSeparator `7..7`, BracketRow publishes nothing).
T4P also preserves the T3 controls: `G T(F A)` retains its one
CallArgumentSeparator Missing at `6..6`; `T(F A)` remains one ordinary Call
argument with no recovery; and `G T((F A))` has only the named
ParenthesizedSeparator, not a Call record.  T4E remains excluded as a later
ordered slice; it first execution-pins all its
source-derived EffectRow tuples, including same-line `G '[F A]`, CRLF,
priority, `G ('[F A])` (EffectRowSeparator `7..7`), and
`G T('[F A])` (EffectRowSeparator `8..8`, Call publishes nothing), plus a
BracketRow-forwarding EffectRow witness.  T4B and T4A do not receive
construction authority.

For each affected owner, local O3 evidence must prove:

- exact AST/CST source order: owner-owned trivia, Missing node, then second
  TypeExpression, with the matching close afterward;
- same-line, LF, CRLF, block-comment, and line-comment inherited-context
  controls, including native trivia kinds and shifted origins;
- fresh/frozen equality of record ID/order, role, range, expectation, primary
  index, Item frontier, line entry, `TypeMlContext`, delimiter/stop/episode/
  outer-boundary restoration, and lossless remainder;
- RB-T seeded-output rejection and handoff matrix for inactive,
  `{ OuterTypeApply, true }`, `{ OuterTypeApply, false }`, and
  `{ NonTypeApply, true }` phase inputs.  Every failed probe, complete,
  caller/outer/abstract boundary, outer-close, local-close, EOF, and frozen
  rejection proves unchanged caller-retained context, input/remainder, pending
  Item identity/frontier/leading, origin/LineEntry, delimiter/stops/fence,
  mark/operator identity, output checkpoint/node/token/slot counts, recovery
  IDs/order, diagnostic cursor, and frozen cursor.  Required transitions also
  include rejected TypeApply probe then standalone P/E, affected parse then
  standalone P/E, NonTypeApply entered inside OuterTypeApply and restored
  without erasing it, and nested TypeApply restoring NonTypeApply afterward;
- actual-close, caller stop, outer close, EOF, and abstract-boundary priority
  controls with no separator record or boundary consumption; and
- standalone `(A B)` / `'[A B]` zero-recovery controls plus unchanged T1--T3,
  including the exact T3 Call active/dormant-context controls, Call,
  named-record, forall, PV, and valid TypeApply cases.

The aggregate T4/T7c matrix remains Open.  O6 must later execute real
successor Yumark for both inherited-context witnesses, compare actual embedded
facts with successor records in source order, prove frame pop and exact
trivia/Missing topology, and parse a clean following `\ref(C)`.  Embedded
offsets remain unverified until those direct legacy baselines execute.

The direct legacy Parenthesized (T4P) baselines were execution-pinned at
`7ed1d35b`.  The one authorized T4P local construction pass completed at
`3bedfbef` on 2026-09-07.
It replaces the normalized TypeExpression cone's loose `type_ml: bool` with the
private by-value context in §2; activates only immediate Parenthesized items
from an outer-TypeApply provenance; preserves Call's existing T3
phase-preserving behavior; and forwards dormant provenance through the named
nonreactive owners.  The completed local proof includes exact direct CST
topology/ranges, native trivia, priority, fresh/frozen, RB-T seeded-state,
rejection, handoff, restoration, and no-EffectRow/BracketRow-publication
controls.  It grants neither T4E nor owner-complete T4/O4 credit.

## 4. Cost, rollback, and review gate

The private by-value context replaces a bool through the existing normalized
TypeExpression cone.  It adds no source retention, scan, allocation, clone,
split, replay, buffer, builder, cache, worklist, or dynamic dispatch.  Valid
input adds constant state propagation/branch work per existing nested entry and
per immediate P/E item, with no traversal; recovery work and the already-
approved eighth terminal remain unchanged.  Timing budget is zero unless review
identifies a material resource change.

Return to architecture without implementation if direct legacy execution
contradicts a listed witness, provenance leaks into an exit value or fails to
cross a nested owner inside the lexical outer argument, a caller/outer boundary
is consumed, the separator is published by TypeApply rather than its delimited
owner, a nonreactive owner publishes a separator, an Error/topology exception
leaks, or the T4B audit finds a dependency that cannot remain excluded.  A
later scoped implementation may return to clean commit `b70951c2` while
retaining this Authoritative amendment.

M3 compiler/recovery, specification, and performance review closed the
authority design with three bounded repair rounds.  The final specification
finding restored T3's unchanged provenance-blind, phase-preserving Call
transition; architecture adjudicated the exact transition and the targeted
independent specification closure was clean.  The user approved the narrow
outer-TypeApply-only option.  M3 implementation review then closed T4P after
two test-evidence-only repair rounds and clean compiler/recovery, specification,
and regression deltas; no repair changed production routing.  The final focused
T4P/T3/legacy controls, package check, format check, and diff check passed;
timing usage is zero.  T4E, NonTypeApply PV/declaration P/E parity (including
the currently unconstructible declaration incoming-Outer witness), T4B/T4A,
T7c certification, O4, O6, public/Yumark, and production expected-output
changes remain excluded.
