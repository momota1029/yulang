# Successor T4 delimited recovery register correction amendment

Status: Authoritative

Date: 2026-09-07

Drafted-by: primary from T4 architecture preflight after T3 local construction

Reviewed-by: M3 compiler/recovery, specification, and performance review;
one authority repair and clean compiler/specification/performance delta review
on 2026-09-07

Approved-by: user through the active legacy-parser replacement objective, which
authorizes a reviewed recommended proposal to proceed absent a material issue,
on 2026-09-07

Scope: correct only the finite T4 register and the distinct T7c evidence cell,
then
propose the owner-bounded recovery capability needed to migrate its
Parenthesized, EffectRow, BracketRow, and BracketRowArrow cells in ordered
slices.  It does not authorize a code change until review and approval.  It
does not authorize T5--T7 except the distinct T7c evidence cell, PV1,
Call/T1--T3 changes, Yumark/session transport,
public dispatch, legacy production changes, or cutover.

Governing sources:

- `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md` §§2, 3.2--3.3,
  Gate 0 ledger, Gate 5, rollback, and review;
- `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md` T4, T7c, §5b, and
  RB-T;
- `2026-08-20-yu-syntax-chasa-architecture.md` Type-delimited recovery,
  EffectRow recovery, BR-R/BR-RP, and BR-A;
- `2026-09-06-successor-typed-output-recovery-amendment.md` §§3--11;
- `2026-09-07-successor-structured-recovery-prerequisite-ordering-addendum.md`
  §§2.2--4;
- `2026-09-07-successor-t3-typecall-recovery-amendment.md`, only as a
  precedent for owner-bounded successive terminals and O3/O6 timing.

## 1. False premise and narrow register correction

The existing T4 register conflicts with the governing TypeExpression contract:
same-line `A B` is one valid TypeApply item unless inherited type-ML stops the
first item.  It must not receive a separator Missing.  The matrix therefore
cannot authorize implementation of its current T4b, T4e, or T4g literals.
Implementing them would change valid syntax/CST, contrary to rewrite-plan
§2(1).

Supersedes if approved, and only for the T4/T7c register cells in the Gate3b
matrix:

- T4b `(A B)` is replaced by `(A{})`, whose ParenthesizedSeparator Missing is
  `2..2`; `(A B)` is a required one-TypeApply, zero-recovery control;
- T4e `'[A B]` is replaced by `'[A{}]`, whose EffectRowSeparator Missing is
  `3..3`; `'[A B]` is a required one-TypeApply, zero-recovery control;
- T4f's quoted `'[,]` is an EffectRow, not BracketRow, and is replaced by
  `T [,] -> U` for BracketRowItem;
- T4g `[A B]` is replaced by `T [A{}] -> U`, whose BracketRowSeparator Missing
  is `4..4`;
- T4h's BracketRowArrow expectation is punctuation `->`, not TypeExpression;
- T7c keeps its own direct/embedded witness and certification obligation while
  sharing T4A's one BracketRowArrow implementation producer.

The corrected finite register has ten T4 producer cells, not the former eight,
plus the distinct T7c evidence cell.  Each owner needs Item, Separator, and
Close cells, plus one BracketRowArrow cell:

| ID | owner / role | primary direct witness |
| --- | --- | --- |
| T4P1 | ParenthesizedItem | `(,)` Missing |
| T4P2 | ParenthesizedSeparator | `(A{})` Missing `2..2` |
| T4P3 | Parenthesized close | `(A` Missing; `(])` Error `1..2` |
| T4E1 | EffectRowItem | `'[,]` Missing; `'[@]` Error `2..3` |
| T4E2 | EffectRowSeparator | `'[A{}]` Missing `3..3` |
| T4E3 | EffectRow close | `'[A` Missing; `'[)]` Error `2..3` |
| T4B1 | BracketRowItem | `T [,] -> U` Missing; `T [:] -> U` Error `3..4` |
| T4B2 | BracketRowSeparator | `T [A{}] -> U` Missing `4..4` |
| T4B3 | BracketRow close | `T [A` Missing; `T [A)] -> U` Error `4..5` |
| T4A | BracketRowArrow | `F [e]` Missing; `F [e] @` Error `6..7`, expected `->` |
| T7c | distinct BracketRowArrow evidence | replaces the matrix's erroneous `R({type T = '[A] @})` EffectRow literal with `R({type T = F [e] @})`; shares T4A's producer but keeps its own witness |

The existing Parenthesized-close Missing prerequisite remains valid and is only
re-executed as T4P3 evidence; this correction does not repeal it.

T3 §2.2's inherited type-ML transport restriction remains Authoritative:
transport is Call-only.  This correction neither supersedes it nor introduces
Parenthesized/EffectRow transport.  `G (F A)` and `G '[F\n  A]` remain direct
legacy/successor no-recovery TypeApply controls rather than separator witnesses.

## 2. Typed Missing and close-error contract

Every Missing remains on the existing typed operation with primary index zero.
The finite roles and expectations are:

| cell class | role | expected syntax |
| --- | --- | --- |
| Item | `Type(ParenthesizedItem)`, `Type(EffectRowItem)`, or `Type(BracketRowItem)` | `TypeExpression` |
| Separator | corresponding `...Separator` role | `DelimitedSequenceSeparator` |
| Close | `ClosingDelimiter { owner, delimiter }` | matching punctuation |
| Arrow | `Type(BracketRowArrow)` | punctuation `->` |

Missing anchors are unchanged:

- an abstract pending boundary uses `PendingBoundary::coordinate()`;
- an un-emitted lexical/caller Item uses its remaining-start; and
- after owner-emitted leading, EOF, or an owner boundary, the anchor is that
  Item's post-frontier remaining-start.

One-item close mismatch Errors use the existing typed Error operation and retain
one `Unknown` child.  Parenthesized and BracketRow emit a later close Missing
when mismatch reaches EOF/boundary; EffectRow suppresses that same-episode
Missing.  Actual matching close and caller/outer/abstract boundaries outrank
mismatch recovery.  No close Error gains the §3 child-topology exception.

## 3. Proposed eighth terminal and owner-local child delta

Existing fifth, sixth, and seventh sealed Error terminals are explicitly
ArrowRhs-, PathSegment-, and CallArgument-only.  They cannot be reused or
broadened.  This amendment proposes a distinct eighth terminal, available only
to an open Error for T4P1, T4E1, T4B1, or T4A after the owning retry loop has
established its exact owner-specific priority.

It may, once only:

1. classify a valid retry payload or the finite BracketRow S/B continuation
   target, leading policy, close/separator/caller/outer/abstract boundary,
   contiguity, carrier/quote prefix, and current frontier before mutation;
2. borrow one immediate retry Item with a nonempty eligible remaining-leading
   prefix;
3. emit that complete prefix into the Error, advancing only the Item frontier;
4. finalize terminally with equal Error-node/record/fact extent and one whole-
   run `OtherCharacter` fact; and
5. return that same Item for the owner-local retry, or for the finite
   BracketRow S/B continuation, return the unchanged payload to the selected
   BracketRow handler.

Carrier/quote prefixes, prior frontier movement, malformed retry payload,
boundary/close/separator payload except the finite BracketRow S/B case,
noncontiguous leading, a second use, and any post-seal operation are
ineligible and leave Error, record/evidence, and Item unchanged.
`Payload::Boundary`, a fragment carrier, and `YmQuotePrefix` are always
atomically ineligible.  The operation cannot use source retention, range/text
copying, Item clone/split, replay, a second builder, or nested recovery.

Leading policy is total.  Let **S** mean: emit the complete contiguous
remaining-leading prefix as native children in the open Error, make node,
record, and one `OtherCharacter` fact share that extended range, advance only
the leading frontier, and return the Item with payload untouched.  **O/R**
means: terminal-ineligible; end Error before leading, then owner emits leading
outside Error and retries.  **O/B** means terminal-ineligible; leading and
payload remain for separator/close/caller/terminal handling.  **S/B** is
BracketRow-only: S the leading prefix, then return an unchanged
separator/close/stop/EOF payload to its owner.

| retry leading / target after nonempty Error | Parenthesized | EffectRow | BracketRow | BracketRowArrow |
| --- | --- | --- | --- | --- |
| horizontal whitespace before valid Type primary; for Arrow, exact `->` or valid RHS | S | S | S | S |
| LF/CRLF, deeper indentation, before valid target | O/R | O/R | S | O/R |
| LF/CRLF equal/shallow or active caller newline | O/B | O/B | O/B | O/B; Arrow and RHS stay incomplete |
| unfragmented single- or multiline BlockComment plus horizontal parts before valid target | S | S | S | S |
| LineComment then deeper LF/CRLF plus indent before valid target | O/R | O/R | S | O/R |
| LineComment then equal/shallow/caller LF/CRLF | O/B | O/B | O/B | O/B |
| unterminated LineComment before EOF | O/B | O/B | S/B to EOF | O/B |
| separator, matching/local-mismatch close after eligible same-line/deeper gap | O/B | O/B | S/B | O/B |
| ordinary EOF, lexical active stop, or outer lexical close after eligible same-line/deeper gap | O/B | O/B | S/B | O/B |
| `Payload::Boundary`, fragment carrier, or any `YmQuotePrefix` | atomic rejection | atomic rejection | atomic rejection | atomic rejection |

A BlockComment is one opaque leading part: an internal LF/CRLF is not a
Newline part and must not be split.  A carrier-bearing multiline comment is
rejected.  Each physical LF or CRLF remains one Newline child/range and its
indent is a separate Whitespace child.  These priority cases are determined
before mutation; O/B and atomic rejection leave the Item frontier unchanged.

For every physical malformed payload Item actually consumed by these T4 P/E/B/A
Error runs, ordinary or eighth-finalized, use its native
`type_recovery_error_syntax_kind`; every emitted leading part uses its native
Whitespace/Newline/LineComment/BlockComment kind.  Thus `@` is `Unknown` while
`T [:] -> U` has a `Colon(":")` Error child.  A CRLF is one Newline child and a
multiline BlockComment is one BlockComment child.  S/B-returned
separator/close/boundary payloads are not Error children.  Close-slot Errors
remain excluded and retain their one coalesced `Unknown` child.

The representative exact successor topology is:

| source | Error range and direct children | continuation |
| --- | --- | --- |
| `(@ A)` | `1..3`: `Unknown("@")` `1..2`, Whitespace `2..3` | `A` `3..4`, close `4..5` |
| `'[@ A]` | `2..4`: `Unknown("@")` `2..3`, Whitespace `3..4` | `A` `4..5`, close `5..6` |
| `T [@ A] -> U` | `3..5`: `Unknown("@")` `3..4`, Whitespace `4..5` | `A` retries in BracketRow |
| `T [@\n  A] -> U` | `3..7`: Unknown `3..4`, Newline `4..5`, Whitespace `5..7` | `A` retries in BracketRow |
| `T [@\r\n  A] -> U` | `3..8`: Unknown `3..4`, Newline `4..6`, Whitespace `6..8` | `A` retries in BracketRow |
| `T [@\nA] -> U` | `3..4`: Unknown `3..4`; newline outside Error | equal newline is owner boundary |
| `T [@/**/ A]` | `3..9`: Unknown, BlockComment `4..8`, Whitespace `8..9` | `A` retries |
| `T [@/*\n*/ A]` | `3..10`: Unknown, one BlockComment `4..9`, Whitespace `9..10` | `A` retries |
| `T [@ , A] -> U` | `3..5`: Unknown `3..4`, Whitespace `4..5`; comma remains `5..6` | S/B then separator owner |
| `T [@\n  ` at EOF | `3..7`: Unknown `3..4`, Newline `4..5`, Whitespace `5..7`; EOF remains outside Error | S/B then EOF owner |
| `F [e] @ -> U` | `6..8`: Unknown `6..7`, Whitespace `7..8`; Arrow `8..10` outside Error | T4A accepts actual Arrow |
| `F [e] @\n  -> U` | `6..7`: Unknown only; newline/indent outside Error | deeper retry trivia outside Error |
| `F [e] @\n-> U` | `6..7`: Unknown only; newline unconsumed | equal newline is caller boundary |

All rows have one equal-range Error record, singleton expectation at that range,
primary index zero, and one equal-range `OtherCharacter` fact.  Error text/range,
parent/sibling topology, continuation, records, evidence, expectation,
diagnostic order, and losslessness remain exact.  The exception is limited to
the named T4 Error owners and never covers a close Error, un-emitted part,
non-T4 owner, or parent/sibling topology.

Supersedes if approved, only for those named physical T4 Error-run parts:

- typed-output amendment §4's whole-Item/literal-only ErrorRunOutput surface
  and its architecture-return sentence, for the eighth terminal;
- typed-output amendment §1's unchanged-CST sentence, rewrite-plan §2(1)'s
  exact green-tree rule and §5 full-CST acceptance bullet, for this exact
  direct-child delta; and
- Item-emission-ownership-frontier amendment Scope and §5's whole-Item
  malformed nonboundary rule, for the same bounded partial-leading operation.

All other Item-frontier ownership/emission, older terminals, owners, and CST
topology remain unchanged.

## 4. Ordered construction, evidence timing, and exclusions

After approval, implementation proceeds only in this order:

1. T4P — complete Parenthesized owner;
2. T4E — complete EffectRow owner;
3. T4B — BracketRow Item/Separator/Close; then
4. T4A — BracketRowArrow.

Each slice needs direct fresh/frozen records, exact CST/Item ownership,
same-line and LF/CRLF/comment/separator/matching/local/outer-close/EOF/caller/
abstract-fence controls, shifted-origin controls, and seeded-output RB-T.
Before successor expectations, a direct legacy baseline must execution-pin the
source-verified Parenthesized `(A{})` tuple (`2..2`, two complete elements,
no other recovery).  EffectRow `'[A{}]` and direct T7c are already pinned by
legacy unit controls; their new embedded direct baselines must execution-pin
the stated source locators, CST, remainder, losslessness, and frame balance.
BracketRow additionally proves Item Missing before close Error, no same-slot
Missing after an Item Error, and no ArrowRhs-Missing cascade after T4A failure.
T7c remains a distinct evidence cell: direct `F [e] @` is BracketRowArrow Error
`6..7`; its embedded `\ref({type T = F [e] @})` locator is the only trailing
`@`, source-counted at global `21..22` with punctuation Arrow expectation.
That offset is not execution-pinned until its direct legacy baseline runs.  It
shares T4A's producer but has its own direct baseline, RB-T, and O6
equality/frame/topology obligation.  Its RB-T active `STOP_WITH` control keeps `with` plus leading
space pending after local Error `6..7`, without BracketRowArrow Missing or an
ArrowRhs record; the seeded-output rejection must preserve input/remainder,
Item frontier/line entry, mark/operator identity, output checkpoint/node/slot
counts, diagnostic cursor, and frozen/preseeded state.
Existing T1--T3, Call, named-record, forall, PV, and valid TypeApply controls
must remain unchanged.

Local O3/O4 evidence may prove only direct successor records, CST/Item
ownership, continuation, fresh/frozen reconciliation, and RB-T.  The aggregate
T4 row remains Open until O6 runs real successor Yumark, compares actual
embedded AST facts with successor records in source order, proves topology,
frame pop, and a clean following `\ref(C)`.  Before then, legacy embedded
direct baselines may pin records/CST/losslessness/remainder/frame balance but
must not fabricate embedded AST-fact equality.  Embedded numeric offsets are
not yet verified; use exact source locators until those direct baselines run.

T5--T7 except this T7c evidence cell, PV1, all existing owner changes,
Yumark/session transport, public dispatch/cutover, legacy deletion,
general-delimited capability, source replay, and O4/O7 broad suites remain
excluded.

## 5. Cost, rollback, review, and approval

Valid paths add only constant owner dispatch.  The eighth terminal runs after
an Error sees one retry Item; for malformed bytes `B` and leading bytes/parts
`P`, it makes a constant number of `O(B + P)` scans and emits each accepted
byte/part once.  It allocates no source buffer/replay state/Item clone.  Static
review must reject a rescan or quadratic path; timing budget is zero unless it
finds material uncertainty.

Return to architecture without implementation if a direct legacy control
contradicts this register, implementation requires forbidden retained source,
split/clone/replay/builder/nested recovery, an outer boundary enters Error, or
a topology exception leaks outside §3.  Each slice rolls back to the preceding
clean commit while retaining this corrected register.

M3 compiler/recovery, specification, and performance review closed after one
authority repair and clean delta.  The active replacement objective's
recommended-proposal authority approves this amendment.  Only the ordered T4P
slice may begin; T4E, T4B, T4A, T7c certification, and every excluded scope
remain separately gated.
