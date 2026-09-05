# Direct expression and statement owner fence-entry addendum

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-05

Drafted-by: primary after the L5 successor-acquisition contradiction

Reviewed-by: independent architecture, specification, and compiler/recovery
review; all blocking findings closed by scoped delta review

Supersedes: only the direct-core successor-acquisition step in
`notes/design/2026-09-02-yu-syntax-expression-tail-handoff-addendum.md` §4,
as specified in §1 below

User direction: the recommended staged owner-local protocol, including the
L5a/L6a/L5b ordering, is approved, 2026-09-05

Scope: the direct-rewrite fence-entry boundary and the order of the isolated
L5/L6 construction gates. This addendum corrects how already accepted direct
owners acquire their next lexical material. It does not add grammar, make Rule
or literal syntax production-reachable, alter a public parser API, complete
interpolation or parsed-Yumark integration, or change the `TailExit` algebra.

## 1. Exact supersession and retained contracts

When Authoritative, this addendum supersedes only the direct-core successor
acquisition step in
`notes/design/2026-09-02-yu-syntax-expression-tail-handoff-addendum.md` §4.
The ordinary direct core no longer hard-codes `scan_trivia` plus
`tail_item_after_trivia` after an accepted NUD/LED; it receives the active
owner's acquisition path. The original document's Item ownership,
total-after-acceptance, rollback, recovery, and three-result handoff remain
unchanged:

```text
TailExit = Ok(()) | Err(Left(Item)) | Err(Right(End))
```

This addendum also refines the L5 implementation order, but does not change
the `ExpressionList(close)` grammar/recovery contract in
`notes/design/2026-09-05-direct-literal-cone-addendum.md` §§2 and 4.2.
That list must eventually accept the full existing direct Expression grammar;
a temporary isolated witness may not redefine that grammar.

## 2. Contradiction and rejected whole-closure shape

An L5 Rule `ExpressionList` cannot recover an exact fence boundary after a
successful child when the direct Pratt core has already obtained that child’s
successor through the ordinary scanner. The original Item's leading trivia,
`PendingFragments`, payload classification, and live suffix have then
already moved; replay, reconstruction, or an outer buffer would violate the
one-forward contract.

A single borrowed complete-`Item` function solves this within the closed
ordinary-expression cone: direct NUD/LED operands, prefix/infix RHSs, ML
arguments, calls, indices, paths, and the ordinary direct delimiter owner
already exchange complete Items. It does **not** transparently solve the full
Expression grammar. A braced primary enters canonical statements, whose
declarations also consume declaration-header Items, raw qualified words,
parameters, Type/Pattern Items, and standalone trivia/token slots. For
example, `type_decl` reaches a declaration-header scanner and `derives`
then owns Type scanner/retry steps.

Making one function cover those unrelated partial lexical products needs a
grammar-wide request enum or a context-like scanner interface. That would grow
whenever an owner is added, obscure local recovery ownership, and recreate the
global mechanism rejected for this rewrite. It is therefore not an
implementation of the approved local-function direction.

## 3. Approved owner-local fence-entry protocol

Every owner with its own lexical protocol receives a second, private,
fence-aware entry of the following semantic shape:

```text
owner_fenced(RewriteIn, immediate origin, &FenceBoundary, owner arguments)
    -> its existing Item / TailExit result
```

It is the same recursive owner and the same CST/recovery procedure as the
ordinary entry. The ordinary entry remains a thin wrapper using its current
ordinary scans. The fenced entry owns only an immediate coordinate and the
borrowed fence boundary for the dynamic extent of its call. Neither entry
stores a cursor, fence, source, token row, callback, or context in `Recover`,
Rowan state, an Item, or a retained frame.

At every point where that owner would inspect **or** consume into a new
physical line—the complete current Item, leading trivia, a declaration header,
a raw identifier slot, a recovery run, or a source-only suffix/layout
probe—the fenced entry first invokes the shared pure fence judge. A probe may
not use bytes on a returned close/transition line to classify an earlier
operator, colon, layout, or contextual form. At that observation boundary it
uses the same result it would have received at end-of-cell, leaves the line
unobserved, and the next owning acquisition returns the exact pending Item.
This applies to `raw_trivia_suffix`, lone-colon/body-layout predicates,
operator fixity probes, and every analogous raw lookahead recorded in the
owner ledger.

After that guard, the owner does exactly one of the following:

1. consumes an accepted equivalent body prefix and records it on the one
   current lexical Item as `ForeignSplit::YmQuotePrefix`;
2. completes the ordinary local lexical product with ordinary source
   ownership; or
3. returns the exact judge-created pending boundary to its immediate caller,
   with no source replay, replacement Item, leading-trivia extraction,
   fragment mutation, or fence-line emission.

Every fenced child call has a local coordinate synchronization point. Its
caller snapshots the live suffix pointer and length plus its current origin
before the call. On return—whether normal, `Left(Item)`, `Right(End)`, or a
private deferred frontier—the caller verifies that the resulting suffix is the
same source pointer advanced by exactly the consumed byte count, then advances
its own immediate origin by that count. A returned pending boundary consumes
zero bytes of its boundary line; any preceding body trivia already consumed is
included in that one suffix delta. This observation uses pointer/length, never
whole-input equality or a root/source wrapper.

The closed direct expression Item cone receives an ordinary-or-fenced borrowed
acquisition function. It is reborrowed through `driver`, `tails`, and
`delimited` only while those owners exchange complete Items. When it reaches
a distinct owner protocol, it calls that owner's matching private fenced entry
directly; it does not expand the complete-Item function into a global request
interface.

## 4. Staged construction order

### L5a — closed direct Item cone and explicit frontier

L5a may complete the Rule string/Pattern witness work already under
construction and may introduce the direct-core ordinary/fenced acquisition seam
for complete Items. Its closed cone is:

- ordinary, prefix, infix, suffix, and ML direct expressions;
- required operands and local recovery;
- calls, indices, paths, projections, and ordinary parenthesized/delimited
  direct expression items; and
- exact Item handoff after those paths.

L5a adds one private, non-production propagation algebra around the retained
`TailExit`:

```text
L5aExit = Complete(TailExit) | Deferred(Item)
```

`Deferred(Item)` is not `TailExit::Left(Item)`. The latter remains an ordinary
Pratt precedence/tail handoff and may be interpreted by that caller; the
former means an unentered distinct lexical owner and must propagate unchanged
through every currently open closed-cone parent. Each propagating owner closes
only its own already-open CST node, emits no recovery for the deferred Item,
and returns `Deferred` without feeding it to tail/ML/list retry logic. Earlier
already committed predecessor tokens may remain in those closed parent nodes;
the deferred child itself has zero CST, Error, or Missing effect. The Rule
witness then returns the same deferred Item to its harness rather than claiming
that its partial construction is a complete ExpressionList.

Before an Item would be interpreted by a distinct protocol—at minimum braced
canonical statements and contextual `if`/`case`/`catch`, and at any
colon/`with` route that enters a statement owner—the L5a witness returns that
same Item as `Deferred`. A call-graph ledger must identify every such frontier
before L5a closes; no inferred “simple expression” subset may be silently
treated as the full list grammar. Required controls place a frontier under a
prefix, infix RHS, ML argument, call/index, and nested delimiter as well as at
the first list Item.

L5a is not L5 completion. It creates no public language restriction and does
not claim fence-after-success support for a deferred owner.

### L6a — owner-local statement/declaration protocol

L6a supplies the private fenced entries needed at that frontier, in this
dependency order:

1. compound expression owners: `if_expr`, `case_like`, and the
   colon/`with` body paths in `tails`;
2. braced and indented canonical statement sequences in `statement`;
3. each current canonical dispatch child: `binding`, `for_decl`,
   `mod_decl`, `struct_decl`, `type_decl`, and `use_decl`;
4. every Pattern and Type owner reached by those children, including
   declaration-header, Type tail, Pattern tail, and `derives` acquisition
   and retry paths; and
5. every raw trivia/token/header loop belonging to one of the preceding
   owners.

This is a local-entry migration, not a central scanner abstraction. Each
owner’s focused ledger records its physical-line checks, exact returned
boundary type, recovery order, and coordinate handoff. An owner may not call
its ordinary entry from its fenced entry after acquiring any input.

### L5b — full Rule ExpressionList closure

Only after L6a, L5b reconnects Rule `ExpressionList(close)` to every existing
direct Expression form. Its list may no longer return a deferred compound
frontier. After a successful simple or compound child, close/transition/EOF
arrives as the exact unchanged Item through `TailExit`; the list emits only
its already-authorized `ExpressionListClose` recovery before handing that
Item back to Rule.

### L6b and later gates

VirtualStatementBlock and StringInterpolation remain the existing L6 work
after L6a. L7 remains the joint literal closure/certification gate. Neither is
advanced by L5a or L6a alone.

## 5. Exact pending-Item and fragment contract

The protocol imports the parsed-fence addendum’s current-Item contract
unchanged.

- A returned pending boundary is the original
  `BorrowedClose(YumarkFence)`, `Stop(YumarkFenceTransition)`, or
  `EofAfterTrivia` Item, including its inspected range, common-root
  coordinate, leading trivia, payload, and live suffix.
- Equivalent accepted active-prefix quote bytes exist only as ordered
  `PendingFragments` `ForeignSplit::YmQuotePrefix` records on that same
  current Item. The scanner-local vector is created only at its first accepted
  prefix and moves once into its boxed carrier at completion.
- No direct owner turns a prefix into `Whitespace`, Yulang token text, a
  range-only replacement, or another Item. No returning owner takes, emits,
  splits, retags, or appends the boundary Item’s leading trivia/fragments.
- Recovery emitted by an already committed inner owner precedes its caller's
  Missing at the same boundary. Yumark alone consumes the returned close or
  transition line and emits its own fence recovery.

Thus the current L5 Rule body-prefix-to-whitespace reclassification remains
forbidden. Normal entries have no origin/fence branches and retain current
ordinary CST/recovery behavior byte-for-byte.

## 6. Required evidence and stop conditions

| gate | focused evidence |
| --- | --- |
| L5a | ordinary/fenced parity for every closed direct Item path; close/transition after NUD/LED, infix, ML, call/index, nested delimiter, multiline trivia, UTF-8/CRLF, and recovery; `Deferred` propagation and zero deferred-child CST/recovery effect at every listed frontier position; exact pointer/length coordinate synchronization; static call-site/frontier ledger |
| L5a observation | paired inputs identical through a close/transition boundary and different only afterwards; operator/contextual/colon/layout classification before the boundary is identical, with no outer-line source observation |
| L6a compound/statement | fence boundary before/after a successful `if`/case/colon/with/braced child; exact braced/indented separator ownership; ordinary wrapper parity; prefix fragment source order; raw probe/coordinate ledger |
| L6a declarations | boundary in binding/for bodies; declaration header/parameter/RHS; Type and Pattern tails; `derives` role/via/retry; multiline comment/trivia; exact error/Missing ordering; raw probe noninterference and coordinate controls; one ledger row for every raw scanner loop |
| L5b | every Rule list child including all former frontiers; first item, separator, trailing/double separator, malformed required Item, child recovery, and close/transition/EOF; original pending Item identity and no list emission of its leading trivia |
| static | no dynamic dispatch, request registry, context/cursor, `Recover` field, retained token Item container, event/body buffer, source replay/copy, second Rowan builder, or unbounded nesting guard |

The static cost remains `O(bytes + structural work)`, with only the already
authorized per-current-Item fragment carrier. No timing measurement is needed
unless implementation introduces a new allocation, dynamic dispatch,
additional traversal, or an uncertain retained-state bound.

Return to design if a local owner needs ambient fence state, an Item
reconstruction, replay, a persistent continuation/frame, a global request
registry, or a source/context wrapper. Such a result invalidates this
owner-local protocol rather than authorizing an exception.

## 7. Gate consequence

The current L5 repair remains uncommitted construction work. It may proceed
only as L5a after the required frontier ledger and focused proof. L5 cannot be
declared complete until L6a and L5b have closed.
