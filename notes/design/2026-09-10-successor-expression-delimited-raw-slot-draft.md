# Expression-delimited raw-slot CST draft

Status: Authoritative; private construction complete

Date: 2026-09-10

Approved-by: user
Approved-at: 2026-09-10
Drafted-by: primary from the direct Rowan collision evidence
Reviewed-by: specification audit, compiler/recovery audit, regression evidence review

Scope: a proposed CST topology distinction for raw recovery inside
`expression::delimited` only. It covers ParenthesizedExpression, CallTail,
IndexTail, ProjectionTupleTail and ProjectionRecordTail. It does not change
accepted syntax, operator selection, current-Item continuation, leading/source
ownership, Missing/Invalid meaning, ProjectionRecordSpreadItem, parser records,
frozen replay, public diagnostics, interpreter/API migration or ledger
retirement.

Governing authority: the Authoritative CST-derived diagnostics amendment,
Error/Invalid topology-ordering addendum and expression-delimited current-Item
recovery authority. This record resolves an owner-schema gap proven by current
behavior.

## Proven collision

The committed direct Rowan control `c265ccf0` proves that, under an empty
operator environment and no inherited close, all three inputs have the same
direct parent/child kinds and ranges:

```text
(@)  -> ParenthesizedExpression(LParen Error-token RParen)
(;)  -> ParenthesizedExpression(LParen Error-token RParen)
(])  -> ParenthesizedExpression(LParen Error-token RParen)
```

The direct Error token is `1..2` in every witness, but the current temporary
records select, respectively, `Expression(Nud)`/Expression,
`Expression(ParenthesizedSeparator)`/DelimitedSequenceSeparator, and
`ClosingDelimiter(ExpressionGroup, Parenthesis)`/Close(Parenthesis). The
future CST interpreter may not inspect Error spelling or retain parser phase,
so the documented grammar cannot derive a unique expected alternative.

This is a schema deficiency, not a parser behavior defect. Existing records
remain compatibility evidence until the complete schema migration.

## Approved decision

Add two transparent shared grammar-slot nodes, admitted only as direct children
of the five listed expression-delimited owners:

```text
ExpressionDelimitedSeparator    := Error+
ExpressionDelimitedForeignClose := Error+
```

Direct raw Error groups remain the existing Item-role occurrence. An Error
group inside `ExpressionDelimitedSeparator` is the existing separator-role
occurrence. An Error group inside `ExpressionDelimitedForeignClose` is the
existing foreign-close occurrence; its immediate parent identifies the existing
owner-specific expected close punctuation. The wrappers themselves have no
diagnostic, attributes or expectation payload. Their Error-token children
produce the ordinary schema-derived raw diagnostic.

Each wrapper contains one nonempty contiguous Error-token group, has exactly
that group's UTF-8 range, and contains no native trivia, Missing, Invalid,
accepted punctuation, accepted syntax subtree, returned Item or retry leading.
Leading still emitted by the outer owner remains outside; leading emitted as
part of the existing rejected Item remains Error content inside.

`ExpressionDelimitedSeparator` wraps exactly one existing Separator-role
lexical run, and each Parenthesized rejected semicolon Error item. Its existing
continuation resets to Item without inventing a Missing. Each consumed,
unprotected foreign close gets one
`ExpressionDelimitedForeignClose`; it preserves the existing sequence phase
and resumes the existing loop. Neither node is a terminal TypeCall-close node.

The XML-like notation is:

```xml
<ParenthesizedExpression><LParen text="("/><Error text="@"/><RParen text=")"/></ParenthesizedExpression>
<ParenthesizedExpression><LParen text="("/><ExpressionDelimitedSeparator><Error text=";"/></ExpressionDelimitedSeparator><RParen text=")"/></ParenthesizedExpression>
<ParenthesizedExpression><LParen text="("/><ExpressionDelimitedForeignClose><Error text="]"/></ExpressionDelimitedForeignClose><RParen text=")"/></ParenthesizedExpression>
```

## Alternatives not selected by this draft

- Wrapping only semicolon and foreign close leaves Item/Separator distinction
  dependent on reconstructing `Recovered`/newline phase from ambient context;
  that reconstruction is not proven complete.
- Owner-specific kinds duplicate information already supplied by immediate
  parent; one untyped shared wrapper cannot distinguish separator from close.
- Wrapping every Item Error adds topology without an ambiguity once the other
  two slots are explicit.
- Error spelling, parser provenance, expectation unions, synthetic Missing,
  a generic recovery state or `Invalid(Error+)` violate governing authority or
  change unrelated recovery semantics.

## Construction gate

The user approved both node names, all five owner contexts, the stated
one-wrapper cardinality and this narrow supersession of direct raw Error
placement on 2026-09-10. M2 construction, focused proof and scoped closure
review are complete. The append-only SyntaxKinds are
`ExpressionDelimitedSeparator = 276` and
`ExpressionDelimitedForeignClose = 277`; existing values are unchanged.
Required proof covers all owners and phases; repeated/mixed runs; semicolon;
accepted separators; retry; UTF-8/CRLF/comments/quote prefixes; spread RHS;
protected close/fence handoff; source flattening; exact wrapper range/order;
unchanged records/frozen replay; and accepted controls. No benchmark
samples/processes are planned unless a material cost uncertainty appears.

Stop if any raw role remains ambiguous, a wrapper changes source/leading/phase
continuation, accepted syntax gains a node, a sibling owner gains either node,
or correctness requires hidden parser provenance.
