# Bracket-row grammar

## 1. Authority and scope

This page defines `BracketRow` in `syntax-v0`. The Authoritative bracket-row
sections of the 2026-08-20 syntax architecture, the leading-row-head and
bracket-arrow current-Item recovery authorities, and the bracket-row recovery
authority govern this page.

It covers a leading row before a required ordinary type head and a trailing row
before a required arrow. It does not define an effectful-type wrapper, row-tail
meaning, effect inference, lowering, or diagnostic wording.

## 2. Accepted syntax

```text
TypeExpression := [ LeadingBracketRow TypeChainTrivia ] TypePrimary { TypeTightTail | TypeApplyArgument } [ TypeArrowTail ]
LeadingBracketRow := BracketRow
TypeArrowTail := [ BracketRow TypeChainTrivia ] "->" TypeChainTrivia TypeExpression
BracketRow := "[" G* [ TypeExpression { BracketRowDelimiter TypeExpression } [ BracketRowDelimiter ] ] "]"
BracketRowDelimiter := comma | semicolon | qualifying newline
```

The head after a leading row and the arrow after a trailing row are mandatory
recoverable slots. `TypeChainTrivia` permits empty, same-line, or deeper
continuation trivia, but not an equal-or-shallower newline.

## 3. Admission and boundaries

In a fresh type slot, `[` admits a leading row after active boundary checks and
contextual or compound type starters, but before ordinary primary candidates.
After one leading row is accepted, a second row is recovered as a malformed
required head rather than parsed recursively.

After a completed operand, the tail judge gives `[` bracket-arrow authority
before TypeApply. `T [e] -> U` is a trailing-row arrow. `F [e] T` is a
malformed bracket-arrow tail, while `F ([e] T)` is an explicit apply argument.
Row items and the matching `]` are local; caller stops and outer closes remain
unconsumed.

## 4. Direct Rowan CST

`BracketRow` contains brackets, trivia, literal separators, and direct
`TypeExpression` items in source order. In the leading form it is the first
source-bearing child of `TypeExpression`. In the trailing form it is the first
child of `TypeArrowTail`, before the arrow token. No effectful-type, effect
arrow, list, or synthetic separator node is added.

## 5. Recovery CST

A leading row without a head recovers the existing primary slot with
`LeadingEffectTypeHead`. A trailing row without an arrow but with an RHS
candidate recovers `BracketRowArrow` and retries the RHS at the same position.
At EOF, an outer boundary, or a newline it emits only the missing arrow, not a
cascading RHS missing slot.

Malformed row items use the shared delimited item and separator slots. A
missing or mismatched `]` is close recovery and does not consume an actual
outer close. A second leading row is one delimiter-aware raw error over that
balanced row before retrying the original head.

## 6. Source/CST examples

`[e] T` has `BracketRow` as the first source-bearing `TypeExpression` child,
followed by the ordinary head `T`.

`T [e] -> U` has `BracketRow` as the first `TypeArrowTail` child; the whitespace
before the tail stays with the enclosing `TypeExpression`.

`T [:] -> U` recovers `:` as one malformed row item and still admits the arrow
and RHS. In `[e][f]T`, only the first row is a `BracketRow`; the balanced second
row is the malformed required head.

## 7. Composition

[Standalone `TypeExpression` core](type-expression-core.md) defines the
ordinary head, RHS, and surrounding tails. The [syntax content
model](../conventions/syntax-content-model.md), [Rowan CST
notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md) define shared
`syntax-v0` conventions.
