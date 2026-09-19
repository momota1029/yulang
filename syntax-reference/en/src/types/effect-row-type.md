# Effect-row types

## 1. Authority and scope

This page defines `EffectRowType` in `syntax-v0`. The Authoritative effect-row
sections of the 2026-08-20 syntax architecture, the Parenthesized/EffectRow
current-Item recovery authority, and the type-delimited foreign-close topology
authority govern this page.

It covers adjacent apostrophe-bracket type primaries and their delimited items.
It does not define row-tail meaning, open or closed row classification, effect
inference, lowering, or diagnostic wording.

## 2. Accepted syntax

```text
EffectRowType := "'" adjacent "[" G* [ TypeExpression { EffectRowDelimiter TypeExpression } [ EffectRowDelimiter ] ] "]"
EffectRowDelimiter := comma | semicolon | qualifying newline
```

The apostrophe and `[` are adjacent. Opening trivia establishes the layout
base. An equal-or-shallower newline separates items; a deeper newline continues
the current item.

## 3. Admission and boundaries

After active stops, closes, and canonical NUD `for`, the primary judge probes
the complete adjacent `"'["` introducer before ordinary type names. `'e`
remains a sigil identifier; `' [` and `'/*c*/[e]` do not admit an effect row.

An accepted row owns its bracket delimiter, items, separators, layout, and
matching close. It then returns to the ordinary tail judge: `'[e]::Result`,
`Foo '[e]`, and `'[e] -> Out` are path, apply, and arrow composition.

## 4. Direct Rowan CST

`EffectRowType` contains apostrophe, brackets, trivia, literal separators, and
direct `TypeExpression` items in source order. It has no item-list, row-tail,
or open/closed-row wrapper. Newline separators remain trivia.

For a locally consumed mismatched close, `TypeDelimitedForeignClose` contains
only that maximal raw `Error` group. It is emitted only below
`EffectRowType` or `ParenthesizedTypeGroup`, adds no diagnostic, and contains
no trivia, `Missing`, accepted punctuation, retry source, or `Invalid`.

## 5. Recovery CST

An absent item, separator, or close uses a slot-local `Missing`; malformed
source in that slot is a raw `Error` group. A same-line next item that cannot
continue the current apply recovers a missing separator and retries the item.
A real trailing separator before `]` is valid and does not create an empty item.

A separator before EOF or a protected outer boundary keeps its missing item and
close slots distinct. A matching `]` is local; protected caller and outer
closes remain unconsumed. The locally consumed mismatched close is the sole
case using `TypeDelimitedForeignClose`.

## 6. Source/CST examples

`'[]` contains only the introducer and brackets. `'[e]` contains one direct
`TypeExpression` item.

`'[tick; 'effect]` has two items and a literal semicolon separator. The
semicolon is syntactic punctuation, not a row-tail interpretation.

`Foo '[e] -> Out` applies the effect-row primary to `Foo`; the completed result
then has an ordinary arrow tail.

## 7. Composition

[Standalone `TypeExpression` core](type-expression-core.md) defines each item
and the tail behavior after the row. The [syntax content
model](../conventions/syntax-content-model.md), [Rowan CST
notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md) define shared
`syntax-v0` conventions.
