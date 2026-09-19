# Record patterns

## 1. syntax-v0 scope

A RecordPattern is the brace-delimited Pattern primary for name-headed fields and spreads.
It includes shorthand fields, nested-pattern fields, defaults, empty forms, and trailing separators.
This page fixes syntax and direct CST recovery topology only.

## 2. Grammar

```text
RecordPattern := LBrace OpeningTrivia [ RecordPatternItem { RecordPatternSeparator RecordPatternItem } [ RecordPatternSeparator ] ] RBrace
RecordPatternItem := RecordPatternField | RecordPatternSpreadItem
RecordPatternField := PatternFieldName [ G0 Colon G* Pattern@Lowest [ G0 Equals G* OperatorChain ] | G0 Equals G* OperatorChain ]
PatternFieldName := Identifier | SigilIdentifier
RecordPatternSpreadItem := DotDot G* Pattern@Lowest
RecordPatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(record_pattern_base)
```

`G0` has no physical newline.
`==`, `=>`, and `=+` are not split to form a default marker.
Semicolon is not a RecordPattern separator.
`OpeningTrivia` and the base snapshot use the definitions in [Pattern core](pattern-core.md).

## 3. Field and delimiter ownership

After a field name, the first same-line `:` is owned by `RecordPatternField` before nested Pattern parsing begins.
The first same-line exact `=` starts that field's default.
Otherwise the field is shorthand.

The RecordPattern owns its comma and matching `}`.
Its nested Pattern and default expression stop at the local comma or close.
An outer close is returned without consumption.

## 4. Direct Rowan CST

The direct Rowan CST places `RecordPattern` below its enclosing `Pattern`.
It contains `LBrace`, `RBrace`, source commas and trivia, `RecordPatternField`, and `RecordPatternSpreadItem` nodes.
A spread node contains `DotDot` and its RHS Pattern.
A default field retains `Equals` and contains its `OperatorChain`.

Record wrong-kind pattern recovery is structured as `Invalid(Pattern(...))`.
An item-phase Invalid is a direct `RecordPattern` child.
A separator-phase Invalid is wrapped once by `RecordPatternSeparator`.
These nodes preserve the phase without adding a diagnostic-bearing wrapper.

## 5. Recovery topology

An absent item, nested Pattern, spread RHS, separator, or close creates one zero-width `Missing` in its immediate slot.
An accepted `=` with no expression creates an empty `OperatorChain` containing that default-expression `Missing`.
The marker remains field-owned.

Ordinary malformed item and separator runs are maximal nonempty raw `Error` children in their ordered sequence context.
A consumed foreign close is different: each occurrence is wrapped once by `RecordPatternForeignClose`, whose only source-bearing child is the raw `Error` for that close.
It does not wrap ordinary item or separator Errors, accepted local closes, Invalid nodes, or retry content.

Recovery stops before a comma, close, caller boundary, fence, or valid retry candidate.
It does not add a second same-cause Missing.

## 6. Layout and caller boundaries

The record base is captured after `{`.
A following indentation at or below that base separates fields; deeper indentation remains with the current field.
An implicit newline is source trivia and creates no separator node.

Matching `}` wins before caller-close handling.
At a caller boundary or fence, pending trivia and the boundary remain unconsumed for the caller.
The local `}` still wins over a same-kind caller close.

## 7. Limits and related pages

RecordPattern does not validate duplicate names, spread placement, matching, capture, types, or lowering.
It does not define record expression or record type syntax.

The governing syntax-v0 recovery sources are the Pattern delimited-slot, sequence, default-expression, and RecordPattern foreign-close decisions.
See [Pattern core](pattern-core.md) for shared behavior, [list patterns](list-pattern.md) for the bracketed form, and [type annotations](type-annotation.md) for outer annotations.
