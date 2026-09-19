# List patterns

## 1. syntax-v0 scope

A ListPattern is the bracketed Pattern primary.
It accepts ordinary Pattern items and spread items, including empty and trailing-separator forms.
This page defines syntax and recovery topology, not spread matching or capture semantics.

## 2. Grammar

```text
ListPattern := LBracket OpeningTrivia [ ListPatternItem { ListPatternSeparator ListPatternItem } [ ListPatternSeparator ] ] RBracket
ListPatternItem := Pattern@Lowest | ListPatternSpreadItem
ListPatternSpreadItem := DotDot G* Pattern@Lowest
ListPatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(list_pattern_base)
```

`..tail` and `.. tail` are spread items.
`...` and `..+` are not split into `DotDot` plus another token.
Semicolon is not a ListPattern separator.
`OpeningTrivia` and the base snapshot use the definitions in [Pattern core](pattern-core.md).

## 3. Item and delimiter ownership

After `[`, the ListPattern owns its comma and matching `]`.
The item judge recognizes the matching close, then exact `DotDot`, then an ordinary Pattern primary.
An outer close returns without consumption.

The spread marker belongs to `ListPatternSpreadItem` even when its RHS is incomplete.
Nested Pattern recovery retains its own owner nodes and is not relabeled as list recovery.

## 4. Direct Rowan CST

The direct Rowan CST places `ListPattern` below its enclosing `Pattern`.
It contains `LBracket`, `RBracket`, source commas and trivia, ordinary child `Pattern` nodes, and `ListPatternSpreadItem` nodes.
Each spread node contains `DotDot` and its RHS Pattern.

A qualifying newline remains source trivia between list children.
The CST does not create a separator node for that newline or for a source-absent separator.

## 5. Recovery topology

An absent ordinary item creates one zero-width `Missing` in the list-item slot.
An absent spread RHS creates one `Missing` inside its existing `ListPatternSpreadItem`.
The comma or close remains list-owned.

A same-line adjacent next item creates one zero-width missing separator and retries at that item.
A malformed ordinary item creates one nonempty raw `Error` for its maximal lexical run, then retries at a valid item.
A malformed separator or unclaimed wrong close is one raw `Error` in the sequence phase that owns it.
Recovery stops before a comma, close, caller boundary, fence, or valid retry item and does not add a second same-cause Missing.

## 6. Layout and caller boundaries

The list base is captured after `[`.
A following indentation at or below that base makes a newline an item boundary; deeper indentation remains with the current item.
An explicit comma wins over a qualifying newline in the same boundary cluster.

Matching `]` wins before caller-close handling.
At a caller boundary or fence, the pending trivia and boundary remain unconsumed for the caller.

## 7. Limits and related pages

ListPattern does not impose spread count, position, matching, binding, typing, or lowering rules.
It does not define expression list syntax.

The governing syntax-v0 recovery sources are the Pattern delimited-slot and sequence decisions.
See [Pattern core](pattern-core.md) for shared Pattern behavior and [record patterns](record-pattern.md) for the brace-delimited form.
