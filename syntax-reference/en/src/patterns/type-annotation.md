# Pattern type annotations

## 1. syntax-v0 scope

A Pattern type annotation is one optional, terminal `: TypeExpression` suffix on a complete Pattern.
It is available wherever a canonical Pattern is accepted, including binding targets, case and catch patterns, and nested patterns.
This page defines syntax-v0 parsing and direct Rowan CST recovery only.

## 2. Grammar

```text
Pattern := Pattern@Lowest
Pattern@P := PatternPrimary { ExistingAliasOrAlternationTail } [ PatternTypeAnnotation if P <= TypeAnnotation ]
PatternTypeAnnotation := Gpta Colon Gpta RequiredTypeExpression(Pattern::TypeAnnotation)
```

`Gpta` is the `G*` maximal trivia run defined in [Pattern core](pattern-core.md).
It may contain no physical newline, or a physical newline whose indentation after the last newline is greater than the continuation base captured when the enclosing Pattern starts.
An equal-or-shallower newline rolls back the complete run.

The type expression is required after an accepted colon.
The annotation itself is optional and terminal.

## 3. Order and ownership

Type annotation has lower precedence than alternation and alias.
Therefore, `A | B as c: Int` annotates the whole alternation.
After one annotation is accepted, the same Pattern does not consider another alias, alternation, or annotation.

An active caller colon wins over annotation recognition, and `::` is not an annotation colon.
For a record field, the first same-line colon belongs to `RecordPatternField` before its nested Pattern starts.
Thus, `{a: A}` has a field colon, while `{a: A} : SomeType` annotates the outer Pattern.

## 4. Direct Rowan CST

The lossless Rowan CST puts `PatternTypeAnnotation` at the end of its enclosing `Pattern`.
The node contains the accepted colon, post-colon trivia, and the required `TypeExpression` entry in source order.
Accepted pre-colon trivia remains a direct child of `Pattern`.
No synthetic colon, separator, or stop token is created.

In the following source, the first colon belongs to the record field and the second belongs to the outer annotation.

```text
{a: A} : SomeType
```

The annotation node contains the second colon, its following space, and `TypeExpression(SomeType)`.

## 5. Recovery topology

Once the colon is accepted, the required type entry has these outcomes.

| input after the colon | direct CST result | ownership and continuation |
| --- | --- | --- |
| valid type primary | `PatternTypeAnnotation > TypeExpression` | The type expression completes. |
| EOF, active stop, close, comma, semicolon, or equal-or-shallower newline | zero-width `Missing(Pattern::TypeAnnotation, TypeExpression)` in an empty `TypeExpression` | The boundary remains unconsumed for its owner. |
| malformed run followed by a valid type primary | one nonempty `Error(Type::Primary, TypeExpression)`, then `TypeExpression` | The required slot retries at that primary. |
| malformed run followed by a boundary | one nonempty `Error(Type::Primary, TypeExpression)` | Recovery returns the boundary and adds no same-cause Missing. |

For example, `my y: = 1` has a zero-width required-type Missing before `=`.
The `=` remains owned by the binding header.

## 6. Caller boundaries and multiline recovery

The annotation enters the existing required `TypeExpression` parser without changing caller stops, delimiter state, or indentation state.
Binding targets leave `=` to the binding owner.
Case and catch patterns leave guards and `->` to the arm owner.
The first catch pattern also leaves its handler comma to the catch owner.
Delimited patterns leave their local comma and matching close to their delimiter owner.

For malformed type recovery, the `TMN` classifier examines one maximal trivia run after the error.
An active caller newline takes priority over indentation and retry candidates.
That `TMN-CallerBoundary` result creates a rollback-scoped positional fence at the untouched trivia start.
The type parser and enclosing type owners do not consume the fenced trivia or its following caller boundary.
No other `TMN` result creates a fence.
Other multiline outcomes use the Pattern base snapshot: only a deeper newline can remain in the same required type slot.

## 7. Limits and related pages

This form does not define annotation meaning, type checking, pattern lowering, constructor or ML pattern tails, diagnostics wording, or formatting.
It does not add a separate type grammar; the RHS is the existing `TypeExpression` entry.

See [Pattern core](pattern-core.md) for aliases and alternation, and [record patterns](record-pattern.md) for field-colon ownership.
