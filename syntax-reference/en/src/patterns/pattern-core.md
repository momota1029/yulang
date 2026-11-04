# Pattern core and parenthesized patterns

## 1. syntax-v0 scope

This page fixes the syntax-v0 core Pattern forms: identifiers, integers, symbols, aliases, alternation, and parenthesized patterns.
List and record primaries are defined on their own pages.
The trailing type annotation is defined in [type annotations](type-annotation.md).

## 2. Grammar

```text
Pattern := Pattern@Lowest
ArmPattern := Pattern@Lowest with arm_application = true
Pattern@P := PatternPrimary { PatternTail(P) }
PatternTail(P) := G* PatternAliasTail if P <= Alias
                | G* PatternAlternationTail if P <= Alternation
                | G_same_line+ PatternMlApplicationTail
                    if arm_application and P < MlApplication
PatternMlApplicationTail := Pattern@MlApplication
PatternAliasTail := AsKw G+ Identifier
PatternAlternationTail := Pipe G* Pattern@Alternation
PatternPrimary := IdentifierPattern | IntegerPattern | SymbolPattern
                | ParenthesizedPattern | ListPattern | RecordPattern
                | RuleLiteral | StringLiteral | RuleExpression
IdentifierPattern := Identifier | SigilIdentifier
IntegerPattern := Integer
SymbolPattern := Colon!Identifier
ParenthesizedPattern := LParen OpeningTrivia [ Pattern { PatternSeparator Pattern } [ PatternSeparator ] ] RParen
PatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(pattern_base)
```

`G*` is one maximal contiguous source-trivia run, and `G+` is one nonempty maximal run.
`G_same_line+` is a nonempty trivia run with no ordinary newline.
`OpeningTrivia` is the `G*` immediately after a delimiter opener.
Each delimited Pattern snapshots its base after that opening trivia:

```text
pattern_base := if OpeningTrivia ends after a physical newline
                   and following_line_indentation > incoming_base
                then following_line_indentation
                else incoming_base
```

Later tokens and recovery positions do not recompute that base.

An adjacent `~"` routes a Pattern primary to `RuleLiteral`, using the same opener and multiline handling as the expression form.
A bare one-quote opener remains accepted and also routes to the existing `RuleLiteral` CST.
A quote run of three or more routes it to `StringLiteral`.
Pattern has no `NormalString` route.
`RuleExpression` retains its own CST and is also admitted as a Pattern primary.

## 3. Order and ownership

The core uses fixed Pattern precedence. `as` binds inside an alternation RHS, so `A | B as c` is an alternation whose RHS is the alias.
An outer type annotation is terminal and is considered only after the core tails have returned.

A contiguous `:identifier` is a SymbolPattern before an active caller colon is considered.
If that composite is absent, an active caller colon remains unconsumed.
The `as` keyword is contextual only in the alias-tail position.

In an `ArmPattern`, a bare `IdentifierPattern` head keeps `arm_application` for its same-line arguments.
Thus `just x`, `node value left right`, and `op x` add one `PatternMlApplicationTail` per argument.
Whether the identifier denotes a binding or a variant is decided by name resolution, not by the parser.
The parser does not admit `as`, `|`, `if`, `where`, `in`, `:`, `->`, `,`, a close delimiter, a newline, or end of input as such an argument boundary.

The Authoritative parser-gap design memo WP-9 supersedes the earlier R280 qualified-only application rule for arm patterns.
Qualified forms such as `opt::just x` retain their existing application shape.

After `(`, the parenthesized owner owns its comma and matching `)`.
An outer close is returned to its caller without consumption.

## 4. Direct Rowan CST

The lossless Rowan CST has one enclosing `Pattern` node.
Its primary is an `IdentifierPattern`, `IntegerPattern`, `SymbolPattern`, `ParenthesizedPattern`, `ListPattern`, `RecordPattern`, `RuleLiteral`, `StringLiteral`, or `RuleExpression`.
`SymbolPattern` contains its colon and adjacent identifier.

`PatternAliasTail` contains `AsKw` and its binding identifier.
`PatternAlternationTail` contains `Pipe` and the recursive RHS `Pattern`.
`PatternMlApplicationTail` contains one argument `Pattern`; the separating source trivia remains direct content of the enclosing `Pattern`.
`ParenthesizedPattern` contains its `LParen`, child Patterns, source commas and trivia, and its `RParen`.
Qualifying newline separation remains source trivia between children; the CST creates no synthetic separator node.

## 5. Recovery topology

An absent primary creates one zero-width `Missing` in the immediate primary slot.
A malformed primary creates one nonempty raw `Error` for the maximal malformed run, then retries a valid primary in the same slot.
Leading trivia of the retry is outside that Error and remains direct Pattern content.

After a committed symbol colon, an absent adjacent name creates one `Missing` in `SymbolPattern`; it does not scan or create an Error.
After `as`, an absent binding creates one `Missing` in `PatternAliasTail`.
After `|`, an absent RHS creates one `Missing` in `PatternAlternationTail`.
When a raw Error reaches a boundary, recovery returns that boundary without a second, same-cause Missing.

## 6. Layout and caller boundaries

The parenthesized base is captured after `(`.
A newline whose following indentation is at most that base separates items; a deeper newline remains with the current Pattern.
An implicit newline is valid source trivia, not a missing comma.

A same-line adjacent item creates one zero-width missing separator and retries at that item.
Matching local close wins before caller-close handling.
Caller boundaries, fences, and protected outer closes remain unconsumed.

## 7. Limits and related pages

This page does not assign binding meaning, constructor meaning, exhaustiveness, resolution, typing, or lowering to a Pattern.
It also does not define list, record, literal, or type syntax beyond their Pattern entry points.

The governing syntax-v0 recovery sources are the Pattern primary, delimited-slot, and sequence recovery decisions.
For contained forms, see [list patterns](list-pattern.md), [record patterns](record-pattern.md), and [type annotations](type-annotation.md).
