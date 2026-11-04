# Expressions

The [syntax content model](../conventions/syntax-content-model.md) identifies the expression contexts and all recorded expression families. The pages below define the placement and production of the documented forms.

## Identifier primary forms

An `IdentifierExpression` records a plain identifier, a reference sigil identifier, or a label identifier in operand position.

```text
IdentifierPrimary := Identifier | ReferenceSigilIdentifier | LabelIdentifier
ReferenceSigilIdentifier := ("$" | "&") ! Identifier
LabelIdentifier := "'" ! Identifier
```

`!` requires the sigil and identifier to be adjacent, with no trivia between them.
The direct CST is `IdentifierExpression` with one `Identifier` or `SigilIdentifier` token.
When LED operator selection applies after an operand, a declared `&` remains an operator candidate rather than starting a sigil identifier.
A bare sigil or a sigil not adjacent to an identifier is not an identifier primary.

```yulang
$count
&count = $count + 1
last 'outer
'done.return 42
```

- [Parenthesized primary forms](parenthesized-expression.md)
- [List-expression primary form](list-expression.md)
- [Lambda-expression primary form](lambda-expression.md)
- [Numeric literal primary forms](numeric-literals.md)
- [Operator-chain expression form](operator-chain.md)
- [Assignment terminal form](assignment-tail.md)
- [Colon-application terminal form](colon-application.md)
- [`if` / `elsif` / `else` primary form](if-expression.md)
- [Braced statement-block primary form](braced-statement-block.md)
- [`case` / `catch` primary forms](case-catch.md)
- [Call, field, path, and ML continuation forms](call-field-path-tails.md)
- [Index and projection continuation forms](index-projection-tails.md)
- [`with` body terminal form](with-body-tail.md)
