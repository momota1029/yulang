# Summary

- [Introduction](index.md)
- [Syntax content model](conventions/syntax-content-model.md)
- [CST conventions](conventions/index.md)
  - [Rowan CST notation](conventions/rowan-cst.md)
  - [Recovery `Error` and `Invalid` topology](conventions/recovery-error-invalid-topology.md)
  - [Source root, headers, and diagnostic ownership](conventions/source-root-and-diagnostics.md)

# Expressions

- [Expression placement overview](expressions/index.md)
- [Parenthesized primary forms](expressions/parenthesized-expression.md)
- [Operator-chain expression form](expressions/operator-chain.md)
- [Assignment terminal form](expressions/assignment-tail.md)
- [Colon-application terminal form](expressions/colon-application.md)
- [`if` / `elsif` / `else` primary form](expressions/if-expression.md)
- [Braced statement-block primary form](expressions/braced-statement-block.md)
- [`case` / `catch` primary forms](expressions/case-catch.md)
- [Call, field, path, and ML continuation forms](expressions/call-field-path-tails.md)
- [Index and projection continuation forms](expressions/index-projection-tails.md)
- [`with` body terminal form](expressions/with-body-tail.md)

# Patterns

- [Pattern placement overview](patterns/index.md)
- [Core and parenthesized pattern forms](patterns/pattern-core.md)
- [List-pattern primary form](patterns/list-pattern.md)
- [Record-pattern primary form](patterns/record-pattern.md)
- [Trailing pattern type-annotation form](patterns/type-annotation.md)

# Types

- [TypeExpression placement overview](types/index.md)
- [Core TypeExpression form](types/type-expression-core.md)
- [Named-record type primary form](types/named-record-type.md)
- [`forall` TypeExpression form](types/forall-type.md)
- [Effect-row type primary form](types/effect-row-type.md)
- [Polymorphic-variant type primary form](types/polymorphic-variant-type.md)
- [Bracket-row TypeExpression and TypeArrowTail forms](types/bracket-row-grammar.md)

# Statements / Declarations

- [Statement and declaration placement overview](statements/index.md)
- [Bare nominal `type` declaration form](statements/bare-nominal-type.md)
- [Equality `type` declaration form](statements/equality-type.md)
- [Binding and use statement forms](statements/binding-use.md)
- [`mod` declaration form](statements/mod-declaration.md)
- [`struct` declaration form](statements/struct-declaration.md)
- [`derives` declaration-attachment form](statements/derives-attachment.md)
- [Standalone `impl` declaration form](statements/impl-shell.md)
- [Standalone `cast` declaration form](statements/cast-declaration.md)

# Cross-cutting mechanisms

- [Overview](cross-cutting/index.md)
- [Layout-aware separator authority](cross-cutting/layout-aware-separator-authority.md)
- [TypeExpression malformed-newline-owner policy (TMN)](cross-cutting/tmn-malformed-newline-owner-policy.md)
- [TypeExpression malformed caller-boundary positional fence](cross-cutting/positional-fence.md)
- [Ambient statement-owner boundary (ASOB)](cross-cutting/ambient-statement-owner-boundary.md)
- [ASOB integration matrix](cross-cutting/asob-integration-matrix.md)

# Index

- [Reference index](indexes/index.md)
