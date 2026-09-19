# Summary

- [はじめに](index.md)
- [構文の内容モデル](conventions/syntax-content-model.md)
- [CST共通規約](conventions/index.md)
  - [Rowan CST表記](conventions/rowan-cst.md)
  - [回復の`Error` tokenと`Invalid` nodeのtopology](conventions/recovery-error-invalid-topology.md)
  - [Source root、header、diagnosticの責務](conventions/source-root-and-diagnostics.md)

# Expressions

- [Expressionの配置一覧](expressions/index.md)
- [Parenthesized primary form](expressions/parenthesized-expression.md)
- [Operator-chainによる式](expressions/operator-chain.md)
- [Assignmentのterminal form](expressions/assignment-tail.md)
- [Colon applicationのterminal form](expressions/colon-application.md)
- [`if` / `elsif` / `else`のprimary form](expressions/if-expression.md)
- [Braceで囲むstatement blockのprimary form](expressions/braced-statement-block.md)
- [`case` / `catch`のprimary form](expressions/case-catch.md)
- [Call、field、path、ML-applicationのcontinuation form](expressions/call-field-path-tails.md)
- [Index、projectionのcontinuation form](expressions/index-projection-tails.md)
- [`with` bodyのterminal form](expressions/with-body-tail.md)

# Patterns

- [Patternの配置一覧](patterns/index.md)
- [Coreとparenthesized patternの形式](patterns/pattern-core.md)
- [List-pattern primary form](patterns/list-pattern.md)
- [Record-pattern primary form](patterns/record-pattern.md)
- [末尾のPattern型注釈](patterns/type-annotation.md)

# Types

- [TypeExpressionの配置一覧](types/index.md)
- [Core TypeExpression form](types/type-expression-core.md)
- [Named-record type primary form](types/named-record-type.md)
- [`forall` TypeExpression form](types/forall-type.md)
- [Effect-row type primary form](types/effect-row-type.md)
- [Polymorphic-variant type primary form](types/polymorphic-variant-type.md)
- [Bracket-rowのTypeExpressionおよびTypeArrowTail形式](types/bracket-row-grammar.md)

# Statements / Declarations

- [Statementとdeclarationの配置一覧](statements/index.md)
- [Bare nominal `type` declaration form](statements/bare-nominal-type.md)
- [Equality `type` declaration form](statements/equality-type.md)
- [Bindingとuseのstatement form](statements/binding-use.md)
- [`mod` declaration form](statements/mod-declaration.md)
- [`struct` declaration form](statements/struct-declaration.md)
- [`derives`のdeclaration-attachment form](statements/derives-attachment.md)
- [Standalone `impl` declaration form](statements/impl-shell.md)
- [Standalone `cast` declaration form](statements/cast-declaration.md)

# Cross-cutting mechanisms

- [一覧](cross-cutting/index.md)
- [Layout-aware separator authority](cross-cutting/layout-aware-separator-authority.md)
- [TypeExpression malformed-newline-owner policy (TMN)](cross-cutting/tmn-malformed-newline-owner-policy.md)
- [TypeExpression malformed caller-boundary positional fence](cross-cutting/positional-fence.md)
- [Ambient statement-owner boundary (ASOB)](cross-cutting/ambient-statement-owner-boundary.md)
- [ASOB integration matrix](cross-cutting/asob-integration-matrix.md)

# 索引

- [リファレンス索引](indexes/index.md)
