# Postfix `if`

Status: Authoritative (approved 2026-11-08 by the language owner for the semantics; the CST shape below is the implementer's proposal)

**Implementation status:** statement, binding-body and delimited-item owners construct the proposed node; condition parsing uses the existing required-expression parser. Chaining, inline body handoff, delimiters, prefix forms and recovery are covered by tests in `tests::statement`. Outer recovery records invalid `else`, `:` and `{` after a guard as non-empty `Error` groups.

The semantic authority is `spec/03-expressions.md` §3.6, 後置 `if`. This addendum specifies parser ownership only.

```text
PostfixIf := Expression "if" Condition
```

The keyword follows the expression on the same logical line. The condition ends at a statement boundary, closing delimiter, or EOF. The postfix form has the weakest binding: it wraps the whole preceding expression, including a pipeline or inline-colon body. Parentheses admit a nested postfix form. A complete prefix `if` remains a prefix expression; a postfix form has no `else`. Chaining associates to the left: `a if b if c` is `(a if b) if c`.

Proposed CST: `PostfixIfExpression(operand, IfKw, Condition(OperatorChain))`, with source-order trivia retained. The operand is the complete existing expression or `ForStatement`; nested `PostfixIfExpression` nodes represent chaining. No lowering or typing occurs in this crate.

A missing condition in `x if` produces a zero-width `Missing` in `Condition` and preserves the boundary for its owner. A colon after a postfix-looking condition, as in `x if c:`, is diagnosed as an invalid postfix introducer and left to the surrounding recovery; it must not become an else arm. Recovery preserves subsequent statement and delimiter ownership.

Expected trees (omitting trivia and existing internal nodes):

```text
say: 1 + 2 + 3 if 6 < 7   PostfixIfExpression(OperatorChain(say, ColonApplicationTail(1 + 2 + 3)), Condition(6 < 7))
x | f if c                  PostfixIfExpression(OperatorChain(x | f), Condition(c))
for x in xs: last if done   PostfixIfExpression(ForStatement(for x in xs: last), Condition(done))
return x if c               PostfixIfExpression(OperatorChain(return x), Condition(c))
last 'outer if done         PostfixIfExpression(OperatorChain(last 'outer), Condition(done))
next if skip                PostfixIfExpression(OperatorChain(next), Condition(skip))
(x if c)                    ParenthesizedExpression(PostfixIfExpression(OperatorChain(x), Condition(c)))
a if b if c                 PostfixIfExpression(PostfixIfExpression(OperatorChain(a), Condition(b)), Condition(c))
```
