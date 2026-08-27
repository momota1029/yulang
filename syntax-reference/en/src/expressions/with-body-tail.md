# `WithBodyTail`

## 1. Status, authority, and last verification

The Authoritative generic-expression `WithBodyTail` addendum is lines 10662–11085 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. It fills the terminal-tail slot reserved by the operator-chain and colon-application work; it is one addendum rather than a declaration-companion addendum.

The approval and implementation commits are `72922125` and `5ca66006`. Later canonical-`Statement` expansion is shared consumer infrastructure, not a second `WithBodyTail` grammar.

## 2. Scope and non-scope

This grammar adds a terminal generic-expression continuation after an operand-complete `OperatorChain`: an inline one-`Statement` body or a non-empty strictly-indented statement block. Its body is a nested canonical statement, so ordinary nested operator tails, colon application, and another `WithBodyTail` can occur inside that body.

It does not define a `struct`, `enum`, `type`, or other declaration companion; `with { ... }` is not this generic form. It also does not decide companion/module semantics, receiver attachment, cleanup meaning, target association, HIR/lowering, inference, diagnostics prose, or formatting.

## 3. BNF-equivalent grammar

```text
WithBodyContinuation :=
    ChainContinuingTrivia WithBodyTail

WithBodyTail :=
    WithKw WithIntroducerTrivia Colon WithBody

WithIntroducerTrivia := G*

WithBody :=
    InlineWithBody
  | IndentedStatementBlock

InlineWithBody :=
    G0* Statement [ Semicolon ]
```

`with` is an exact maximal word; `withx` and `with?` are not split. `::` is not split into the required lone `:`. The introducer allows maximal trivia, including newlines, between the keyword and colon. `ChainContinuingTrivia` belongs to the outer chain, while post-keyword and inline post-colon trivia belong to the tail.

## 4. Judge, priority, and owner boundary

At an operand-complete site, active owner stops, matching delimiters, and equal-or-shallower newlines first return to their owners. With `StopKind::With` inactive, an exact `with` probe then precedes dynamic LED recognition, fixed postfix recognition, ML-argument recognition, and colon-application recognition. Once the word is accepted, the tail owns mandatory colon/body recovery and cannot roll back to an identifier, dynamic operator, or ML argument.

`WithBodyTail` is a `TerminalOuterTail`: it has no target child and finishes the current outer chain. Its nested body owns a fresh statement/chain, so `a with: b: c` and `a with: b with: c` put the inner terminal continuation in the body rather than adding a second terminal sibling to outer `a`. A later fixed tail therefore needs a new outer chain, for example through parenthesization.

## 5. Byte-exact CST worked examples

The addendum supplies source-order CST trees but no byte-range-annotated tree; no ranges are invented here.

```text
a + b with: cleanup
```

Design lines 10769–10783 give the complete tree: the outer `OperatorChain` owns `a`, `+`, and `b`; the following `WithBodyTail` owns `WithKw`, colon, post-colon trivia, and a nested `Statement` whose `OperatorChain` owns `cleanup`.

```text
value with: body
```

Design line 10962 records the complete inline-body recovery-table row: one `WithBodyTail`, a completed colon slot, and a completed inline `Statement`, with no diagnostic.

```text
a with: b: c
```

Design lines 10988–10996 fix the nested ownership: `WithBodyTail` is outer-tail syntax, while the body statement's nested `OperatorChain` owns `b` and its `ColonApplicationTail`.

```text
f with: body
```

Design lines 11002–11004 fix exact `with` priority over ML application: this is a with-tail whose target segment is `f`, not `Primary(f), MlArgument(with), ColonApplicationTail(body)`.

The documented indented complete form is `value with:\n  body` at design line 10963; it has one `IndentedStatementBlock`, including its opening trivia and nested statement, rather than an inline wrapper.

## 6. Parser-side AST shape

`TerminalOuterTail` has exactly `ColonApplication(ColonApplicationTail)` and `WithBody(WithBodyTail)` variants in this portion of the grammar. `WithBodyTail` has exactly `keyword: WordSpan<'source>`, `colon: Recovered<Range<usize>>`, `body: Recovered<WithBody<'source>>`, and `range: Range<usize>`.

`WithBody` has exactly `Inline { statement: Box<Statement<'source>> }` and `Indented { block: IndentedStatementBlock<'source> }` variants. There is no target field, numeric binding-power field, inline-semicolon field, or trivia field: those remain CST/source ownership. Keeping `colon` and `body` as separate recovered slots distinguishes missing-colon retry from a present colon with a missing body.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| `value with` at EOF | retain `WithKw`; emit one zero-width `Missing(Introducer: Colon)` and no cascaded body Missing |
| `value with body` | emit one zero-width introducer-colon Missing, then retry the same position as the inline statement body |
| `value with :: body` | do not split `::`; retain longer punctuation for body/outer recovery after the colon Missing |
| `value with:` at EOF | retain colon and emit one zero-width `Missing(Body: Statement)` |
| post-colon newline at indent `<= with_base` | emit one body Missing; leave newline and following token for the outer statement owner |
| deeper newline then EOF | retain `IndentedStatementBlock` and its opening trivia; emit one `Missing(IndentedStatement)` |
| `value with: ;` | emit one body Missing and retain the literal terminal semicolon |
| malformed non-statement run before a valid body | emit one maximal non-empty `Error(Body)`, then retry the same body slot |
| malformed inner indented statement or nested tail | delegate to the nested/shared owner without a duplicate With recovery |

`Missing` is zero-width, `Error` is maximal and non-empty, and each committed recovery node has one diagnostic identity. Comma, matching close, dedent, equal-or-shallower newline, active owner stops, EOF, and valid retry points remain scanner boundaries.

## 8. Boundary and state-restoration contract

The tail snapshots the active indentation baseline before its introducer/layout episode. No physical post-colon newline selects exactly one canonical inline `Statement`; a newline selects an indented block only when the following indent is strictly deeper. Inline terminal semicolon is owned once by the tail, while subsequent trivia and outer boundaries remain outside it.

AST and direct-CST paths restore input, line state, sink, ambient-owner scope, stop set, indentation state, `ml_arg`, and other local parser frames on normal, recovery, and rollback exits. Nested body recovery leaves outer comma, matching close, dedent, and owner boundaries available to their callers.

## 9. Yulang2 divergences

Yulang3 renames Yulang2 `WithBlock` to `WithBodyTail`, making the flat-chain terminal role explicit. It replaces empty/generic invalid-token recovery with typed `WithBodyRole` Missing/Error records and a same-position missing-colon body retry. It also distributes trivia to the nearest typed CST owner rather than reproducing a single Yulang2 `Lex` emission.

The original Yulang3 slice deliberately excluded Yulang2 declaration-companion/brace paths and, until shared canonical `Statement` expansion, accepted only the then-current statement subset inside the body. The generic tail never infers a declaration companion owner from its target.

## 10. Known residual / deferred surface

The shared `ASOB-G` caller-boundary residual remains characterized rather than hidden: a caller boundary behind a missing nested delimited owner can be unavailable to that nested owner's recovery scan. This page neither broadens nor resolves that cross-cutting residual.

Deferred surfaces include declaration companions and brace companion bodies, companion item classification, name resolution/visibility, receiver or method attachment, cleanup/local-module interpretation, HIR/lowering, inference, diagnostics wording, and formatting.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/expression.rs`: `recognize_with_body_tail`, `parse_with_body_tail`, `parse_with_inline_statement`, `commit_with_body_tail`, `with_body_absent_boundary`, `with_body_error_retry`, `emit_with_missing`, and `emit_with_error`.

Fixtures include `with_body_tail_is_terminal_and_reuses_inline_and_indented_statement_bodies`, `with_body_tail_missing_colon_is_single_typed_recovery_and_retries_body`, and `indented_and_with_inline_ambient_scopes_restore_after_ast_and_direct_episodes`.
