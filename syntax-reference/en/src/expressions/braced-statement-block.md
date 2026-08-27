# Brace-delimited statement block

## 1. Status, authority, and last verification

The Authoritative NUD-primary brace-delimited statement-block addendum is lines 6067–6627 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. The closing signature records Claude review and user approval.

The design and implementation commits are `04ebde8e`, `2c9a77b8`, and `9f0d9d88`. The implementation introduced the closed shared statement-sequence policy used by braced primary blocks and indented blocks without merging their outer ownership.

## 2. Scope and non-scope

At an operand-required NUD site, `{ ... }` is `BracedStatementBlockExpression`: zero or more canonical Statements enclosed by braces. It is one primary in a surrounding flat `OperatorChain` and permits comma, semicolon, or returned physical-newline statement separators, including all three trailing forms.

It does not define a record literal/field node, brace bodies for `if` or declarations, projection records, fixed brace-local spread items, rule/use/interpolation braces, `CatchBlock`, HIR block/record interpretation, inference, diagnostics wording, or formatting.

## 3. BNF-equivalent grammar

```text
BracedStatementBlockExpression :=
    LBrace OpeningTrivia
    [ Statement { BraceStatementSeparator Statement } [ BraceStatementSeparator ] ]
    ClosingTrivia RBrace

BraceStatementSeparator := G0 Comma G* | G0 Semicolon G* | Gnl
OpeningTrivia := G*
ClosingTrivia := G0
```

`Gnl` is only trivia returned after a completed current-depth Statement. A deeper continuation newline remains within that Statement. The block is empty-valid; a separator in the optional final position does not create an empty Statement.

## 4. Judge, priority, and owner boundary

The sink-free NUD judge accepts only a lone fixed `{`, then cuts and owns the total block continuation. It pushes `Delimiter::Brace`, local `Comma`/`Semicolon`/`RightBrace` stops, bracketed inline mode, and a braced ambient-owner barrier; outer condition, comma, and close stops are suspended until this scope exits.

The brace owner recognizes its matching `}` before a statement slot and after a separator. It alone owns statement separators and close recovery. In `{x: 1, y: 2}`, the brace-owned comma stops each ordinary `ColonApplicationTail` after one RHS; the parser creates neither `RecordLiteral` nor `RecordField`.

## 5. Byte-exact CST worked examples

The addendum gives source-order CST trees but no byte-range-annotated tree; no ranges are invented here.

```text
{}
```

Design lines 6219 and 6495 record the valid empty block: `LBrace`, opening/closing trivia if present, and `RBrace`, with no synthetic Statement, separator, or Missing node.

```text
{x,y}
```

Design lines 6220–6222 and 6561–6563 record two `Statement > OperatorChain` children separated by one comma `BlockStatementSeparator`.

```text
{x,}
```

Design lines 6224 and 6499 record a valid trailing comma separator with one Statement and no `Missing(statement)`.

```text
{x: 1, y: 2}
```

Design lines 6116, 6259, and 6536 fix the outer `BracedStatementBlockExpression`: its comma is a block separator, while both inner Statements end in ordinary one-argument `ColonApplicationTail` nodes.

## 6. Parser-side AST shape

`PrimaryExpression::BracedStatementBlock` contains `BracedStatementBlockExpression`. That struct has exactly `open`, recovered ordered `statements`, recovered `close`, and `range`.

The AST does not duplicate comma, semicolon, newline, or trailing-separator spelling. Those bytes remain source-order CST children; the recovered close preserves either the matching brace range or its committed missing slot.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| `{` at EOF | empty body is valid; emit only one zero-width close Missing |
| `{x` at EOF | retain the Statement and emit one close Missing |
| `{x,` at EOF | trailing comma is valid; emit only one close Missing |
| `{x y}` with a separate second Statement candidate | one zero-width separator Missing, then retry `y` as the next Statement |
| `{x,,y}` | recover the mandatory post-comma Statement; do not accept an empty Statement |
| `{x,@ y}` | one non-empty statement Error, then same-slot retry at `y` |
| `{x]}` | consume `]` as one closing-delimiter Error and continue seeking this block's `}` |
| owner/root safe point before `}` | do not consume it; emit zero-width close Missing |

All Missing nodes are zero-width, Errors are non-empty maximal episodes, and each committed recovery node has one diagnostic identity.

## 8. Boundary and state-restoration contract

Every AST/direct exit restores the incoming delimiter stack, stop set, `ml_arg`, inline mode, and ambient-owner/If-companion visibility state. The braced barrier owns current-depth newline sequence authority; nested lexical regions and delimiters cannot donate separators or closes to the outer block. This is the same brace-owned sequence authority later reused as an ASOB barrier, while the outer node remains this construct's own owner.

## 9. Yulang2 divergences

Yulang3 retains ordinary brace-primary statement blocks, empty validity, comma/semicolon/newline separators, and trailing separators. It deliberately replaces overloaded Yulang2 `BraceGroup` with primary-only `BracedStatementBlockExpression`, preserves flat `OperatorChain` statements rather than Pratt subtrees, emits no synthetic newline separator token, and does not add historical fixed `ExprSpread`.

## 10. Known residual / deferred surface

The documented `ASOB-G` caller-boundary residual remains characterized rather than hidden. Brace-specific spread, record/block/argument interpretation, declaration and control-flow brace bodies, projection/rule/use/interpolation forms, HIR lowering, inference, diagnostics, and formatting remain deferred or belong to their own owner grammar.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/expression.rs`: `recognize_braced_statement_block_open`, `recognize_braced_statement_block_close`, `parse_braced_statement_block_expression`, `braced_statement_block_close_pending`, `push_braced_statement_block_scope`, `pop_braced_statement_block_scope`, `commit_braced_statement_block_expression`, `commit_braced_statement_block_close`, `emit_braced_statement_separator_missing`, `emit_braced_close_missing`, and `emit_braced_close_error`.

Fixtures include `braced_statement_block_is_a_primary_with_all_separator_forms`, `braced_statement_block_ast_keeps_statement_count_close_and_range`, `braced_statement_block_is_binding_power_invariant_and_keeps_deeper_newlines_local`, `braced_statement_block_keeps_colon_arguments_and_outer_chain_flat`, and `braced_statement_block_recovers_mandatory_slots_and_close`.
