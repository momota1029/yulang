# Colon application

## 1. Status, authority, and last verification

The Authoritative generic colon-application and indented-block-boundary addendum is lines 5014–5467 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its original comma-only inline loop is superseded by the layout-aware separator revision at 9314–9693; its tail, inline-versus-indented branch, CST, and AST decisions remain in force.

The design and implementation commits are `01348df9`, `14eb4900`, and `81ef211d`. `14eb4900` introduced the terminal colon tail; `81ef211d` added the current comma-or-qualifying-newline inline boundary rule.

## 2. Scope and non-scope

Generic colon application is a terminal continuation after a completed `OperatorChain`: `f: x`, `f: x, y`, or `f:\n  x\n  y`. It owns a non-empty inline argument sequence when no outer sequence owner is active, or an indented canonical statement block after a strictly deeper newline.

It does not own `if`/`elsif`/`else` arm colons, declaration/pattern/type colons, `with:`, semantic call sugar, target association, HIR/lowering, type inference, record-field semantics, diagnostics wording, or formatting.

## 3. BNF-equivalent grammar

```text
ColonApplicationTail :=
    Colon G0 InlineColonArguments
  | Colon IndentedStatementBlock

InlineColonArguments(no_outer_sequence_owner) :=
    OperatorChain
    { InlineColonArgumentSeparator OperatorChain }
    [ ImplicitNewlineBoundary(colon_inline_base) ]

InlineColonArgumentSeparator :=
    ExplicitCommaBoundary
  | ImplicitNewlineBoundary(colon_inline_base)

InlineColonArguments(outer_sequence_owner) := OperatorChain
```

An indented block is selected only when post-colon trivia has a physical newline and `block_indent > base_indent`. A literal trailing comma is not valid for the colon-owned inline sequence.

## 4. Judge, priority, and owner boundary

The operand-complete chain judge first respects active `StopKind::Colon`, `ml_arg`, caller boundaries, and longest punctuation (`::` before `:`). Only an unreserved lone colon cuts to `ColonApplicationTail`; accepted colon parsing is total and terminates the current chain.

The layout probe chooses inline only with no physical post-colon newline. A newline starts the indented branch only at strictly deeper indentation; wrong-indent newline is left for the outer owner. Outer sequence ownership takes precedence: in `(f: x, y)`, colon parses one RHS and leaves comma to the parenthesized owner, while root `f: x, y` owns both arguments.

## 5. Byte-exact CST worked examples

The addendum gives source-order CST trees but no byte-range-annotated tree; no ranges are invented here.

```text
a + b: x
```

Design lines 5213–5226 show an outer `OperatorChain` with `a`, infix `+`, `b`, then a target-free `ColonApplicationTail` that owns only `:`, whitespace, and RHS `x`.

```text
f: x, y + z
```

Design lines 5041–5045 and 5411–5413 record the two-inline-argument form; comma and argument chains are tail children, not source-absent list wrappers.

```text
f:
  x
  y
```

Design lines 5041–5045 and 5415–5417 require one `IndentedStatementBlock` with its opening trivia and statement sequence.

```text
{x: 1}
```

Design lines 5323–5336 and 5418–5419 fix this as `BracedStatementBlockExpression` containing an ordinary colon tail, not a dedicated record CST node.

## 6. Parser-side AST shape

`TerminalOuterTail::ColonApplication` contains `ColonApplicationTail`. That struct has exactly `colon`, recovered `rhs`, and `range`; it has no target field.

`ColonApplicationRhs` has exactly `Inline { arguments: Vec<Recovered<OperatorChain<'source>>> }` and `Indented { block: IndentedStatementBlock<'source> }`. `IndentedStatementBlock` has exactly `base_indent`, `block_indent`, recovered ordered `statements`, and `range`. Inline comma tokens and whitespace remain CST-owned rather than AST fields.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| `f:` or horizontal trivia then EOF | retain colon and emit one zero-width RHS Missing |
| post-colon newline at equal/shallower indent | do not consume newline/next statement; emit one RHS Missing at colon boundary |
| strictly deeper newline then EOF | retain block/opening trivia and emit one statement Missing in the block |
| colon-owned leading comma | one first-argument Missing; preserve comma and retry next argument |
| colon-owned comma then EOF | one next-argument Missing; no valid trailing-comma marker |
| comma owned by outer sequence | leave comma unconsumed for its owner; colon parses at most one RHS |
| malformed inline run before a valid value | one non-empty Error, then same-argument-slot retry |
| malformed block statement | shared statement recovery synchronizes to sibling indentation or dedent |

Missing is zero-width, Error is non-empty, and the accepted tail/chain always finishes without duplicate diagnostics.

## 8. Boundary and state-restoration contract

The introducer snapshots its active base indentation before post-colon trivia. Inline/list stops, indentation baselines, `inline`, `ml_arg`, and stop-set changes are restored on every normal, recovery, and rollback exit. Dedent, outer comma, matching close, wrong-indent newline, and statement/root boundary are caller safe points and remain unconsumed.

## 9. Yulang2 divergences

Yulang3 preserves lone-colon outer-tail ownership, inline arguments, and strict indented-block triggering, but stores flat `OperatorChain` RHS values rather than Pratt trees. It replaces synthetic separator output with raw trivia, treats the brace-record-looking form as ordinary statement-block plus colon syntax, and gives typed recovery roles to RHS/inline/block slots.

## 10. Known residual / deferred surface

The shared `ASOB-G` hidden caller-boundary residual remains characterized rather than hidden. Colon target association, call/block/record semantic interpretation, HIR/lowering, type inference, `with:`, other control/declaration/pattern/type colon families, diagnostics text, and formatting remain outside this grammar page.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/expression.rs`: `recognize_colon_application_tail`, `parse_inline_colon_arguments`, `outer_owns_inline_argument_sequence`, `commit_colon_application_tail`, `commit_colon_inline_argument`, `colon_inline_argument_error_retry`, `emit_colon_application_missing`, and `emit_colon_application_error`.

Fixtures include `colon_application_ast_and_cst_keep_inline_arguments_in_the_terminal_tail`, `colon_inline_returns_a_live_if_companion_gap_after_its_first_argument`, `colon_inline_newline_arguments_have_ast_direct_and_bp_parity`, `colon_application_recovery_keeps_commas_and_retries_valid_values`, and `colon_application_parses_an_indented_statement_block`.
