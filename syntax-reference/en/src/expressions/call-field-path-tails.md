# Call, field, path, and ML-application tails

## 1. Status, authority, and last verification

The Authoritative Call/Field/Path/ML fixed-tail addendum is lines 9695–10182 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its current ML-delimited-owner composition is refined by the later Authoritative Index/Projection addendum at lines 10184–10660, which establishes the typed expression-delimited owner shared by Call, Index, and Projection items.

The implementation series is `82bd7613`, `4d2931d6`, and `97b6bc81`. The later shared-owner wiring is `5f067e33`, and current ambient boundary handling is covered by `a355058d` and `af3cce2f`.

## 2. Scope and non-scope

This page covers four target-free source-order `OperatorChain` continuations: adjacent CallTail, FieldTail, PathTail, and one-argument-per-node ML application. Call owns a layout-aware argument list; Field owns an adjacent dot/name; Path owns `::` plus a normal or sigil segment; ML owns qualifying non-empty trivia plus one nested chain.

Index and Projection bodies/recovery belong to their own later addendum. Colon application, `WithBodyTail`, semantic call/field/path resolution, application association, HIR lowering, inference, diagnostics wording, and formatting are outside this page's parser scope.

## 3. BNF-equivalent grammar

```text
FixedPostfixContinuation := CallTail | FieldTail | PathTail

CallTail := LParen CallOpeningTrivia
            [ OperatorChain { CallSeparator OperatorChain } [ CallSeparator ] ]
            RParen
CallSeparator := Comma | Semicolon | ImplicitNewlineBoundary(call_base)

FieldTail := Dot Identifier
PathTail := ColonColon G* PathSegment
PathSegment := Identifier | SigilIdentifier

MlApplicationContinuation := MlArgumentSeparator MlArgument
MlArgumentSeparator := non-empty trivia with no newline
                     | newline with following_indent > active_base
MlArgument := OperatorChain under the ml_arg stop scope
```

Call's opener and Field's dot/name are adjacent; Path permits trivia after `::`. ML requires both a qualifying non-empty separator and a shared NUD candidate. Equal-or-shallower newline is not an ML separator and returns to the outer owner.

## 4. Judge, priority, and owner boundary

At an operand-complete site, active owner stops, matching closes, and equal-or-shallower newline win first. The canonical longest dynamic judge then retains an accepted suffix/infix spelling. Next, adjacent `(` is CallTail, exact `.identifier` is FieldTail, and exact `::` is PathTail; projection lookahead takes precedence over bare Field recovery. Only then can qualifying trivia plus a shared NUD form `MlArgument`.

Thus `f(x)` is a CallTail while `f (x)` is ML application with a parenthesized argument. ML does not push its own layout frame: its nested chain sets `ml_arg`, reads the current typed baseline/owner, and leaves later qualifying trivia for the enclosing chain to form sibling ML arguments. All four continuations precede terminal `ColonApplicationTail`; colon ends the current chain.

## 5. Byte-exact CST worked examples

The addendum gives source-order CST shapes but no byte-range-annotated tree; no ranges are invented here.

```text
f(x)
```

Design line 9929 fixes an adjacent opener as one `CallTail`.

```text
f (x)
```

Design line 9930 fixes non-empty same-line trivia plus a parenthesized NUD as one `MlArgument`, not a CallTail.

```text
f x y
```

Design lines 9978 and 10152 fix two sibling `MlArgument` nodes: the space before `y` belongs to the outer chain rather than the nested first argument.

```text
a.b(c)::d e
```

Design lines 10101–10110 give the source-order outline: primary `a`, FieldTail, CallTail, PathTail, trivia, and MlArgument, with no target child nested into any tail.

## 6. Parser-side AST shape

`OperatorChainItem::FixedPostfix` holds `FixedPostfixTail`; `OperatorChainItem::MlArgument` has exactly boxed `argument` and `range`. In this page's variants, `FixedPostfixTail` is `Call`, `Field`, or `Path`.

`CallTail` has exactly `open`, ordered `arguments`, recovered `close`, and `range`. `FieldTail` has exactly `dot`, recovered `name`, and `range`. `PathTail` has exactly `separator`, recovered `segment`, and `range`; `PathSegment` is exactly `Identifier` or `SigilIdentifier`. AST does not retain separator spelling/trivia or a target edge.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| `f()` | valid empty call; no recovery |
| `f(,a)` / `f(a,,b)` | one zero-width CallArgument Missing at each absent argument; retain separator and retry |
| `f(a` at EOF or caller boundary | retain argument, leave boundary untouched, emit missing `RParen` |
| malformed call argument before a valid NUD | one maximal non-empty Error, then same-slot retry |
| `x.` at EOF/owner boundary | retain dot and emit zero-width FieldName Missing |
| `x..`, `x...`, `x.(`, `x.{` | do not split a longer operator/projection candidate into Field plus Missing |
| `x::` at EOF/owner boundary | retain `::` and emit zero-width PathSegment Missing |
| `x::::name` | missing first segment, then non-consuming same-position retry at the second `::` |
| `f ` at EOF or no shared NUD | do not commit an empty ML node |
| accepted ML prefix/nullfix with absent operand | nested OperatorChain owns one operand Missing; ML adds no duplicate |

Missing is zero-width, Error is non-empty, accepted introducers cut, and owner boundaries remain unconsumed.

## 8. Boundary and state-restoration contract

Call pushes Parenthesis plus comma/semicolon/right-parenthesis stops, an indentation baseline, and `ExpressionDelimitedOwner::Call`; each is restored on normal, recovery, and rollback exits. ML uses that enclosing typed owner or root context but restores its nested `ml_arg` scope exactly. Nested delimiter frames, active ambient owner claims, lexical regions, outer closes, and equal-or-shallower newlines remain higher-priority boundaries.

## 9. Yulang2 divergences

Yulang3 splits Yulang2 composite `DotField` into Dot plus Identifier, emits raw call punctuation/trivia instead of separator wrappers or empty implicit-separator nodes, uses typed zero-width Missing/maximal Error recovery, and keeps ML strictly whitespace/layout separated rather than generalizing Yulang2 trivia-free ML candidates.

## 10. Known residual / deferred surface

The documented `ASOB-G` caller-boundary residual remains characterized rather than hidden. Index/Projection syntax bodies, semantic target association, resolution, HIR lowering, inference, diagnostics, and formatting remain deferred or belong to their own grammar owner.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/expression.rs`: `recognize_fixed_postfix`, `recognize_ml_argument`, `ml_argument_candidate_input`, `ml_argument_context_allows`, `parse_fixed_postfix_tail`, `parse_call_tail`, `call_argument_error_retry_ast`, `commit_fixed_postfix_tail`, `commit_call_tail`, `commit_call_separator`, `emit_call_missing`, `emit_call_close_missing`, and `emit_call_error`.

Fixtures include `fixed_field_and_path_tails_are_flat_and_bp_neutral`, `call_tail_uses_adjacent_opener_and_layout_boundaries`, `call_tail_recovers_missing_arguments_and_closing_delimiter`, `call_and_ml_adjacency_keep_flat_source_order`, `ml_arguments_split_on_trivia_but_keep_adjacent_fixed_tails_and_colon_terminality`, `call_and_ml_recovery_keep_owner_boundaries_local`, and `call_tail_restores_each_enclosing_owner_frame`.
