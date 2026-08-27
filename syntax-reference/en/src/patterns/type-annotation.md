# Trailing Pattern type annotations

## 1. Status, authority, and last verification

The Authoritative trailing annotation addendum is lines 16042–16556 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`, with canonical `PTA-G`, `PTA-J`, `PTA-C`, `PTA-A`, `PTA-O`, and `PTA-R`. Its mandatory-TypeExpression malformed-newline behavior is governed by the Authoritative `TMN` addendum at 16557–16861 and its implementation authority, the positional-fence addendum at 16862–17289.

The main implementation is `9323ce68`. Follow-up commits are `d99d49e7`, `72948621`, `13450592`, `7838355e`, `a0365f98`, `42c1544c`, `d58181df`, and `2c4d7540`. This page was checked against `102cfa98`.

## 2. Scope and non-scope

This feature adds one optional, terminal `Pattern : TypeExpression` tail to canonical Pattern, including bounded trivia, precedence, CST/AST shape, typed recovery, and composition with existing Binding, Case, Catch, and delimited Pattern owners.

It does not add Pattern constructor/ML tails, a new TypeExpression grammar, new declaration syntax, type checking, Pattern HIR/lowering, annotation semantics, diagnostics wording, or formatter policy.

## 3. BNF-equivalent grammar

```text
Pattern := PatternBp(Lowest)
PatternBp(minimum) := PatternPrimary { ExistingAliasOrAlternationTail allowed by PTA-J } [ PatternTypeAnnotation allowed by PTA-J ]
PatternTypeAnnotation := Gpta Colon Gpta RequiredTypeExpression(Pattern::TypeAnnotation)
```

`Gpta` is one maximal trivia run. It accepts no-newline trivia, or a physical newline only when the next indentation is strictly greater than the entry-captured `pattern_continuation_base`. Equal-or-shallower runs roll back whole. The annotation is optional and terminal: no alias, alternation, or second annotation is judged after it.

## 4. Judge, priority, and owner boundary

The shared tail judge tries exact `as`, then exact `|`, then an exact single `:` only when `minimum <= TypeAnnotation` and no active Colon stop wins. `::` is not an annotation candidate. The precedence order is `Lowest`, `TypeAnnotation`, `Alternation`, then `Alias`: `A | B as c: Int` attaches the annotation to the whole outer Pattern.

Record fields own their first same-line colon before nested Pattern parsing. Thus `{a: A}` has a field colon, while `{a: A} : SomeType` has an outer annotation. After annotation colon acceptance, the TypeExpression mandatory slot imports existing stops/closers; Binding owns `=`, arms own arrow/guards, Catch owns comma, and delimited owners own their local close/separator.

## 5. Byte-exact CST worked examples

The annotation addendum gives complete token-tree shapes but no byte-range-annotated CST trees for these examples; no ranges are invented here.

```text
x: Int
```

Design lines 16318–16331 show `PatternTypeAnnotation` owning `Colon`, post-colon whitespace, and a `TypeExpression` child, after the identifier Pattern.

```text
A | B as c: Int
```

Design lines 16333–16358 show `PatternAlternationTail` whose RHS owns `PatternAliasTail`; the `PatternTypeAnnotation` is the outer Pattern's final child.

```text
my x: Int = 0
```

Design lines 16360–16384 show the annotation inside `BindingHeader`; whitespace before exact `=` rolls back to the Binding owner, while the annotation owns only its colon-side bytes.

```text
my y: = 1
```

Design lines 16442–16466 show `PatternTypeAnnotation > TypeExpression > Missing(Pattern::TypeAnnotation, TypeExpression)` at the zero-width site before `=`, which remains Binding-owned.

## 6. Parser-side AST shape

`Pattern` has `head`, `tails`, `type_annotation`, and `range`. `type_annotation` is `Option<PatternTypeAnnotation>`, not an iterative tail. `PatternTypeAnnotation` stores `colon`, recovered boxed `type_expr`, and `range`.

An accepted colon makes the option present even when the RHS is incomplete. Its range ends at the TypeExpression on completion, or at the colon on an incomplete RHS; trivia does not extend semantic ranges. Direct CST uses `SyntaxKind::PatternTypeAnnotation` without synthetic punctuation or separators.

## 7. Typed recovery table

| condition | AST/CST result and continuation |
| --- | --- |
| no annotation candidate | `type_annotation = None`; no node or diagnostic; return at the same position |
| colon + valid TypePrimary | complete annotation and one TypeExpression |
| colon + EOF/stop/close/comma/semicolon/equal-or-shallower newline | incomplete RHS and one zero-width `Missing(Pattern::TypeAnnotation, TypeExpression)`; boundary remains owned |
| colon + malformed run + valid TypePrimary | one `Error(Type::Primary, TypeExpression)`, then same-slot retry to one complete TypeExpression |
| colon + malformed run + boundary | one non-empty Error only; stop before boundary and add no cascading Missing |

`TMN-C` classifies a maximal newline-bearing trivia run as `TMN-NoNewline`, `TMN-CallerBoundary`, `TMN-Handoff`, `TMN-Boundary`, or `TMN-DeeperContinuation`. A committed `TMN-CallerBoundary` marks the exact untouched trivia start with a rollback-scoped positional fence; a later TypeExpression owner cannot consume the fenced trivia or the following boundary.

## 8. Boundary and state-restoration contract

The Pattern parser does not replace the caller's stop, delimiter, or indentation stacks; it supplies only `PatternRole::TypeAnnotation` for a completely missing outer TypeExpression. `TMN` uses the Pattern-captured continuation base, preventing a nested Pattern from borrowing an unrelated type baseline. Positional-fence state participates in checkpoints and rollback, while normal multiline type paths do not create a fence.

Fixtures exercise Binding/Case/Catch boundaries, record-colon ownership, nested bases, malformed same-slot retry, active newline caller boundaries, and AST/direct losslessness. The broader `ASOB-G` state contract also covers ambient/If, delimiter, indentation, type-owner, ML, and fence restoration.

## 9. Yulang2 divergences

Yulang2 attached `TypeAnn` tighter than alternation/alias; Yulang3 makes one terminal outer `PatternTypeAnnotation`. Yulang3 therefore does not accept repeated annotations as an iterative tail, keeps a named AST field rather than wrapping the left side, and uses typed Missing/Error with owner-safe retry instead of generic `InvalidToken` recovery. Surface spelling, mandatory RHS after accepted colon, and reachability from nested Patterns and outer binding targets are preserved.

## 10. Known residual / deferred surface

The documented residual is not an annotation grammar exception: `ASOB-G` characterizes hidden caller boundaries behind missing nested delimiters. The Cast addendum has a separate condition-based residual characterization for Cast-contained Pattern/type owners.

Deferred work includes constructor/ML Pattern tails, annotation semantics and type checking, Pattern HIR/lowering, resolver/inference integration, diagnostics text, and formatting.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/pattern.rs`: `parse_pattern_bp`, `parse_pattern_bp_with_fresh_primary_policy`, `recognize_pattern_led`, `PatternTypeAnnotation`, `parse_required_pattern_with_outer_missing_role_and_policy`, and `commit_direct_pattern_with_outer_missing_role_and_policy`.

In `crates/yu-syntax/src/grammar/type_expr.rs`: `parse_required_type_expression_with_recovery_context`, `commit_direct_type_expression_with_recovery_context`, `classify_type_malformed_trivia`, `scan_type_item_invalid_run_with_disposition`, and positional-fence handling.

Fixtures include `type_annotation_is_terminal_and_qualifies_the_outer_pattern`, `type_annotation_reaches_nested_patterns_and_keeps_record_colons_owned`, `type_annotation_trivia_ranges_and_recovery_keep_owner_boundaries`, `annotation_malformed_recovery_uses_the_nested_pattern_base`, `enclosing_binding_case_and_catch_owners_keep_annotation_boundaries`, `malformed_trivia_classifier_distinguishes_all_tmn_c_outcomes`, `delimited_recovery_classifier_yields_to_a_pending_fence_before_trivia`, `legacy_after_trivia_marks_a_caller_boundary_fence`, and `ordinary_multiline_type_constructs_do_not_create_caller_boundary_fences`.
