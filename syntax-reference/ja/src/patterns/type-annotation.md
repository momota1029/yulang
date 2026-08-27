# Trailing Pattern type annotation

## 1. 状態・正本・最終確認

Authoritative な trailing annotation 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 16042–16556 行にあり、canonical な `PTA-G`、`PTA-J`、`PTA-C`、`PTA-A`、`PTA-O`、`PTA-R` を持つ。mandatory TypeExpression の malformed-newline behavior は 16557–16861 行の Authoritative `TMN` 追補と、その implementation authority である 16862–17289 行の positional-fence 追補で定まる。

主実装は `9323ce68`。後続 commit は `d99d49e7`、`72948621`、`13450592`、`7838355e`、`a0365f98`、`42c1544c`、`d58181df`、`2c4d7540`。このページは `102cfa98` を基準に確認した。

## 2. 対象範囲と非対象

この機能は canonical Pattern に optional かつ terminal な `Pattern : TypeExpression` tail を一つ追加する。bounded trivia、precedence、CST/AST shape、typed recovery、既存 Binding/Case/Catch/delimited Pattern owner との composition を対象にする。

Pattern constructor/ML tail、新しい TypeExpression grammar、新しい declaration syntax、type checking、Pattern HIR/lowering、annotation semantics、diagnostics 文言、formatter policy は対象外である。

## 3. BNF 相当の grammar

```text
Pattern := PatternBp(Lowest)
PatternBp(minimum) := PatternPrimary { ExistingAliasOrAlternationTail allowed by PTA-J } [ PatternTypeAnnotation allowed by PTA-J ]
PatternTypeAnnotation := Gpta Colon Gpta RequiredTypeExpression(Pattern::TypeAnnotation)
```

`Gpta` は one maximal trivia run である。physical newline がない trivia、または following indentation が entry-captured `pattern_continuation_base` より strictly greater な physical newline だけを accept する。equal-or-shallower run は whole rollback する。annotation は optional かつ terminal であり、その後に alias、alternation、second annotation を judge しない。

## 4. Judge・priority・owner boundary

shared tail judge は exact `as`、次に exact `|`、最後に `minimum <= TypeAnnotation` かつ active Colon stop が勝たない場合の exact single `:` を試す。`::` は annotation candidate ではない。precedence は `Lowest`、`TypeAnnotation`、`Alternation`、`Alias` の順で、`A | B as c: Int` の annotation は whole outer Pattern に attach する。

Record field は nested Pattern parse 前に first same-line colon を own する。従って `{a: A}` は field colon、`{a: A} : SomeType` は outer annotation になる。annotation colon を accept した後、TypeExpression mandatory slot は existing stop/closer を import する。Binding は `=`、arm は arrow/guard、Catch は comma、delimited owner は local close/separator を own する。

## 5. Byte-exact CST の worked examples

annotation 追補は complete token-tree shape を示すが、この例群の byte-range 付き CST tree はない。ここでは byte range を作らない。

```text
x: Int
```

設計文書 16318–16331 行は identifier Pattern の後に、`Colon`、post-colon whitespace、`TypeExpression` child を own する `PatternTypeAnnotation` を示す。

```text
A | B as c: Int
```

設計文書 16333–16358 行は、RHS が `PatternAliasTail` を own する `PatternAlternationTail` と、outer Pattern の final child である `PatternTypeAnnotation` を示す。

```text
my x: Int = 0
```

設計文書 16360–16384 行は `BindingHeader` 内の annotation を示す。exact `=` 前の whitespace は Binding owner に rollback し、annotation は colon 側の byte だけを own する。

```text
my y: = 1
```

設計文書 16442–16466 行は、`=` 前の zero-width site に `PatternTypeAnnotation > TypeExpression > Missing(Pattern::TypeAnnotation, TypeExpression)` を置き、`=` 自体は Binding-owned のままにする。

## 6. Parser 側 AST shape

`Pattern` は `head`、`tails`、`type_annotation`、`range` を持つ。`type_annotation` は iterative tail ではなく `Option<PatternTypeAnnotation>` である。`PatternTypeAnnotation` は `colon`、recovered boxed `type_expr`、`range` を持つ。

colon を accept すると RHS が incomplete でも option は present になる。range は complete 時に TypeExpression まで、incomplete RHS 時に colon までであり、trivia は semantic range を延ばさない。direct CST は synthetic punctuation/separator を作らず `SyntaxKind::PatternTypeAnnotation` を使う。

## 7. Typed recovery table

| condition | AST/CST result と continuation |
| --- | --- |
| annotation candidate なし | `type_annotation = None`。node/diagnostic なし。同位置で return |
| colon + valid TypePrimary | complete annotation と TypeExpression 一件 |
| colon + EOF/stop/close/comma/semicolon/equal-or-shallower newline | incomplete RHS と zero-width `Missing(Pattern::TypeAnnotation, TypeExpression)` 一件。boundary は owner のまま |
| colon + malformed run + valid TypePrimary | `Error(Type::Primary, TypeExpression)` 一件後、same-slot retry で complete TypeExpression 一件 |
| colon + malformed run + boundary | non-empty Error 一件だけ。boundary 前で止まり cascading Missing を置かない |

`TMN-C` は maximal newline-bearing trivia run を `TMN-NoNewline`、`TMN-CallerBoundary`、`TMN-Handoff`、`TMN-Boundary`、`TMN-DeeperContinuation` に分類する。committed `TMN-CallerBoundary` は exact untouched trivia start を rollback-scoped positional fence として mark し、後続 TypeExpression owner は fenced trivia もその後の boundary も consume できない。

## 8. Boundary と state-restoration contract

Pattern parser は caller の stop、delimiter、indentation stack を置き換えず、completely missing outer TypeExpression にだけ `PatternRole::TypeAnnotation` を渡す。`TMN` は Pattern-captured continuation base を使い、nested Pattern が無関係な type baseline を借りることを防ぐ。positional-fence state は checkpoint/rollback に参加し、normal multiline type path は fence を作らない。

fixture は Binding/Case/Catch boundary、record-colon ownership、nested base、malformed same-slot retry、active newline caller boundary、AST/direct losslessness を扱う。より広い `ASOB-G` state contract は ambient/If、delimiter、indentation、type-owner、ML、fence restoration も含む。

## 9. Yulang2 divergences

Yulang2 は `TypeAnn` を alternation/alias より tight に attach した。Yulang3 は terminal な outer `PatternTypeAnnotation` 一つにする。そのため repeated annotation を iterative tail として accept せず、left side を wrap せず named AST field を使い、generic `InvalidToken` recovery ではなく typed Missing/Error と owner-safe retry を使う。surface spelling、accepted colon 後の mandatory RHS、nested Pattern と outer binding target からの reachability は保つ。

## 10. Known residual / deferred surface

documented residual は annotation grammar の例外ではない。`ASOB-G` は missing nested delimiter の背後にある hidden caller boundary を記録する。Cast 追補は Cast-contained Pattern/type owner 向けに別の condition-based residual characterization を持つ。

constructor/ML Pattern tail、annotation semantics/type checking、Pattern HIR/lowering、resolver/inference integration、diagnostics text、formatting は deferred である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/pattern.rs` では `parse_pattern_bp`、`parse_pattern_bp_with_fresh_primary_policy`、`recognize_pattern_led`、`PatternTypeAnnotation`、`parse_required_pattern_with_outer_missing_role_and_policy`、`commit_direct_pattern_with_outer_missing_role_and_policy` を参照する。

`crates/yu-syntax/src/grammar/type_expr.rs` では `parse_required_type_expression_with_recovery_context`、`commit_direct_type_expression_with_recovery_context`、`classify_type_malformed_trivia`、`scan_type_item_invalid_run_with_disposition`、positional-fence handling を参照する。

fixture は `type_annotation_is_terminal_and_qualifies_the_outer_pattern`、`type_annotation_reaches_nested_patterns_and_keeps_record_colons_owned`、`type_annotation_trivia_ranges_and_recovery_keep_owner_boundaries`、`annotation_malformed_recovery_uses_the_nested_pattern_base`、`enclosing_binding_case_and_catch_owners_keep_annotation_boundaries`、`malformed_trivia_classifier_distinguishes_all_tmn_c_outcomes`、`delimited_recovery_classifier_yields_to_a_pending_fence_before_trivia`、`legacy_after_trivia_marks_a_caller_boundary_fence`、`ordinary_multiline_type_constructs_do_not_create_caller_boundary_fences`。
