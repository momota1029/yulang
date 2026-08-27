# Bracket-row grammar

## 1. 状態・正本・最終確認

Authoritative な bracket-row grammar 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 15235–16040 行にある。後続の shared caller-boundary work は 18358–19161 行の `ASOB-G` にある。

実装 slice は `92f662cc`、`e31ab517`、`327607a9`、`b6d4d91e`、`d25fa985`、`7252920f`、`a7c8fbd8`、`35cad71a`、`5f627f1c`。最後の listed implementation gate は `5f627f1c`。

## 2. 対象範囲と非対象

BracketRow は二つの asymmetric position で使う source-bearing bracketed row である。leading row は mandatory ordinary type head（`[e] T`）を prefix し、trailing row は mandatory arrow（`T [e] -> U`）の optional argument effect になる。item は full TypeExpression である。

EffectfulType primary wrapper、EffectArrow node、別の row-list parser、row-tail semantics、effect inference、use-site wiring、HIR/lowering、resolver/inference、diagnostics wording、formatting は追加しない。

## 3. BNF 相当の grammar

```text
TypeExpression := [ LeadingBracketRow TypeChainTrivia ] TypePrimary { TypeTightTail | TypeApplyArgument } [ TypeArrowBoundary TypeArrowTail ]
LeadingBracketRow := BracketRow
TypeArrowTail := [ BracketRow TypeChainTrivia ] Arrow TypeChainTrivia TypeExpression
BracketRow := LBracket BracketRowOpeningTrivia [ TypeExpression { BracketRowDelimitedBoundary TypeExpression } [ BracketRowDelimitedBoundary ] ] RBracket
BracketRowDelimitedBoundary := CommaBoundary | SemicolonBoundary | ImplicitNewlineBoundary(bracket_row_base)
```

leading row 後の head と trailing row 後の arrow は mandatory recoverable slot である。`TypeChainTrivia` は empty/same-line/strictly-deeper trivia だけを許し、row と head/arrow の間で equal-or-shallower newline を許さない。

## 4. Judge・priority・owner boundary

fresh type slot では `[` は active boundary check と contextual/compound type starter の後、ordinary primary candidate より前の leading-row candidate である。leading row accept 後は second leading row を disabled にし、recursive parse ではなく malformed mandatory head として recover する。

operand complete 後、fixed-tail judge は TypeApply より前に `[` へ bracket-arrow authority を与える。従って `T [e] -> U` は trailing-row arrow、`F [e] T` は malformed bracket-arrow tail、`F ([e] T)` は explicit apply argument である。row delimiter/list frame が item/close recovery を所有し、caller stop と matching/outer close は non-consuming である。

## 5. Byte-exact CST の worked examples

追補は complete source-order CST tree を持つが byte-range 付き tree はない。ここでは range を作らない。

```text
[e] T
```

設計文書 15726–15737 行は leading `BracketRow` を `TypeExpression` の first source-bearing child とし、その後に whitespace と ordinary head `T` を置く。

```text
T [e] -> U
```

設計文書 15739–15756 行は `BracketRow` を arrow/RHS 前の `TypeArrowTail` first child として置く。tail 前の whitespace は enclosing `TypeExpression` に残る。

```text
T [:] -> U
```

設計文書 15790–15809 行は row 内の `:` を `Error(Type::BracketRowItem, TypeExpression)` 一件とし、その後に ordinary valid arrow/RHS を置く。

```text
[e][f]T
```

設計文書 15908–15922 行は first row node だけを置く。complete `[f]` は retried head `T` 前の `Error(Type::LeadingEffectTypeHead, TypeExpression)` 一件になる。

## 6. Parser 側 AST shape

`BracketRow` は正確に `open`、recovered ordered `items`、recovered `close`、`range` を持つ。leading position では `TypeExpression.leading_effect_row`、trailing position では `TypeArrowTail.argument_effect` が保持する。

`TypeExpression` は正確に `leading_effect_row`、recovered `primary`、`postfix`、optional `arrow`、`range` を持つ。`TypeArrowTail` は正確に optional `argument_effect`、recovered `arrow`、recovered boxed `rhs`、`range` を持つ。`EffectfulType`、`EffectArrow`、synthetic list wrapper、synthetic separator field はない。

direct CST は `SyntaxKind::BracketRow` だけを追加する。leading form では first source-bearing child、trailing form では arrow token 前 child になる。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| leading row 後に head がない | `LeadingEffectTypeHead` Missing/Error が existing recovered `TypeExpression.primary` slot を shape |
| trailing row 後に arrow はないが valid RHS candidate がある | `BracketRowArrow` Missing 後 same-position RHS retry |
| trailing row が EOF/outer boundary/newline に到達 | `BracketRowArrow` Missing 一件。RHS Missing を cascade しない |
| real `->` または RHS 前の malformed byte | maximal `BracketRowArrow` Error 一件後 arrow/RHS slot を retry |
| malformed/absent row item | `BracketRowItem`/separator role を伴う shared delimited-item Missing/Error/retry |
| missing/mismatched `]` | typed `ClosingDelimiter(BracketRow)` recovery。actual outer close は consume しない |
| second leading row | balanced second row 全体への delimiter-aware `LeadingEffectTypeHead` Error 一件後 original head を retry |

row-internal recovery は shared type-delimited driver と bracket-specific alignment policy を使い、separator/layout/delimiter/TypeExpression parse を複製しない。

## 8. Boundary と state-restoration contract

leading/trailing form は canonical TypeExpression episode、bracket delimiter、`TypeDelimitedOwner::BracketRow`、local stop、layout frame を再利用する。normal/recovery/rollback の全 exit は delimiter/stop/layout/type-owner/Type-ML state を exact restore する。equal-or-shallower row-to-head/arrow newline は caller boundary に留まり、no-row `T -> U` は既存の CST/AST/recovery boundary を保つ。

## 9. Yulang2 divergences

Yulang3 は trailing-row arrow と leading row の head を typed recovery 付き mandatory にし、row-to-head/arrow trivia を bounded `TypeChainTrivia` に制限し、Yulang2 の shared `TypeRow`/possible synthetic separator を source-bearing `BracketRow` と raw trivia に置換する。asymmetric NUD/LED position、full type item、comma/semicolon/qualifying-newline row boundary、leading-row/ordinary-head と trailing-row/arrow の関係は保つ。

## 10. Known residual / deferred surface

`ASOB-G` は general hidden caller-boundary residual を documentation し、BracketRow はそれ以上の construct-specific exemption を持たない。empty/trailing-separator accept は dedicated bare-bracket oracle fixture ではなく shared delimited source と EffectRow contract からの inference と明記される。effect semantics、use-site integration、HIR/lowering、resolver/inference、diagnostics、formatting は deferred である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/type_expr.rs` では `parse_bracket_row`、`parse_leading_effect_type_head_for_ast`、`commit_direct_leading_effect_type_head`、`parse_bracket_arrow_tail`、`commit_direct_bracket_arrow_tail`、`bracket_arrow_pending`、`bracket_arrow_recovery_candidate`、`scan_bracket_arrow_invalid_run`、`drive_type_delimited`、`commit_direct_type_delimited`、`scan_bracket_row_item_invalid_run` を参照する。

fixture は `leading_bracket_row_is_a_fresh_type_expression_prefix`、`trailing_bracket_row_is_an_arrow_effect_and_not_a_type_apply_argument`、`bracket_arrow_mandatory_slot_recovers_without_rhs_cascades`、`bracket_row_rp1_classifies_every_malformed_item_retry`、`bracket_row_sequence_matrix_keeps_shared_normal_behavior`。
