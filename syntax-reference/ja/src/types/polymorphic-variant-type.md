# Polymorphic-variant type

## 1. 状態・正本・最終確認

Authoritative な polymorphic-variant primary 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 14527–15233 行にある。current caller-boundary behaviour は 18358–19161 行の `ASOB-G` でも扱う。

実装 series は `fd2f3ad8`、`52f45c52`、`e451063f`、`3a048bde`、`d37a77cf`、`54f1b927`、`f4332308`。最後の listed implementation gate は `f4332308`。特に `d37a77cf` は AST/direct-CST realization を別々の two-level judge ではなく one streaming driver へ移した。

## 2. 対象範囲と非対象

この TypePrimary は type-only form `:{A Int, B}` であり、plain identifier tag ごとに zero-or-more payload type を持つ。outer tag list は comma/qualifying-newline boundary、tag の inner payload sequence は non-empty same-line payload boundary を所有する。

expression-side variant literal、pattern polymorphic variant、struct/enum/error payload semantics、declaration/use-site wiring、HIR/lowering、inference、resolver、diagnostics wording、formatting は追加しない。

## 3. BNF 相当の grammar

```text
TypePrimary := ... | PolymorphicVariantType
PolymorphicVariantType := Colon AdjacentLBrace PolyVariantOpeningTrivia [ PolymorphicVariantTag { PolyVariantTagBoundary PolymorphicVariantTag } [ PolyVariantTagBoundary ] ] RBrace
PolymorphicVariantTag := Identifier { PolymorphicVariantPayload }
PolymorphicVariantPayload := PolyVariantPayloadBoundary TypeExpressionInTypeMlScope
PolyVariantPayloadBoundary := NonEmptyTriviaWithoutPhysicalNewline
PolyVariantTagBoundary := ExplicitPolyVariantCommaBoundary | ImplicitNewlineBoundary(poly_variant_base)
ExplicitPolyVariantCommaBoundary := CommaBoundary
```

`AdjacentLBrace` は `{` が `Colon.end` から正確に始まることを表す。physical newline は inner payload sequence を必ず終え、outer list だけが qualifying newline を tag boundary として classify できる。

## 4. Judge・priority・owner boundary

canonical primary judge は active stop/caller-owned close を返した後、ordinary name/number/`(`/`{` より前に `for`、adjacent `"'["`、adjacent `":{"` を probe する。bare `:` は cut しない。`:{A}` は primary だが、`: {A}`、`:/*c*/{A}`、`:\n{A}` は candidate ではない（設計文書 14612–14635 行）。

pair accept 後、outer brace/list frame が tag/close recovery を所有する。tag は Type-ML mode の inner payload judge を動かすので、same-line payload candidate は TypeApply tail ではなく sibling になる。complete primary は ordinary fixed tail judge に戻る。`F :{A}` は TypeApply argument であり、その後の path/call/apply/arrow tail は ordinary のままである。

## 5. Byte-exact CST の worked examples

追補は complete source-order CST tree を持つが、この construct の byte-range 付き tree はない。ここでは range を作らない。

```text
:{A Int, B}
```

設計文書 14980–14998 行は `:`, `{`, tag `A`、whitespace を持つ `PolymorphicVariantPayload`、comma、tag `B`、`}` を `PolymorphicVariantType` が所有する tree を示す。

```text
:{A Int Bool}
```

設計文書 15000–15018 行は tag `A` の下に sibling payload node 二つを示す。`Bool` は `Int` の TypeApply tail ではない。

```text
:{A Int
B}
```

設計文書 15020–15038 行は payload を持つ tag `A` と tag `B` の間の physical newline を outer-list trivia として示し、synthetic separator を置かない。

```text
:{
  A Pair(
    Int,
    Bool
  )
  B
}
```

設計文書 15042–15083 行は nested `TypeCallTail` が所有する newline と `)` 後の tag-level newline を区別する。

## 6. Parser 側 AST shape

`TypePrimary::PolymorphicVariant(PolymorphicVariantType)` は real primary である。`PolymorphicVariantType` は正確に `colon`、`open`、recovered ordered `tags`、optional `trailing_comma`、recovered `close`、`range` を持つ。

各 `PolymorphicVariantTag` は recovered `name`、recovered ordered `payloads`、`range` を持つ。各 `PolymorphicVariantPayload` は recovered `boundary`、recovered boxed `type_expr`、`range` を持つ。すべて source-slot field であり、synthetic inner-sequence wrapper はない。

direct CST は `SyntaxKind::PolymorphicVariantType`、`SyntaxKind::PolymorphicVariantTag`、`SyntaxKind::PolymorphicVariantPayload` を使い、punctuation/trivia を source order のまま保持する。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| non-adjacent または incomplete `:{` introducer | variant authority なし。ordinary primary owner が継続 |
| empty list または complete tag 後の real `}` | valid list/close。real trailing comma は empty tag なしで保持 |
| leading/repeated comma | required tag slot ごとに zero-width `PolymorphicVariantTag` Missing 一件 |
| non-caller-owned semicolon | `PolymorphicVariantTagSeparator` Error 一件後 outer tag judge へ re-enter |
| wrong-kind/malformed tag name | typed tag/name Error。同じ tag slot を retry し second tag を作らない |
| primary 前の empty payload gap | `PolymorphicVariantPayloadBoundary` Missing 後 same-position type retry |
| accepted payload boundary の malformed | payload Error 一件後 same-slot retry。outer safe point では type slot が Incomplete で cascade なし |
| missing/mismatched brace | typed close Missing/Error 一件。caller-owned boundary は non-consuming |

AST は direct CST と同じ accepted/recovery range を advance する。direct CST は source-bearing/zero-width recovery node ごとに committed Missing/Error record 一件を作る。

## 8. Boundary と state-restoration contract

accept は brace delimiter、`TypeDelimitedOwner::PolymorphicVariant`、local stop、layout frame、Type-ML state を establish する。normal/recovery/rollback exit は delimiter/stop/layout/type-owner/Type-ML state を exact restore する。shared driver が同じ tag/payload boundary と safe-point decision を AST/direct CST へ与える。

## 9. Yulang2 divergences

Yulang3 は Yulang2 の trivia-tolerant colon/brace spelling を adjacent `":{"` へ意図的に狭め、non-empty same-line payload boundary を要求し、Yulang2-style direct payload child ではなく source-bearing payload node を出し、generic invalid-token recovery を typed phase に置換する。plain-Identifier tag head、zero-or-more payload、comma-only explicit outer separation、qualifying outer newline、ordinary TypeApply/tail composition は保つ。

## 10. Known residual / deferred surface

`ASOB-G` は general caller-boundary-hidden-behind-missing-delimiter residual を characterization し、この primary はそれ以上の exemption を作らない。bracket row と TypeExpression use-site wiring は original addendum では deferred で、現在は別途 specified される。semantic variant representation、HIR/lowering、inference、resolver、diagnostics、formatting は deferred のままである。

## 11. 実装と regression fixture の cross-reference

shared implementation は `crates/yu-syntax/src/grammar/type_expr/polymorphic_variant.rs` にある。`parse`、`commit_direct`、`drive`、`drive_payloads`、`inspect_payload`、`classify_tag_boundary`、`consume_invalid_run` を参照する。`crates/yu-syntax/src/grammar/type_expr.rs` は `scan_polymorphic_variant_open` と enclosing canonical primary/tail entry を提供する。

regression fixture は `polymorphic_variant_type_is_a_two_level_primary`、`polymorphic_variant_type_preserves_primary_and_ml_payload_boundaries`、`polymorphic_variant_type_uses_phase_specific_recovery_roles`、`polymorphic_variant_outer_judge_preserves_owner_boundaries_and_reentry_order`、`polymorphic_variant_shared_driver_regression_matrix`。
