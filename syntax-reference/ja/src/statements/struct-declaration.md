# `struct` declaration

## 1. 状態・根拠・最終照合

このページは `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の
Authoritative な「canonical `Statement` / root `Declaration` `struct` declaration
grammar」（17400–18359行）を要約する。規範節は `SD-G`、`SD-J`、`SD-T`、`SD-R`
（17497–18359行）である。

approval は `238e0250`。implementation sequence は `47ed2c99`、`62ea8a31`、
`fd401a26`、`eeedc5a1`、`05358e72`、`4c52d048`、`cecba259`、`1900e076`。
observable review finding は `668c9b19` と `7f47d9a7` が修正し、このページの
verified behavior に含む。`b080c022` に対して照合した。

## 2. 対象と非対象

grammar は visibility、exact `struct`、mandatory raw name、bodyless `;`、named braced
field、named indented field、tuple field のいずれかを受ける。named field は
`Identifier : TypeExpression`、tuple field は required TypeExpression を所有する。

declaration generic、derives/`with:` companion、method、constructor、literal、default、
shorthand、field visibility、doc、layout/ABI、semantic field validation、HIR、resolver、
inference、formatter、diagnostics は deferred である。

## 3. BNF 相当の grammar

```text
StructDeclaration :=
    [ VisibilityKw Gstruct+ ] StructKw Gstruct+ StructName Gstruct* StructBody
StructBody :=
    Semicolon
  | LBrace StructOpeningTrivia [ StructNamedField { StructBracedFieldBoundary StructNamedField } ] RBrace
  | Colon StructIndentedOpeningTrivia StructNamedField { StructIndentedFieldBoundary StructNamedField }
  | LParen StructOpeningTrivia [ StructTupleField { StructBracedFieldBoundary StructTupleField } ] RParen
StructNamedField := Identifier Gfield-name Colon Gfield-type RequiredTypeExpression(Struct::FieldType)
StructTupleField := RequiredTypeExpression(Struct::FieldType)
```

`Gstruct` は same-line または strictly-deeper continuation trivia を受ける。brace / tuple
list は `struct_list_base`、indented field は `block_indent` を使う。

## 4. Judge・priority・owner boundary

bare / visibility-led exact `struct` は Binding より先に cut し、`structure`、`structural`、
`my_struct` は ordinary word のままである。complete/recovered name 後に body を選ぶのは exact
`;`、`{`、`(`、lone `:` だけである。following type word から missing body container は発明しない。

field layout は comma と qualifying newline を所有する。deeply indented line は field type
continuation、qualifying equal-or-shallower line は field/list または outer boundary である。
`::` は field colon に split しない。field owner は `StructRole::FieldType` outer role の
full mandatory TypeExpression を使う。

## 5. byte-exact CST worked examples

```text
pub struct Marker;
```

```text
StructDeclaration
  PubKw "pub" 0..3
  StructKw "struct" 4..10
  Identifier "Marker" 11..17
  Semicolon ";" 17..18
```

```text
struct Point { x: Int, y: List Int }
```

は `StructDeclaration 0..36`、`StructField` 二つを持つ。後者の
`List Int` TypeApply range は `34` で終わり、brace close は `35..36` である。

```text
struct Point:
  x: Int
  y: String
```

は `StructDeclaration 0..34`。opening / inter-field newline・indent trivia は
implicit separator wrapper でなくこれが直接所有する。

```text
struct S { x Int, y: Bool }
```

は `13..13` に `Missing(Struct::FieldColon, Colon)` を置き、field type として
`Int` を retry する。`y: Bool` は別 field のままである。

## 6. parser 側 AST shape

```rust
pub(crate) struct StructDeclaration<'source> {
    visibility: Visibility,
    name: Recovered<WordSpan<'source>>,
    derives: Vec<DerivesAttachment<'source>>,
    body: Recovered<StructBody<'source>>,
    range: Range<usize>,
}

pub(crate) enum StructBody<'source> {
    Bodyless { semicolon: Range<usize> },
    NamedBraced(StructNamedBracedBody<'source>),
    NamedIndented(StructNamedIndentedBody<'source>),
    Tuple(StructTupleBody<'source>),
}

pub(crate) struct StructNamedField<'source> {
    name: Recovered<WordSpan<'source>>,
    colon: Recovered<Range<usize>>,
    type_expr: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

pub(crate) struct StructTupleField<'source> {
    type_expr: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}
```

`derives` は後続の shared attachment である。ここでは `StructBody` を選び、synthetic field
でなく incomplete slot を保持する。

## 7. typed recovery table

| condition | recovery と continuation |
| --- | --- |
| keyword at boundary | `Missing(StructRole::Name, Identifier)` 一件。body は cascade しない |
| malformed name then name | maximal `Error(StructRole::Name)` 一件と same-slot retry |
| complete name without body starter | `Missing(StructRole::BodyIntroducer)` 一件。next word は outer-owned |
| malformed starter then real starter | body-introducer error 一件と same-slot retry |
| field lacks colon before reusable type | `Missing(StructRole::FieldColon, Colon)` 一件と same-position type retry |
| accepted colon at boundary | `Missing(StructRole::FieldType, TypeExpression)` 一件 |
| malformed Type primary reaches boundary | inner `Error(Type::Primary)` だけ。FieldType は cascade しない |
| separator before EOF | distinct incomplete field / closing-delimiter slot |
| outer-owned mismatched close | local close Missing。outer close は non-consuming |
| repeated tuple comma | missing tuple field type 一件の後に separator retry |

body / named-field / tuple-field / close row は no-cascade と one range = one recovery node =
one record を保つ。

## 8. boundary と state-restoration contract

root、indented canonical statement、braced block、With、Binding/Mod body、nested struct は同じ
adapter を共有する。normal / recovery / rollback exit は delimiter/stop state、
`TypeDelimitedOwner`、list/indent baseline、`inline`、`ml_arg`、`type_ml_arg`、positional fence、
scanner state、sink を restore する。findings fix は body-judge handoff と no-cascade ownership
を保つ。

## 9. Yulang2 divergences

Yulang3 は principal struct surface を保つが、Y2 whitespace type variable と companion は defer
する。bodyless `struct S;` を受け、bare EOF は incomplete とする。`InvalidToken` の代わりに
typed recovery を使い、`TypeVars` / synthetic `Separator` を作らず、`()` を fieldless とし、
Y2 type stop の代わりに approved standalone TypeExpression entry を使う。

## 10. known residual / deferred surface

accepted Struct-specific residual はない。section 2 の non-scope、特に declaration generic と
companion/derives semantics は deferred のままである。

## 11. implementation と regression fixture cross-reference

`crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_struct_statement_intro`, `parse_struct_declaration`,
`commit_struct_declaration`, `parse_struct_body_ast`,
`commit_struct_body_introducer`, `parse_struct_named_field_ast`,
`commit_struct_named_field`, `parse_struct_tuple_body_ast`,
`commit_struct_tuple_body`, `struct_outer_owned_mismatched_close_pending`。

fixture:
`struct_intro_commits_exact_keywords_before_binding_and_expression_fallback`,
`struct_header_recovery_hands_a_body_starter_forward_without_cascading`,
`struct_named_brace_fields_keep_their_own_layout_and_type_apply_boundary`,
`struct_named_fields_recover_colon_skeletons_without_cascading`,
`struct_named_indented_fields_keep_their_block_baseline_and_boundaries`,
`struct_tuple_fields_keep_type_apply_and_tuple_close_ownership_distinct`,
`struct_lists_leave_ambient_if_companions_for_the_statement_owner`。

