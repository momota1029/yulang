# 等式 `type` 宣言

## 1. 状態・根拠・最終照合

このページは `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の
Authoritative な追補「canonical `Statement` / root `Declaration` の type equality
declaration grammar」（19162–19676行）を要約する。規範節は `TD-G`、`TD-J`、
`TD-T`、`TD-R`（19286–19674行）である。

実装 gate は `f1681594`、`78d09b74`、`cf2ecd32`、`dec5b7cf`、`c23e870d`、
`c48086a5`、`263a99cc`、`be1d1dcb`、`8284e4fe` で完了した。追補の確定は
`4037c69e`。このページは `96d98da4` に対して最終照合した。

## 2. 対象と非対象

対象は visibility、`type`、名前、同一行の任意の declaration parameter、等式
introducer、必須の `TypeExpression` からなる equality form だけである。bodyless
nominal form、`impl` / `with:` companion、colon/brace の role-like body、derives、
associated type、alias/nominal の意味論はこの追補の対象外である。後続の nominal
追補が nominal form を加え、現在の `TypeDeclarationForm` は両 form を一つの
header の下に持つ。

## 3. BNF 相当の grammar

```text
TypeDeclaration :=
    [ VisibilityKw Gtype+ ]
    TypeKw Gtype+ TypeName
    [ DeclarationTypeParameterList ]
    Gtype* Equals Gtype-rhs
    RequiredTypeExpression(TypeDeclaration::Rhs)

VisibilityKw := MyKw | OurKw | PubKw
TypeName := Identifier
DeclarationTypeParameterList :=
    Gtype-param DeclarationTypeParameter
    { Gtype-param DeclarationTypeParameter }
DeclarationTypeParameter := Identifier | SigilIdentifier
Gtype+ := non-empty TypeContinuationTrivia(type_base)
Gtype* := empty or one TypeContinuationTrivia(type_base)
Gtype-rhs := empty or one TypeContinuationTrivia(type_base)
```

`TypeContinuationTrivia` は same-line trivia、または `type_base` より strictly
deeper な次行を持つ trivia を受ける。declaration parameter は same-line 限定である。

## 4. Judge・priority・owner boundary

exact `type`、または必要な continuation trivia 後の visibility prefix と exact `type`
が Type introduction を選ぶ。選択後は後続 slot が recovery しても header を cut
する。root と canonical `Statement` は同じ declaration shape を使い、header discovery
はここで止まり Type header fact を作らない。

lone exact `=` は header evidence である。`=` のない non-parameter type primary
は missing introducer 後に RHS として same-position retry できる。EOF、separator、
equal-or-shallower newline、ambient owner boundary は non-consuming である。RHS 前には
declaration indentation base と `Semicolon` / `With` stop を入れ、ambient-owner
boundary predicate を判定する。

## 5. byte-exact CST worked examples

```text
type Pair 'left 'right = ('left, 'right)
```

```text
TypeDeclaration 0..40
  TypeKw 0..4 "type"
  Trivia 4..5 " "
  Identifier 5..9 "Pair"
  DeclarationTypeParameterList 9..22
  Trivia 22..23 " "
  Equals 23..24 "="
  Trivia 24..25 " "
  TypeExpression 25..40
```

```text
type Result 'a = ;
```

```text
TypeDeclaration 0..17
  TypeKw 0..4 "type"
  Identifier 5..11 "Result"
  DeclarationTypeParameterList 11..14
  Equals 15..16 "="
  TypeExpression 17..17
    Missing(TypeDeclaration::Rhs, TypeExpression) 17..17
Semicolon 17..18 ";"
```

`type Id 'a 'a` では二つの sigil identifier が greedy parameter となり、reusable
RHS ではなく EOF の `Missing(TypeDeclaration::DefinitionIntroducer, Equals)` 一件になる。
`type Id 'a ('a)` が missing-`=` retry の対照例である。

## 6. parser 側 AST shape

現在の parser は equality を shared declaration の form として表す。

```rust
pub(crate) struct TypeDeclaration<'source> {
    visibility: Visibility,
    name: Recovered<WordSpan<'source>>,
    parameters: Vec<DeclarationTypeParameter<'source>>,
    derives: Vec<DerivesAttachment<'source>>,
    form: Recovered<TypeDeclarationForm<'source>>,
    range: Range<usize>,
}

pub(crate) enum TypeDeclarationForm<'source> {
    Nominal,
    Equality {
        equals: Recovered<Range<usize>>,
        rhs: Recovered<Box<TypeExpression<'source>>>,
    },
}
```

`derives` と `Nominal` は後続追加である。このページの対象は
`Complete(TypeDeclarationForm::Equality { .. })` とその recovered form である。

## 7. typed recovery table

| slot / condition | record と continuation |
| --- | --- |
| name が boundary で欠落 | zero-width `Missing(TypeDeclaration::Name, Identifier)` 一件。equality/RHS は cascade しない |
| malformed name 後に name | maximal `Error(TypeDeclaration::Name)` 一件と same-slot retry |
| reusable type 前で `=` 欠落 | zero-width `Missing(TypeDeclaration::DefinitionIntroducer, Equals)` と same-position RHS retry |
| malformed introducer が `=` / type に到達 | maximal introducer error 一件。追加 Missing なしで続行 |
| accepted/recovered `=` 後の RHS boundary | zero-width `Missing(TypeDeclaration::Rhs, TypeExpression)` 一件。boundary は外側 owner に残す |
| malformed RHS 後に type primary | existing `Error(Type::Primary, TypeExpression)` と same-slot retry |
| malformed RHS が boundary に到達 | inner Type error だけを残し、outer RHS Missing は cascade しない |

nested type slot は `TypeRole` を保持し、完全に absent な RHS primary だけが
declaration-owned `Rhs` role を使う。

## 8. boundary と state-restoration contract

gate は root / nested canonical statement、`Semicolon` / `With` boundary、
equal-or-shallower newline、ambient gap、active delimiter、malformed tail、rollback の
AST/direct parity を証明した。各 RHS exit は input、line state、stop set、indentation
baseline、delimiter state、expectation sink、TypeExpression-local state を restore する。

## 9. Yulang2 divergences

surface は Yulang2 の visibility spelling、exact `type`、whitespace parameter、exact
`=`、full RHS type を保つ。意図的な差は semantic `TypeAlias` でなく neutral
`TypeDeclaration` を使うこと、private default normalization、outer semicolon ownership、
empty `TypeVars` を作らないこと、typed recovery、declaration-local colon/brace stop を
作らないこと、現在の `_a` lexical classification、`$` / `&` type-reference atom を
新設しないことである。

## 10. known residual / deferred surface

`TD-R` に equality 固有の accepted residual はない。historical complete-header terminal
family は後続 nominal form に supersede され、genuine equality evidence と recovery は残る。
type semantics、companion tail、role-like body、docs/where attachment、HIR、resolver、formatter
はこの syntax contract の外である。

## 11. implementation と regression fixture cross-reference

`crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_type_statement_intro`、`parse_type_declaration_header_slots`、
`parse_type_declaration_shared_header_phase`、
`parse_type_declaration_definition_phase`、
`commit_type_declaration_header_slots`、`parse_type_declaration_rhs`、
`commit_type_declaration_rhs`、`parse_type_declaration`、
`commit_type_declaration`、`classify_type_declaration_form`。

fixture:
`type_declaration_header_slots_follow_td_r_name_and_equals_recovery`、
`type_declaration_td_r_worked_examples_are_lossless_and_byte_exact`、
`type_declaration_rhs_wiring_is_atomic_typed_and_state_balanced`。

