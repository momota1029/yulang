# Bare nominal `type` declaration

## 1. Status / authoritative source / last verified commit

- Status: Authoritative、ユーザ承認済み（2026-08-26）。
- 正本: `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の
  `canonical Statement / root Declarationのbare nominal type declaration grammar` 節、現行行19677–20277。
  grammarは`TND-G`、judgeは`TND-J`、TypeExpression / ASOB compositionは`TND-T`、typed recoveryは`TND-R`が正本である。
- 設計確定commit: `9cee84e5`。
- 実装series: Gate 1 `538af5d8`、Gate 2 `fa9a3a11`、Gate 3 `d88694bd`、Gate 4 `f42a5929`、Gate 5 `b3b07727`、Gate 6 `26e5b030`、Gate 8 `ff215ce9`、Gate 9 `fec43734`。
  Gate 7はread-only equality-fixture auditであり、reachable historyには独立した`bare-nominal-type Gate 7` commitがない。Gate 9のclosing messageが9 gates全体の完了を記録する。
- Last verified: `4b8c4c91`。以下のimplementation symbolとfixture名を現行treeで照合した。

## 2. Scope and non-scope

このページは、shared `TypeDeclaration` headerの後で、RHSを持たないbare nominal formを選ぶ規則を扱う。surfaceはoptional visibility、exact `type`、mandatory raw name、same-line declaration type parametersである。

対象はnominal/equalityのpriority、AST/direct-CST shape、typed recovery、ASOB・layout・separator ownership、rootとnested canonical Statementで同じdeclaration childを使うことだけである。

このTND addendumは`impl` / `with` / colon / brace role-like body、associated type、constructor / module registration、nominal identity、visibility semantics、HIR lowering、resolver、formatterを定義しない。pre/post-body `derives`もこのaddendumのscope外であり、現在の`derives` attachmentは後続のshared derives addendumが別に扱う。

## 3. BNF-equivalent grammar

```text
TypeDeclaration :=
    TypeDeclarationHeader TypeDeclarationForm

TypeDeclarationHeader :=
    [ VisibilityKw Gtype+ ]
    TypeKw Gtype+ TypeName
    [ DeclarationTypeParameterList ]

TypeDeclarationForm :=
    NominalTypeDeclarationEnd
  | EqualityTypeDeclarationDefinition

NominalTypeDeclarationEnd :=
    Gtype-terminal NominalStatementBoundary
  | MaximalStrictlyDeeperTrailingTriviaBeforeEOF EOF

EqualityTypeDeclarationDefinition :=
    Gtype* Equals Gtype-rhs
    RequiredTypeExpression(TypeDeclaration::Rhs)

NominalStatementBoundary :=
    EOF
  | OuterStatementSemicolon
  | EqualOrShallowerStatementNewline(type_base)
  | BracedStatementSequenceNewline
  | CatchArmSequenceNewlineThroughInlineCanonicalStatement
  | ActiveOuterFixedStatementBoundary
  | AmbientStatementOwnerBoundary

ActiveOuterFixedStatementBoundary :=
    ActiveStop(Comma)
  | ActiveStop(RightParenthesis)
  | ActiveStop(RightBracket)
  | ActiveStop(RightBrace)
```

`VisibilityKw`、type parameter、`Gtype*`、`Gtype-rhs`、`type_base`はequality `type` declarationのshared header / RHS grammarを再利用する。`NominalStatementBoundary`はsource childではなくowner handoff resultである。

## 4. Judge / priority / owner boundary

form judgeはcomplete headerの直後にsink-freeで動き、original trivia gapとfollowing tokenだけをprobeしてexact rollbackする。arbitrary-distanceの`=`探索やfull TypeExpressionのspeculative parseはしない。

priorityは次の順である。

1. NameがIncompleteならnominal authorityを与えない。exact `=` evidenceがあればequality recoveryへ、それ以外はshared header recoveryを維持する。
2. complete headerの直後でoriginal gapがambient ownerにclaimされず、accepted `Gtype*`の後にexact lone `=`があればEqualityを選ぶ。local exact `=`はbraced/Catch newlineのterminal inferenceより先に勝つ。
3. complete headerがEOF、outer semicolon、equal-or-shallower newline、typed braced/Catch newline、active comma/right delimiter、ambient owner、またはstrictly-deeper triviaの後のEOFへ達すればNominalを選ぶ。boundary bytesはconsumeしない。
4. それ以外はshared `DefinitionIntroducer` recoveryへ渡す。reusable TypePrimaryならzero-width Missing `=`とsame-position RHS retry、malformed runならmaximal Errorとselected retryを使う。

semicolonはouter canonical Statement sequenceが所有する。active fixed boundaryはincoming stopがactiveな`Comma | RightParenthesis | RightBracket | RightBrace`だけであり、spellingだけでboundaryにしない。

## 5. Byte-exact CST worked examples

### Complete nominal

Source:

```text
type Point
```

```text
TypeDeclaration 0..10
  TypeKw 0..4 "type"
  Trivia 4..5 " "
  Identifier 5..10 "Point"
```

ASTは`name = Complete(Point)`、zero parameters、`form = Complete(Nominal)`、range `0..10`となる。Missing / Error / TypeExpressionは作らない。

### Visibility and parameter with outer semicolon

Source:

```text
pub type Phantom 'a;
```

```text
TypeDeclaration 0..19
  PubKw 0..3 "pub"
  Trivia 3..4 " "
  TypeKw 4..8 "type"
  Trivia 8..9 " "
  Identifier 9..16 "Phantom"
  DeclarationTypeParameterList 16..19
    Trivia 16..17 " "
    SigilIdentifier 17..19 "'a"
Semicolon 19..20 ";"
```

semicolonは`TypeDeclaration`のchildでもrangeでもなく、outer statement separatorである。

### Nominal before the next root statement

Source:

```text
type value
our x = 1
```

first `TypeDeclaration`は`0..10`でcloseし、newline `10..11`はouter root sequenceへ返る。`our x = 1`は`11..20`のseparate Bindingであり、first declarationにMissing `=`やRHSは作らない。

## 6. Parser-side AST shape

現行`declaration.rs`のactual shapeは次である。`derives` fieldは後続のshared derives addendumによるattachmentであり、nominal/equality form choiceは`form`が表す。

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

valid nominalにはdummy `equals = Incomplete`やempty RHSを入れない。`form = Incomplete`は、name incompleteまたはmalformed `DefinitionIntroducer` runがterminal boundaryへ達し、nominal/equalityのpositive evidenceがない場合に限る。

valid nominalのCSTはexisting `TypeDeclaration` nodeを使い、`NominalTypeDeclaration`、empty body、empty RHS、nominal-only wrapper nodeを追加しない。

## 7. Typed recovery table

TND-Rの主要なslot transitionを要約する。Name、`DefinitionIntroducer`、Rhsはshared type declaration recovery roleを使い、nominal専用recovery roleはない。

| Input state | Result / recovery | Ownership or retry |
| --- | --- | --- |
| complete header + EOF / `;` / terminal newline / ambient owner / active fixed boundary | `Complete(Nominal)`、zero recovery | boundaryをnon-consumeでouter ownerへ返す。strictly-deeper trivia + EOFだけはtriviaをdeclarationが所有する。 |
| complete header + exact `=` | `Complete(Equality)` | shared mandatory RHSへcutする。 |
| complete header + reusable non-parameter TypePrimary、`=`なし | one zero-width Missing `DefinitionIntroducer`、`Complete(Equality)` | same positionからRHS retry。 |
| malformed post-header run + exact `=`またはreusable TypePrimary | one maximal Error `DefinitionIntroducer`、`Complete(Equality)` | actual `=`をconsume、またはsame-position RHS retry。 |
| malformed post-header run + terminal boundary | one maximal Error `DefinitionIntroducer`、form Incomplete | Nominalへupgradeせず、additional Missingなし。 |
| `type` + terminal boundary | one Missing Name、form Incomplete | nominal / equals / RHS Missingをcascadeしない。 |
| malformed name + valid raw name + terminal boundary | one maximal Error Name、retried name Complete、`Complete(Nominal)` | Name Missingを重ねない。 |
| `type Point = ;` | `Complete(Equality)`、one Missing Rhs | Nominal fallbackを試さない。 |

cardinality規約はone source range = one recovery node = one recordである。同一terminal causeに後続slotのMissingをcascadeしない。ASTとdirect-CSTは同じform decision、Complete/Incomplete slot、source range、recovery recordを持つ。

## 8. Boundary/state-restoration contract

nominal pathはTypeExpression RHS slotを開かない。exact `=`またはequality recoveryを選んだ場合だけshared TD-T RHS episodeを再利用する。

form judgeはroot、indented、braced、inline canonical Statement、depth-2+ ambient / If companionでprobeしても、input、line state、sink、ambient / If、delimiter、stop、indentation、type owner、ML、positional fenceをentry depthへexact restoreする。Gate 6のboundary matrixはEOF、semicolon、comma、各active right delimiter、equal-or-shallower newline、braced newline、Catch arm newline、strictly-deeper continuation / EOFを固定した。

## 9. Yulang2 divergences

- Y2はsame `TypeDecl`をsilent closeし、missing-equalsとのtyped distinctionを持たなかった。Y3はterminal owner boundaryをpositive Nominal evidenceとし、malformed post-header bytesをnominalへfoldしない。
- Y3はroot / indentedではtype-base disciplineを保ち、braced Statement sequenceではindent非依存のtyped newline owner queryを使う。
- Y2のrole-like bodyはsemicolonをTypeDecl内でconsumeした。Y3ではsemicolonはouter statement separatorである。
- Y3はalways-present empty `TypeVars`、empty body、nominal-only CST wrapperを作らない。
- `Nominal`はsyntax-only form labelであり、nominal identity、constructor registration、opaque / alias meaning、default visibilityをparserが決めない。

## 10. Known residual / deferred surface

TND addendumはbare nominal form固有のknown residualを宣言していない。

このaddendumのdeferred surfaceはcompanion `impl` / `with`、colon / brace role-like body、`struct self`、associated-type owner、constructor / module registration、nominal semantics、HIR / resolver / formatter、kind / bound / default / `where`を含む。後続addendumで実装済みのsurface（たとえばshared `derives` attachmentやstandalone `impl` shell）は、このbare-nominal form decisionの一部としては定義しない。

## 11. Implementation functions and regression fixtures

Implementation: `crates/yu-syntax/src/grammar/declaration.rs`。

- `recognize_type_statement_intro`
- `parse_type_declaration_header_slots` / `commit_type_declaration_header_slots`
- `parse_type_declaration` / `commit_type_declaration`
- `classify_type_declaration_form`
- `type_declaration_terminal_boundary_pending`
- `type_declaration_active_fixed_statement_boundary_pending`

Regression fixtures:

- `type_declaration_form_judge_follows_tnd_j_and_restores_every_probe_state`
- `type_declaration_form_aware_ast_construction_reuses_tnd_j_once`
- `type_declaration_form_aware_direct_cst_is_byte_exact_and_parity_checked`
- `type_declaration_form_aware_tnd_r_recovery_matrix_is_complete_and_non_cascading`
- `type_declaration_form_aware_boundary_matrix_restores_deep_parser_state`
- `nominal_type_declaration_final_public_boundary_matrix_preserves_ast_direct_parity`
- `type_declaration_scope_gate_keeps_deferred_yulang2_family_surfaces_outside_the_grammar`
