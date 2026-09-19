# 構文の内容モデル

このページは、各構文文脈に何を置けるかを調べるための主な入口である。
受理する`syntax-v0`の表層構文を、配置の観点から示す。
各構文ページは、その形式のBNF相当の生成規則を定める。
このページは生成規則を置き換えたり、統合したりしない。

## 権威と対象範囲

`syntax-v0`は、2026年9月17日のAuthoritativeな「Syntax freeze and vertical-implementation completion-policy amendment」が維持する受理構文と直接Rowan CSTの構造である。
この追補は、受理構文とrecoveryの責務を維持する。
生成規則とtopologyは、下記で引用するAuthoritativeな設計記録が定める。
実装、テスト、フィクスチャ、コミットは規範的な出典ではない。

次の一覧は、`syntax-v0`の配置を網羅して記録する。
詳細ページがまだない形式もある。
そうした項目は配置だけを記録する。
生成規則と直接CST配置の出典は、対応するAuthoritativeな設計記録である。
一覧項目があることは、詳細ページがあることを意味しない。

## 生成規則の読み方

構文ページの生成規則では、ページが個別の字句条件を定めない限り、次の記法を用いる。

| 記法 | 意味 |
| --- | --- |
| `A B` | `A`に続いて`B`を必ず置く |
| `[ A ]` | `A`を省略できる |
| `{ A }` | `A`を0回以上繰り返す |
| `A | B` | いずれか1つを選ぶ |
| `Name` | 同じページまたはリンク先の構文ページで定める非終端記号 |
| `<identifier>` | 字句上のプレースホルダー。受理するトークン形式は、その記法を使う生成規則が定める |
| `"keyword"`または句読点 | その位置で必要なソース上の表記 |

`trivia`、`layout`、`stop`、`separator`などのページ固有の記号は、その記号を導入するページで定める。

## 表層構文、直接CST、recovery

表層構文の内容モデルは、Authoritativeな受理済み有効形式を記録する。
直接CSTのモデルは、対応する構文の子要素をソース順に置く方法を記録する。
直接CSTのモデルは、表層構文の形式を増やさない。
このページ自体は規範的な権威ではない。

recoveryは別の参照層である。
`Missing`、raw `Error`、structured `Invalid`は、不正な入力に対して保持するrecovery構造を示す。
これらは不正な文字列を受理済みの選択肢にしない。
[recoveryの構造](recovery-error-invalid-topology.md)と[source rootおよびdiagnosticの責務](source-root-and-diagnostics.md)を参照する。

## 入口となる文脈

このリファレンスは、次の入口文脈を扱う。

```text
Root
  ルートの式または宣言の子
  ルート専用の演算子定義: OperatorHeader、式本体

Nested statement owner
  Statement
    入れ子になった式または宣言の子

Expression
  Pattern
  TypeExpression
```

これは配置図であり、ルートの生成規則を置き換えるものではない。
ルートの式と宣言は`Root`の直接の子である。
入れ子になったstatement ownerは`Statement`の親を加える。
statement列のラッパーは加えない。

## 内容モデルの一覧

### Statement列と宣言

直接CSTの列で、`R`は直接の`Root`配置を、`S`は入れ子になった`Statement`の下への直接配置を表す。
「ソース順」は、生成規則のリテラルトークンと`trivia`を含む。
以下の名前付きの子は構造上の子を列挙する。

| 文脈と受理する形式 | 表層構文の子生成規則と境界 | 直接CSTの親 | 直接CSTの順序付き直接子と多重度 | 権威 |
| --- | --- | --- | --- | --- |
| Rootまたは入れ子になったStatement: 式statement | [operator chain](../expressions/operator-chain.md)。終端継続 | R: `Root`。S: `Statement` | `OperatorChain`。ちょうど1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § “Surface grammar” in dynamic-operator addendum (4375–5012) |
| Rootまたは入れ子になったStatement: bindingまたはuse | [binding and use](../statements/binding-use.md)。statement境界 | R: `Root`。S: `Statement` | `BindingStatement`（可視性、`Pattern`、任意の本体）または`UseDeclaration`（use tree）。ちょうど1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § “canonical Statement binding / use declaration extension” (11086–11623) and § “Complete use declaration grammar and projection” (933–1924) |
| Rootまたは入れ子になったStatement: nominalまたはequalityの`type` | [nominal](../statements/bare-nominal-type.md)、[equality](../statements/equality-type.md) | R: `Root`。S: `Statement` | `TypeDeclaration`。header、任意のattachment、選んだ形式。ちょうど1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ `TND-G` and `TD-G` |
| Rootまたは入れ子になったStatement: `mod`、`struct`、単独の`impl`、または`cast` | [mod](../statements/mod-declaration.md)、[struct](../statements/struct-declaration.md)、[impl](../statements/impl-shell.md)、[cast](../statements/cast-declaration.md) | R: `Root`。S: `Statement` | 対応する宣言ノード。header、次にソース順の本体または形式の子。ちょうど1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ “canonical Statement / root Declaration mod declaration extension”, `SD-G`, `IMD-G`, `CAST-G` |
| 対応する宣言host: `derives` attachment | [`derives`](../statements/derives-attachment.md)。下記の正確な位置 | host宣言 | `DerivesClause`の子はソース順に出現する。受け入れたattachment pointごとに0個以上。`Statement`の子にはならない | shared clause grammar: `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ `DRV-G`, `DRV-J`。後続のowner配置は下記の出典を参照 |
| `StructDeclaration`: declaration companion | header derivesの後で本体の前、またはactual-completeなbraced / tuple closeとtrailing derivesの後にある、exact contextual `with` | `StructDeclaration` | いずれかの許可位置に`DeclarationCompanion`の子を1個置く。`WithKw`、actualまたはrecovered introducer、次にinlineの直接の`Statement` 1個または直接の`DerivesClause` 1個以上、直接item childを持つ`DeclarationCompanionIndentedBody`、またはbraceと直接のitem childをソース順に置く。宣言ごとに最大1個 | `notes/design/2026-08-30-declaration-companion-with-addendum.md` §§ `DC-G`, 6 “Owner and attachment matrix”, 8.2 “CST” |
| `TypeDeclaration`: declaration companion | header derivesとattached-`impl` probeの後、またはequality RHSとtrailing derivesの後にある、exact contextual `with` | `TypeDeclaration` | いずれかの許可位置に`DeclarationCompanion`の子を1個置く。`WithKw`、actualまたはrecovered introducer、次にinlineの直接の`Statement` 1個または直接の`DerivesClause` 1個以上、直接item childを持つ`DeclarationCompanionIndentedBody`、またはbraceと直接item childをソース順に置く。宣言ごとに最大1個 | `notes/design/2026-08-30-declaration-companion-with-addendum.md` §§ `DC-G`, 6 “Owner and attachment matrix”, 8.2 “CST” |
| `EnumDeclaration`: declaration companion | header derivesの後、actual-completeなbraced closeとtrailing derivesの後、またはequals-inline variant列の後にある、exact contextual `with` | `EnumDeclaration` | 許可位置に`DeclarationCompanion`の子を1個置く。`WithKw`、actualまたはrecovered introducer、次にinlineの直接の`Statement` 1個または直接の`DerivesClause` 1個以上、直接item childを持つ`DeclarationCompanionIndentedBody`、またはbraceと直接item childをソース順に置く。宣言ごとに最大1個 | `notes/design/2026-08-30-declaration-companion-with-addendum.md` §§ `DC-G`, 6 “Owner and attachment matrix”, 8.2 “CST” |
| `ErrorDeclaration`: declaration companion | header derivesの後、またはactual-completeなbraced closeとtrailing derivesの後にある、exact contextual `with`。equals-inline companion位置はない | `ErrorDeclaration` | いずれかの許可位置に`DeclarationCompanion`の子を1個置く。`WithKw`、actualまたはrecovered introducer、次にinlineの直接の`Statement` 1個または直接の`DerivesClause` 1個以上、直接item childを持つ`DeclarationCompanionIndentedBody`、またはbraceと直接item childをソース順に置く。宣言ごとに最大1個 | `notes/design/2026-08-30-declaration-companion-with-addendum.md` §§ `DC-G`, 6 “Owner and attachment matrix”, 8.2 “CST” |
| `ActDeclaration`: declaration companion | Headとheader derivesの後、またはSourceとheader derivesの後にある、exact contextual `with`。companionを受理するとActの継続は終わる | `ActDeclaration` | 選んだpost-Headまたはpost-Source位置に`DeclarationCompanion`の子を1個置く。`WithKw`、actualまたはrecovered introducer、次にinlineの直接の`Statement` 1個または直接の`DerivesClause` 1個以上、直接item childを持つ`DeclarationCompanionIndentedBody`、またはbraceと直接item childをソース順に置く。宣言ごとに最大1個 | `notes/design/2026-08-30-declaration-companion-with-addendum.md` §§ `DC-G`, 6 “Owner and attachment matrix”, 8.2 “CST” |
| `type`宣言: 付加した`impl` | type header継続。type宣言境界 | `TypeDeclaration` | header、任意のderives、`ImplKw`、headの`TypeExpression`、任意の説明、本体。最大1個。入れ子の`ImplDeclaration`は置かない | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ `TAI-G`, “AST / direct-CST shape” |
| Rootのみ: 演算子定義 | 演算子headerと式本体の境界 | `Root` | `Root > OperatorHeader, OperatorChain`。`OperatorHeader`、次に兄弟の`OperatorChain`。headerと本体の組は1組。`Statement`にはならない | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ “Root statement loop”, “Operator definition body full-only continuation” |
| Rootまたは入れ子になったStatement: `role`、`act`、`enum`、`error`、または`for` | 宣言またはstatement固有の本体境界 | R: `Root`。S: `Statement` | 対応する`RoleDeclaration`、`ActDeclaration`、`EnumDeclaration`、`ErrorDeclaration`、または`ForStatement`。header、次に直接の形式または本体の子。ちょうど1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ `RLD-G`, `ACT-G`, `ENUM-G`, `ERROR-G`, `FOR-G` and their “AST / direct-CST shape” sections |
| Rootまたは入れ子になったStatement: Yumarkを持つdoc-comment宣言 | document envelopeとYumark blockの境界 | R: `Root`。S: `Statement` | `DocCommentDeclaration`。markerと`YmDoc`内容をソース順に置く。ちょうど1個 | `notes/design/2026-09-01-doc-comment-yumark-addendum.md` §§ 2 “Envelope and dispatch”, 8 “AST, CST, and recovery vocabulary” |

`derives`のhostと位置は正確に定める。
`StructDeclaration`は共有headerの後で本体の前にheaderを置ける。
trailingはactual-completeなbracedまたはtuple本体の後にだけ置ける。
`TypeDeclaration`はheaderの後で形式選択の前にheaderを置ける。
trailingはequality RHSの後に置ける。
これらのStructとTypeの位置は`DRV-G`/`DRV-J`を使う。
`EnumDeclaration`と`ErrorDeclaration`はheaderを置ける。
trailingはactual-completeなbraced closeの後にだけ置ける。
owner固有の出典はarchitecture recordのそれぞれの“Derives composition”節と、*Direct Enum/Error companion trailing-close amendment*の§ “Decision”である。
`ActDeclaration`はCompleteなHeadの後と、actualなSourceがCompleteな場合のSource後にheader derivesを置ける。
trailingはactual-completeなbraced closeの後にだけ置ける。
owner固有の出典は`ACTDRV-G`/`ACTDRV-J`である。
`Role`、`Impl`、`Cast`、`Mod`、binding、use、演算子定義は`derives`のhostではない。

### Expression

| 文脈と受理する形式 | 表層構文の子生成規則と境界 | 直接CSTの親 | 直接CSTの順序付き直接子と多重度 | 権威 |
| --- | --- | --- | --- | --- |
| Expression | [operator chain](../expressions/operator-chain.md)。終端継続 | R: `Root`。S: `Statement` | `OperatorChain`。1個。そのitemはソース順を保つ | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § “Surface grammar” (dynamic-operator addendum) |
| Expression primary: parenthesized form | [parenthesized expressions](../expressions/parenthesized-expression.md)。parenthesesとseparator | `OperatorChain` | `ParenthesizedExpression`。0個以上の直接の`OperatorChain`要素を含む。primaryは最大1個 | Parenthesized-expression authority、`notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ 4103–4355、layout separator authority |
| 完了したchain: call、field、path、ML、index、またはprojection | [fixed tails](../expressions/call-field-path-tails.md)、[index/projection](../expressions/index-projection-tails.md) | `OperatorChain` | 対応するtailノードと、その直接のargumentまたはitem chainをソース順に置く。継続は0個以上 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ “Call/Field/Path/ML fixed-tail addendum”, “IndexTail/ProjectionTail fixed-tail addendum” |
| 完了したchain: 型注釈 | annotation継続境界 | `OperatorChain` | `TypeAnnotationTail`。annotation token、次に`TypeExpression`。終端でないtailは0個以上 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § “Surface grammar” (`TypeAnnotationContinuation`) |
| 完了したchain: colon application、assignment、または`with`本体 | [colon](../expressions/colon-application.md)、[assignment](../expressions/assignment-tail.md)、[`with`](../expressions/with-body-tail.md) | `OperatorChain` | 対応する終端tailと直接の本体またはargumentの子。終端継続は0個または1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ “Valid grammar” (colon), `WithBodyTail` addendum, and assignment direct-inline contract |
| Expression primary: `if`、braced block、`case`、または`catch` | [if](../expressions/if-expression.md)、[block](../expressions/braced-statement-block.md)、[case/catch](../expressions/case-catch.md) | `OperatorChain` | 対応するprimaryノード。直接のarmまたはstatementの子をソース順に置く。value slotのprimaryは最大1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ NUD-primary `if` (5469–6065), braced block (6067–6627), `case`/`catch` (7243–8017) |
| Expression primary: stringまたはrule literal | literal delimiter境界 | `OperatorChain` | `StringLiteral`は`StringStart`、`StringText`/`StringEscape`/`StringInterpolation`の内容、`StringEnd`をこの順に置く。`RuleLiteral`は`RuleLiteralStart`、`RuleLiteralText`/`RuleLiteralInterpolation`/`RuleLazyCapture`の内容、`RuleLiteralEnd`をこの順に置く。いずれもvalueは最大1個 | `notes/design/2026-09-05-direct-literal-cone-addendum.md` §§ 2 “Exact grammar and lexical ownership”, 3 “Proposed CST and public surface”, 6 “Dispatch and successor acquisition” |
| Expression primary: contextual rule expression | exact `rule RuleIntroducerTrivia {` | `OperatorChain` | `OperatorChain > RuleExpression`。`RuleExpression`は`RuleKw`、source trivia、次に`RuleBody`をソース順に置く。primaryはちょうど1個 | `notes/design/2026-09-05-direct-literal-cone-addendum.md` §§ 2 “Exact surface grammar”, 6 “Dispatch and successor acquisition”; `LC-8` |

### Pattern

| 文脈と受理する形式 | 表層構文の子生成規則と境界 | 直接CSTの親 | 直接CSTの順序付き直接子と多重度 | 権威 |
| --- | --- | --- | --- | --- |
| Pattern: core、parenthesized、list、またはrecord primary | [core](../patterns/pattern-core.md)、[list](../patterns/list-pattern.md)、[record](../patterns/record-pattern.md) | `Pattern` | 対応するprimaryノード。直接のpatternまたはitemの子をソース順に置く。`Pattern`ごとにprimaryは1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ Pattern addendum (6629–7242), ListPattern (8019–8612), RecordPattern (8613–9312) |
| Pattern primary: string literal | Pattern literal境界の3個以上のquote run | `Pattern` | `StringLiteral`は`StringStart`、`StringText`/`StringEscape`/`StringInterpolation`の内容、`StringEnd`をこの順に置く。primaryはちょうど1個 | `notes/design/2026-09-05-direct-literal-cone-addendum.md` §§ 2 “Exact grammar and lexical ownership”, 3 “Proposed CST and public surface”, 6 “Dispatch and successor acquisition”; `LC-5` |
| Pattern primary: rule literal | 1個のquoteによるPattern literal opener | `Pattern` | `RuleLiteral`は`RuleLiteralStart`、`RuleLiteralText`/`RuleLiteralInterpolation`/`RuleLazyCapture`の内容、`RuleLiteralEnd`をこの順に置く。primaryはちょうど1個 | `notes/design/2026-09-05-direct-literal-cone-addendum.md` §§ 2 “Exact grammar and lexical ownership”, 3 “Proposed CST and public surface”, 6 “Dispatch and successor acquisition”; `LC-5` |
| Pattern primary: contextual rule expression | exact `rule RuleIntroducerTrivia {` | `Pattern` | `RuleExpression`は`RuleKw`、source trivia、次に`RuleBody`をソース順に置く。primaryはちょうど1個 | `notes/design/2026-09-05-direct-literal-cone-addendum.md` §§ 2 “Exact grammar and lexical ownership”, 3 “Proposed CST and public surface”, 6 “Dispatch and successor acquisition”; `LC-5`、`LC-8` |
| 完了したPattern: 末尾の型注釈 | [pattern annotation](../patterns/type-annotation.md)。colonと`TypeExpression`の境界 | `Pattern` | `PatternTypeAnnotation`。colon、次に`TypeExpression`。終端注釈は0個または1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § `PTA-G` |

### TypeExpression

| 文脈と受理する形式 | 表層構文の子生成規則と境界 | 直接CSTの親 | 直接CSTの順序付き直接子と多重度 | 権威 |
| --- | --- | --- | --- | --- |
| TypeExpression: core atom、path、call、application、arrow、group | [core](../types/type-expression-core.md)。type delimiterとarrow境界 | `TypeExpression` | primary tokenまたはnode、次にソース順のtightまたはapply tail、次に任意の`TypeArrowTail`。各tailは0個以上。arrowは0個または1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ “Authoritative surface grammar”, “CST vocabulary and shape” (12155–12866) |
| Type primary: named record、`forall`、effect row、またはpolymorphic variant | [record](../types/named-record-type.md)、[`forall`](../types/forall-type.md)、[effect row](../types/effect-row-type.md)、[variant](../types/polymorphic-variant-type.md) | `TypeExpression` | 対応するprimaryノードと、その直接のfield、binder、item、tagの子をソース順に置く。primaryは1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ NamedRecordType (12867–13429), Forall (13431–13980), EffectRowType (13982–14525), polymorphic-variant primary (14527–15233) |
| TypeExpression: 先頭のbracket row | [bracket row](../types/bracket-row-grammar.md)。row境界 | `TypeExpression` | `BracketRow`、次にchain trivia、次に必須の通常type head。先頭のrowは0個または1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § `BR-G` |
| `TypeArrowTail`: 必須arrowの前に置く末尾のbracket row | [bracket row](../types/bracket-row-grammar.md)。rowとarrowの境界 | `TypeArrowTail` | 任意の`BracketRow`、chain trivia、arrow、RHSの`TypeExpression`。rowは0個または1個。arrowとRHSのslotはそれぞれちょうど1個 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § `BR-G` |

構文ページが共通規則へ委譲する場合は、[layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md)、[positional fence](../cross-cutting/positional-fence.md)、[ambient statement-owner boundary](../cross-cutting/ambient-statement-owner-boundary.md)を参照する。
