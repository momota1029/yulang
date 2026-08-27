# standalone `cast` declaration

## 1. Status、正本、最終確認

このページは、`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`
21646–22774行のAuthoritativeなstandalone cast declaration追補、`CAST-G`、
`CAST-J`、`CAST-T`、`CAST-R`を要約する。closing signatureには、査読・確定と
ユーザ承認までに11巡の独立レビューを経たことが記録されている。

13個のimplementation sliceは`3d7154eb`、`003cdc9a`、`bd96837d`、
`d3778e13`、`0da2d26e`、`43abd938`、`fe67f4eb`、`f79df17f`、
`b6b4f5ba`、`0c5c4af9`、`e3cffdf1`、`372af45e`、`dd1505f4`でlandした。
Gate 3bは、error recoveryしたnested Pattern closeの後にouter PatternがCast target
colonをannotationとして取れてしまうcomposition gapを見つけ、narrow opt-in policy
`recovered_primary_tail_stops`で直した。このページは`a00b8c74`に対して確認した。

## 2. Scopeとnon-scope

standalone Castはoptional visibility、1個のparenthesized canonical Pattern、mandatory
colonとfull TypeExpression target、bodyless semicolonまたはexact equals後のinline /
strictly-deeper indented bodyを持つroot Declaration兼nested Statementである。

本追補はtyped recovery、AST/direct-CST parity、root/nested shared dispatch、source-leading
header discoveryをfactなしで止めることを扱う。rule registration、source/target extraction、
conversion application、semantic validation、downstream loweringやanalysisは扱わない。

## 3. BNF-equivalent grammar

```text
CastDeclaration := [ VisibilityKw Gcast+ ] CastKw Gcast-pattern CastPatternGroup Gcast-target CastTarget Gcast-form CastForm
CastPatternGroup := RecoveredLParen(Cast::PatternIntroducer) Gcast-delimited* RequiredPatternWithPolicy(Cast::Pattern) Gcast-delimited* RecoveredRParen(CastPattern)
CastTarget := RecoveredTargetColon(Cast::TargetIntroducer) Gcast-type RequiredTypeExpression(Cast::TargetType)
CastForm := BodylessSemicolon | DefinitionEquals CastDefinitionBody
CastDefinitionBody := Gcast-inline RequiredOperatorChain(Cast::Body) | IndentedStatementBlock(item-role := Cast::IndentedStatement)
VisibilityKw := MyKw | OurKw | PubKw
CastKw := exact maximal word "cast"
```

`Gcast-indent`はstrictly-deeper continuation triviaであり、existing
`IndentedStatementBlock`のopening prefixとして所有される。Pattern policyはprimaryを
acceptする前だけ`Colon | Equal`を使い、accept後のordinary Pattern annotationとnested syntaxは
それぞれのownerに残す。

## 4. Judge、priority、owner boundary

statement positionのexact contextual `cast`だけ、bareまたは`my`、`our`、`pub`と
declaration-continuing triviaの後ならCast introになる。`casting`、`castaway`、intro以外の
word positionはsplitしない。real intro recognitionの順位はImplの後、Bindingの前である。

Cast groupはcanonical Patternをちょうど1個だけ所有し、ParenthesizedPatternのtuple/list wrapperではない。
actual `(`だけがCast-local delimiter frameを作り、missing openerはframeを合成しない。delimiter-stack topで
Cast-local `)`とouter-owned / unowned `)`を分け、後者はnon-consuming boundaryにする。target colonは
scoped outer `Equal`、`Semicolon`、conditional `Newline` stopを持つfull TypeExpression episodeを所有する。

exact `;`はbodyless formへcutする。exact `=`はdefinition formへcutし、equals後の1個のtrivia runで
inline `OperatorChain`かexisting strictly-deeper indented statement blockを選ぶ。inline expressionの後のbraceは
Cast body openerではない。

## 5. Byte-exact CST worked examples

追補には、次のsourceとrange treeが直接載っている。

```text
cast(x: A): B;
```

design 22139–22163行は`CastDeclaration 0..14`、`CastPattern 4..10`、
`Pattern 5..9`、`CastTarget 10..13`、Cast-owned `Semicolon 13..14`を与える。

```text
pub cast(x: A): B = x
```

design 22165–22189行は`CastDeclaration 0..21`、`CastPattern 8..14`、
`CastTarget 14..17`、`Equals 18..19`、`CastBody 19..21`、inline
`OperatorChain 20..21`を与える。

```text
pub cast(x: int): user_id = user_id { raw: x }
```

design 22192–22234行は`CastDeclaration 0..46`、`CastBody 27..46`、inline
`OperatorChain 28..46`を与える。その`MlArgument 36..46`はordinary
`BracedStatementBlockExpression 36..46`を含むため、braceはCast form selectionではなく
inline expressionに所有される。

```text
cast(x: A): B =
  x
```

design 22240–22259行は`CastDeclaration 0..19`、`Equals 14..15`、
`CastBody 15..19`、`IndentedStatementBlock 15..19`を与える。blockのfirst childは
`Trivia 15..18`で、その後が`Statement 18..19`になる。opening triviaは`CastBody`の
siblingではなくblock rangeの中にある。

## 6. Parser-side AST shape

`CastDeclaration`は`visibility`、recovered `pattern`、recovered `target`、recovered
`form`、source rangeを持つ。`CastPattern`はrecovered `open`、1個のrecovered boxed
`Pattern` value、recovered `close`、rangeを持つ。`CastTarget`も同様にrecovered colon、
1個のrecovered boxed `TypeExpression`、rangeを持つ。

`CastForm`は`Bodyless { semicolon }`か`Definition { equals, body, range }`であり、
`CastBody`は`Inline { expression: OperatorChain }`か`Indented { block: IndentedStatementBlock }`である。これは
`crates/yu-syntax/src/grammar/declaration.rs`の実際の型であり、`BindingBody`やsynthetic
separatorを代用しない。

## 7. Typed recovery table

| condition | recoveryとcontinuation |
| --- | --- |
| exact intro at EOF/owner boundary | `Missing(CastRole::PatternIntroducer)`を1個だけ置き、downstream slotへcascadeしない |
| missing/malformed opener | `CastRole::PatternIntroducer`のMissing/Errorを1個置き、same-position Pattern retryまたはpunctuation/boundary handoffへ進む |
| mandatory Pattern failure | nested Pattern recoveryはown roleを保ち、valid retryはsame slotをcompleteにする |
| Cast-local vs outer `)` | actual Cast-local current-top closeだけconsumeし、outer/unowned closeはnon-consuming |
| missing/malformed close | closing-delimiter Missing/Errorを1個置き、evidenceがあればtarget-colon same-position retryを行う |
| missing/malformed target colon | `CastRole::TargetIntroducer`のMissing/Errorを1個置き、same-position TypeExpressionまたはform-starter retryへ進む |
| target TypeExpression failure | nested Type recoveryとsame-slot retryを行い、`=`/`;`またはouter boundaryはform/ownerに残す |
| missing/malformed form starter | `CastRole::BodyIntroducer`のMissing/Errorを1個置き、actual `;`または`=`でform retryする |
| missing/malformed body | `CastRole::Body`のMissing/Errorを1個置き、indented item failureは`CastRole::IndentedStatement`に残す |

invariantは、accepted Castごとにdeclaration nodeが1個、recovery rangeごとにrecovery nodeと
committed recordが1個、same-cause downstream Missing cascadeがないことである。nested Pattern、
TypeExpression、Expression recoveryはCast recoveryへrelabelもduplicateもしない。

## 8. Boundaryとstate-restoration contract

promotion前のGate 7はisolated adapterをroot、indented、braced、inline ambient boundaryで確認し、
depth-2+ ambient/If state、every fixed terminal boundary、local/outer parentheses、normal/recovery/
rollback exitを含めた。input/line/sink、ambient/If、delimiter/stop、indentation、Pattern layout、
expression-type owner、ML、positional fence、TypeExpression episode depthがexact restoreされることを要求する。

Gate 8はこのcontractをreal root/canonical-statement dispatchで再実行し、Expressionとsupported
statement/declaration kindを含むCast indented bodyも通した。Gate 3bのopt-in tail-stop fixはopt inしない
callerを変えない。

## 9. Yulang2 divergences

surface spellingは`yulang2-oracle` parserと揃える。optional visibility、1個のPattern group、colonと
full target type、semicolonまたはequals bodyである。contextual-word handlingもdivergenceではなくparityで、
declaration-intro position以外の`cast`はordinary identifierのままである。

Yulang3はYulang2のgeneric invalid tokenとsilent closeをtyped role、same-slot retry、exact ownership、
no-cascade recoveryへ置き換える。inline constructor braceの解釈も保ち、brace/colon Cast declaration bodyや
punctuation-free target/body splitは追加しない。

## 10. Known residual / deferred surface

documented residualはclosed tableではなくcondition-basedである。次の4条件がすべて成り立つ場合だけ適用する:
missing-closeのnested PatternまたはTypeExpression ownerがrecovery中またはpost-item boundaryをjudging中であること、
gapがenclosing sequenceのnext-candidate boundaryであること、そのboundaryがcaller-ownedとして見えないこと、
inner driverにlocal recovery/separationとしてconsume/reinterpretしてnext outer candidateまで続けるreal pathがあること。
complete item後のclean local `ImplicitNewline` continuationもmalformed scanだけでなく含む。

`cast_gate_8_real_dispatch_is_atomic_across_root_and_canonical_owners`は、ListPattern/CatchBraced、
ParenthesizedPattern/CatchIndented、RecordPattern/root same-indent、Pattern-annotation
EffectRow/CaseIndented、CastTarget EffectRow/root same-indent、ListPattern/CaseInline commaという
6個のnon-exhaustive characterizationについて、current AST/direct remainder、recovery、discovery count、
lossless CSTを固定する。これらはgreen successではない。well-delimited input、propagated caller close、
strict dedent、active If companion、visible caller boundaryはrequired success caseのままである。

deferred surfaceはCast-specific `via`、cast-rule registration、implicit conversion application、
expected-type behavior、ambiguity/coherence、HIR、resolver、inference、monomorphization、diagnostics wording、
formatterである。explicit `.cast` method/role familyはseparateのままにする。

## 11. Implementationとregression cross-reference

`crates/yu-syntax/src/grammar/declaration.rs`では、Cast pathは
`recognize_cast_statement_intro`、
`parse_required_cast_pattern_value_isolated`、
`commit_required_cast_pattern_value_isolated`、
`parse_required_cast_target_type_isolated`、
`commit_required_cast_target_type_isolated`、`parse_cast_pattern_isolated`、
`commit_cast_pattern_isolated`、`parse_cast_target_isolated`、
`commit_cast_target_isolated`、`parse_cast_declaration_form_aware_isolated`、
`commit_cast_declaration_isolated`、`parse_cast_form_isolated`、
`commit_cast_form_isolated`で実装される。

regression fixtureには
`cast_statement_intro_is_exact_isolated_and_rolls_back_every_probe_state`、
`isolated_cast_signature_prefix_lattice_is_typed_lossless_and_ast_direct_exact`、
`isolated_cast_form_uses_the_neutral_binding_style_layout_without_binding_identity`、
`isolated_cast_declaration_direct_cst_is_byte_exact_and_matches_ast_forms`、
`isolated_cast_declaration_recovery_rows_are_typed_non_cascading_and_lossless`、
`isolated_cast_declaration_restores_full_boundary_state_before_promotion`、
`cast_gate_8_real_dispatch_is_atomic_across_root_and_canonical_owners`、
`cast_gate_9_final_public_boundary_matrix_closes_scope_and_parity`がある。
