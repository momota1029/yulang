# Pattern core と parenthesized pattern

## 1. Status、正本、最終確認

originalのAuthoritative first-slice Pattern追補は`notes/design/2026-08-20-yu-syntax-chasa-architecture.md` 6629–7242行にある。opening statusは古いが、closing signatureは査読・確定とユーザ承認を記録している。current parenthesized separatorはAuthoritative layout追補 9314–9696行でrevisionされ、ambient-boundary recoveryはAuthoritative `ASOB-G`追補 18358–19161行でrevisionされている。

core implementationは`4ec436cc`から始まり、current parenthesized behaviorは`81ef211d`、`f38c77d8`、`d3778e13`、`0da2d26e`にも依存する。laterの`9323ce68` annotation追補はshared ASTへ`PatternTypeAnnotation`を追加した。そのgrammarはseparate reference pageで扱う。このページは`f9393004`に対して確認した。

## 2. Scopeとnon-scope

coreはindependent fixed-precedence Pattern Pratt familyである。ordinary/sigil identifier、decimal integer、contiguous symbol pattern、parenthesized pattern、`as` alias、`|` alternationを扱い、expression `OperatorChain`、dynamic binding power、`BpVec`を使わない。

このページはparenthesized containerのcurrent comma-or-layout-newline behaviorを扱う。List/Record primary、trailing Pattern type annotation、call、path、ML application、literal、resolution、lowering、exhaustiveness、binding validationはseparate grammarまたはsemantic workに残る。

## 3. BNF-equivalent grammar

```text
Pattern := Pattern@Lowest
Pattern@P := PatternPrimary { PatternTail(P) } [ PatternTypeAnnotation ]
PatternTail(P) := G* PatternAliasTail if P <= Alias | G* PatternAlternationTail if P <= Alternation
PatternAliasTail := AsKw G+ Identifier
PatternAlternationTail := Pipe G* Pattern@Alternation
PatternPrimary := IdentifierPattern | IntegerPattern | SymbolPattern | ParenthesizedPattern | ListPattern | RecordPattern
SymbolPattern := Colon!Identifier
ParenthesizedPattern := LParen OpeningTrivia [ Pattern@Lowest { ParenthesizedPatternSeparator Pattern@Lowest } [ ParenthesizedPatternSeparator ] ] RParen
ParenthesizedPatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(parenthesized_pattern_base)
```

first-slice orderは`Alternation < Alias`であり、alternationは`A | (B | C)`になる。later annotation suffixはcurrent shared `Pattern` ASTを反映するためだけに示す。implicit newlineは`(`直後にcaptureしたbase以下のindentだけseparatorになり、deeper newlineはcurrent Pattern continuationへ残る。

## 4. Judge、priority、owner boundary

operand positionのNUD judgeはactive caller `Colon` stopより先にcontiguous `:identifier`を取る。compositeがなくcolonがactive stopならcaller-ownedのままにする。sigil nameはordinary wordより先、`as`はtail positionだけcontextual、`|`はdynamic expression operatorではなくfixed Pattern tokenである。

`(`をacceptするとparenthesized ownerはlayout baseをcaptureし、own delimiter/local comma-and-close scopeをpushして、explicit commaとqualifying newline boundaryを所有する。implicit newlineにはsynthetic separatorをemitしない。own matching `)`がfirst、propagated caller right closeはnon-consuming returnになる。`ASOB-G`はstrict ambient dedentまたはactive If companionがlocal implicit-boundary decisionをvetoできるようにする。close-recovery driverはAST cursor ownershipをpre-existing direct-CST resultへconvergeする。

## 5. Byte-exact CST worked examples

originalとrevising addendumにはexact CST treeがあるが、このexample群のbyte-range-annotated CST treeはない。このページはrangeを作らない。

```text
A | B as c
```

design 6901–6918行はouter `Pattern`、`IdentifierPattern A`、続く`PatternAlternationTail`を示す。tailは`Pipe`とrecursive RHS `Pattern`を持ち、RHSは`IdentifierPattern B`と`AsKw`およびidentifier `c`を持つ`PatternAliasTail`を所有する。left primaryをtailの下へreparentしない。

```text
(:foo, _bar,)
```

design 6920–6937行はouter `Pattern`の`ParenthesizedPattern`がraw parentheses/comma、two-token `SymbolPattern`（`Colon`、`Identifier foo`）、`SigilIdentifier _bar`を持つ`IdentifierPattern`を所有することを示す。

```text
(A
B)
```

design 9549–9551行はbase zeroでvalid two-element `ParenthesizedPattern`へrevisionしている。physical newlineはchild `Pattern`間のliteral triviaであり、`Missing(Comma)`もsynthetic separator nodeも作らない。

## 6. Parser-side AST shape

`crates/yu-syntax/src/grammar/pattern.rs`のactual `Pattern`はrecovered `head`、ordered `tails`、optional `type_annotation`、`range`を持つ。`PatternPrimary`はcurrentでidentifier、integer、symbol、`Parenthesized`、`List`、`Record` variantを持つ。core parenthesized variantは`open`、recovered element Pattern、literal `trailing_comma`、recovered `close`、`range`を持つ。

`PatternTail`は`Alias(PatternAliasTail)`または`Alternation(PatternAlternationTail)`である。aliasはkeywordとrecovered ordinary binding、alternationはpipeとrecovered boxed RHSを持つ。Pattern coreはidentifierをbinding、constructor、wildcardへ分類しない。

## 7. Typed recovery table

| condition | recoveryとcontinuation |
| --- | --- |
| absent primary | `PatternRole::Primary` Missingを1個置き、caller boundaryをconsumeしない |
| malformed primary then NUD | maximal primary Errorを1個置き、same-slot retryする |
| `:` without an adjacent name | colonがcaller-ownedでなければmalformed symbolと`PatternRole::SymbolName` Missingになる |
| `A as` | `AsKw`を保持し、terminal boundaryへ`PatternRole::AliasBinding` Missingを1個置く |
| `A |` | `Pipe`を保持し、recovered RHS Pattern primaryを1個置く |
| leading comma in parens | `PatternRole::ParenthesizedElement` Missingを1個置き、next-element retryする |
| adjacent same-line element | `PatternRole::ParenthesizedSeparator` Missingを1個置き、same-position retryする |
| malformed/missing parenthesized close | closing-delimiter ErrorまたはMissingを1個置き、own/caller-close ownershipを分ける |
| qualifying newline | valid implicit boundary。missing commaもsynthetic separatorもない |
| ASOB-vetoed boundary | local containerが止まりambient gapを返し、outer ownerをconsumeしない |

direct pathはrangeごとにrecovery nodeとrecordを1個ずつ持つ。nested recoveryはPatternまたはclosing-delimiter roleを保ち、同じcauseへouter diagnosticを追加しない。

## 8. Boundaryとstate-restoration contract

parenthesized entry/exitはdelimiter、stop、layout frameをbalanceする。layout baseはopener後に1回だけcaptureする。AST/direct fixtureはnormal item、implicit boundary、malformed recovery、caller-close handoff、ambient If veto、scanner/sink stateのexact rollbackをcoverする。`ASOB-G`はnested exitでambient/If、delimiter/stop、indentation、expression/type-owner、ML、positional-fence stateをrestoreすることを要求する。

## 9. Yulang2 divergences

Yulang3はindependent fixed Pattern Pratt family、contiguous symbol spelling、alias/alternation ordering、layout-separated parenthesized formを保つ。Yulang2と違いimplicit newlineはsource-absent `Separator` nodeではなくliteral triviaとadjacent childで表す。typed Missing/Error recoveryはgeneric invalid tokenとsilent closeを置き換える。

## 10. Known residual / deferred surface

`ASOB-G`はnon-companion same-indent competitionとmissing nested delimiterの背後に隠れる一部caller boundaryをknown residual familyとして明示的に残す。later Cast addendumはそのown four-condition instanceをcharacterizeするが、どちらもgeneralな"outer owner always wins" exceptionを与えない。

deferred grammarはPattern annotation detail、List/Record form、constructor tail、literal、ML applicationである。deferred semantic workはwildcard meaning、binding set、alias scope、type constraint、exhaustiveness、Pattern HIR、loweringである。

## 11. Implementationとregression cross-reference

`crates/yu-syntax/src/grammar/pattern.rs`のkey functionは`parse_pattern`、`parse_pattern_with_outer_missing_role`、`parse_direct_pattern`、`parse_pattern_bp`、`parse_pattern_primary`、`parse_parenthesized_pattern`、`parse_pattern_delimited_items_ast`、`commit_direct_parenthesized_pattern`、`commit_direct_pattern_delimited_items`、`drive_parenthesized_pattern_close_recovery`、`outer_pattern_close_stop_pending`である。

fixtureには`identifiers_and_integer_primaries_have_the_fixed_pattern_vocabulary`、`symbol_pattern_is_two_adjacent_tokens_and_never_an_expression_tail`、`parenthesized_patterns_accept_comma_or_layout_newline_boundaries`、`parenthesized_close_recovery_converges_ast_onto_existing_direct_ownership`、`ambient_if_companion_vetoes_every_pattern_delimited_implicit_newline`、`dynamic_operator_tables_cannot_change_pattern_cst`、`excluded_forms_remain_unconsumed_after_a_first_slice_pattern`、`pattern_caller_close_propagation_is_right_close_only`がある。
