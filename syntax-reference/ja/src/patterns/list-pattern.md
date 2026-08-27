# List pattern

## 1. Status、正本、最終確認

originalのAuthoritative ListPattern追補は`notes/design/2026-08-20-yu-syntax-chasa-architecture.md` 8019–8612行にある。comma-only separator scopeはAuthoritative layout追補 9314–9696行で明示的にsupersedeされ、ambient recoveryは`ASOB-G` 18358–19161行でさらにrevisionされている。original opening statusは古いが、relevant addendumのclosing signatureは査読・確定とユーザ承認を記録している。

implementation commitは`af9c85f4`、`c852d878`、`81ef211d`、`f38c77d8`、`0da2d26e`である。このページは`f9393004`に対して確認した。

## 2. Scopeとnon-scope

ListPatternはordinary Pattern itemまたはliteral spread itemから成るbracketed sequenceである。empty list、trailing comma、arbitrary spread count/position、full recursive Pattern spread RHS、typed recovery、caller-boundary handoffを扱う。

Record pattern、Pattern annotation、constructor/ML tail、expression list literal、spread matching semantics、cardinality validation、resolution、typing、Pattern HIR、lowering、diagnostics wordingはscope外である。

## 3. BNF-equivalent grammar

```text
ListPattern := LBracket OpeningTrivia [ ListPatternItem { ListPatternSeparator ListPatternItem } [ ListPatternSeparator ] ] RBracket
ListPatternSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(list_pattern_base)
ListPatternItem := Pattern@Lowest | ListPatternSpreadItem
ListPatternSpreadItem := DotDot G* Pattern@Lowest
```

baseは`[`直後にopening triviaとincoming indentationからcaptureする。following indentationが`<= list_pattern_base`のnewlineはseparator、deeper newlineはcontinuationである。semicolonはList separatorにならない。`..tail`と`.. tail`はspread formで、`...`と`..+`は`DotDot`へprefix-splitしない。

## 4. Judge、priority、owner boundary

`[`をacceptした後、ListPatternはbracket delimiterとlocal comma/right-bracket stopを所有する。item judgeはmatching close、exact `DotDot`、ordinary Pattern NUD、comma missing-item boundary、malformed recoveryの順に見る。List-local commaはCatch handler / arm separatorにならない。

explicit commaは同じboundary cluster内のqualifying newlineより優先する。implicit newlineはliteral triviaであり、synthetic tokenではない。own `]`がfirst、propagated caller right closeはnon-consuming returnになる。`ASOB-G`はstrict ambient dedentまたはactive If companionでlocal implicit boundaryをvetoし、ordinary same-indent non-companion competitionはこのmechanismのscope外に残す。

## 5. Byte-exact CST worked examples

ListPatternとlayout addendumにはexact CST shapeがあるが、このexample群のbyte-range-annotated CST treeはない。ここではrangeを作らない。

```text
[head, ..middle, tail]
```

design 8289–8311行は`Pattern > ListPattern`が`head`と`tail`のdirect ordinary `Pattern` child、raw `Comma` token、`DotDot`とRHS Pattern `middle`を持つ1個の`ListPatternSpreadItem`を持つことを示す。

```text
[..left, ..right,]
```

design 8313–8336行は2個の`ListPatternSpreadItem` childとraw trailing commaを示す。spread multiplicityでouter nodeは変わらない。

```text
[
  head
  ..middle
  tail
]
```

design 9574行はbase two、3個のListPattern item、valid trailing implicit boundaryと分類する。newlineとindentationはliteral triviaであり、`Separator` nodeを追加しない。

```text
[a
b]
```

design 9575行はbase zeroのequal-indent newlineをvalid two itemsと分類する。design 9576行はdeeper newlineをsecond List itemではなくfirst Patternのcontinuationとして対比する。

## 6. Parser-side AST shape

current AST primaryは`PatternPrimary::List(ListPattern)`である。`ListPattern`は`open`、recovered ordered `items`、literal `trailing_comma`、recovered `close`、`range`を持つ。各`ListPatternItem`はdirect `Pattern`または`Spread(ListPatternSpreadItem)`であり、spread nodeは`marker`、recovered boxed RHS Pattern、rangeを持つ。

accepted `DotDot`はRHSがincompleteでも保持する。ASTはitem orderとliteral trailing-comma evidenceを保持するが、every separator tokenをduplicateせず、spread semanticsも決めない。

## 7. Typed recovery table

| condition | recoveryとcontinuation |
| --- | --- |
| `[]` / `[a,]` | valid empty/trailing-comma list。recoveryなし |
| `[,a]` / `[a,,b]` | absent itemごとに`PatternRole::ListItem` Missingを1個置き、same-position item retryする |
| same-line next item or spread | `PatternRole::ListSeparator` Missingを1個置き、same-position retryする |
| `[a; b]` | non-empty `PatternRole::ListSeparator` Errorを置き、`b`をnext itemとしてretryする |
| malformed ordinary item | `PatternRole::ListItem` Errorを1個置き、same-slot retryする |
| `[..]` / `[..,a]` | `ListPatternSpreadItem`を保持し、`PatternRole::ListSpreadRhs` Missingを1個置く。comma/closeはownerに残す |
| `[..@tail]` | RHS Errorを1個置き、`tail`でsame-slot retryする |
| `[...,a]` / `[..+,a]` | malformed item Error。prefix splitでspread nodeを作らない |
| missing/mismatched `]` | ListPattern closing-delimiter Missing/Errorを1個置き、caller boundaryをconsumeしない |
| ambient-vetoed newline | outer gapで止まり、それまでに必要なlocal recoveryだけを保持する |

committed rangeごとにrecovery nodeとrecordが1個ある。nested list frameはnormal close、terminal boundary、recoveryでexactly once balanceする。

## 8. Boundaryとstate-restoration contract

bracket frameはopener後にbaseを1回captureし、every exitでdelimiter、stop、layout、scanner、sink stateをrestoreする。AST/direct fixtureはnested bracket、outer arm arrow、handler comma、implicit newline、malformed item、missing close、propagated caller close、ambient If vetoをcoverする。`ASOB-G`はambient/If、indentation、expression/type-owner、ML、positional-fence stateのexact restoreも要求する。

## 9. Yulang2 divergences

Yulang3はbracket ownership、ordinary/spread item、unrestricted spread placement、layout-separated item formを保つ。implicit newlineはYulang2のempty `Separator` nodeではなくliteral triviaで表し、generic invalid token / silent closeの代わりにtyped Missing/Errorとsame-position retryを使う。

## 10. Known residual / deferred surface

`ASOB-G`はmissing nested delimiterの背後に隠れるcaller boundaryのうち、strict dedentでもactive If companionでもないresidual caseをdocumentする。これらをsuccessとして隠さない。later Cast addendumはCast-contained ListPattern caseのseparate condition-based characterizationを持つ。

deferred workはrecord-list unification、spread matching/capture semantics、multiplicity/position validation、list element typing、Pattern HIR、lowering、expression list literalである。

## 11. Implementationとregression cross-reference

`crates/yu-syntax/src/grammar/pattern.rs`では`parse_list_pattern`、`commit_direct_list_pattern`、`parse_pattern_delimited_items_ast`、`commit_direct_pattern_delimited_items`、`commit_direct_pattern_delimited_item`、`recover_pattern_delimited_separator_or_close`、`outer_pattern_close_stop_pending`を使う。

fixtureには`list_patterns_accept_comma_or_layout_newline_and_keep_spread_items`、`list_pattern_recovery_preserves_item_and_separator_boundaries`、`list_pattern_typed_recovery_contract_has_direct_coverage_for_every_list_row`、`ambient_if_companion_vetoes_every_pattern_delimited_implicit_newline`、`binding_list_pattern_preserves_else_arm_after_an_ambient_veto`、`pattern_delimited_malformed_recovery_returns_the_same_ambient_gap`、`pattern_caller_close_propagation_is_right_close_only`がある。
