# Bracket-row grammar

## 1. 正本と対象範囲

このページは`syntax-v0`の`BracketRow`を定める。2026年8月20日のAuthoritative
bracket-row section、leading-row-head/bracket-arrow current-Item recovery
authority、bracket-row recovery authority、BracketRow close-error CST topology
supersessionに従う。

leading row後のrequired ordinary type headと、trailing row後のrequired arrowを対象とする。
effectful-type wrapper、row-tail meaning、effect inference、lowering、diagnostic wordingは
対象外である。

## 2. 受理構文

```text
TypeExpression := [ LeadingBracketRow TypeChainTrivia ] TypePrimary { TypeTightTail | TypeApplyArgument } [ TypeArrowTail ]
LeadingBracketRow := BracketRow
TypeArrowTail := [ BracketRow TypeChainTrivia ] "->" TypeChainTrivia TypeExpression
BracketRow := "[" G* [ TypeExpression { BracketRowDelimiter TypeExpression } [ BracketRowDelimiter ] ] "]"
BracketRowDelimiter := comma | semicolon | qualifying newline
```

leading row後のheadとtrailing row後のarrowはmandatory recoverable slotである。
`TypeChainTrivia`はempty/same-line/deeper continuation triviaを許すが、equal-or-shallower
newlineを許さない。

## 3. 受理と境界

fresh type slotの`[`はactive boundary checkとcontextual/compound type starterの後、ordinary
primary candidateより先にleading rowを受理する。一つのleading rowをaccept後、second rowは
recursive parseせずmalformed required headとしてrecoverする。

complete operand後、tail judgeはTypeApplyより先に`[`へbracket-arrow authorityを与える。
`T [e] -> U`はtrailing-row arrow、`F [e] T`はmalformed bracket-arrow tail、
`F ([e] T)`はexplicit apply argumentである。row itemとmatching `]`はlocalであり、caller
stop/outer closeは消費しない。

## 4. Direct Rowan CST

`BracketRow`はbracket、trivia、literal separator、direct `TypeExpression` itemをsource
orderで持つ。leading formでは`TypeExpression`のfirst source-bearing childである。trailing
formでは`TypeArrowTail`のfirst childでarrow tokenより前に置く。effectful-type、effect
arrow、list、synthetic separator nodeは作らない。

Item errorはdirect raw `Error` groupとして`BracketRow`の下に残る。locally consumed
mismatched closeごとに、そのcloseのraw `Error` leafだけを持つdirect `BracketRow` child
`TypeDelimitedForeignClose`一つを置く。このwrapperはleading/retry trivia、`Missing`、
accepted `]`、returned Item、nested type、caller/outer close、fence、successor acquisitionを
含まない。

## 5. Recovery CST

leading row後にheadがなければexisting primary slotを`LeadingEffectTypeHead`でrecoverする。
trailing row後にarrowがなくRHS candidateがあれば`BracketRowArrow`をrecoverし、同位置で
RHSをretryする。EOF/outer boundary/newlineではmissing arrowだけを置き、RHS Missingを
cascadeしない。

malformed row itemはshared delimited item/separator slotを使う。raw `Error` groupはdirect
`BracketRow` childのままである。locally consumed mismatched closeごとにdirect
`TypeDelimitedForeignClose` child一つを置く。matching `]`、protected caller/outer close、
fenceはこのwrapperの外に残る。direct Item groupとwrapped Close groupはgeneric CST-derived
occurrenceのままであり、occurrence pathがroleを区別する。`BracketRow`はconstruct-specific
diagnostic schema/API mappingを追加しない。second leading rowはbalanced row全体への
delimiter-aware raw error一つとなり、その後でoriginal headをretryする。

## 6. Source/CST例

`[e] T`では`BracketRow`がfirst source-bearing `TypeExpression` childとなり、その後に
ordinary head `T`が続く。`T [e] -> U`では`BracketRow`がfirst `TypeArrowTail` childとなり、
tail前のwhitespaceはenclosing `TypeExpression`に残る。

`T [:] -> U`は`:`をmalformed row item一つとしてrecoverし、arrow/RHSを受理する。
`[e][f]T`ではfirst rowだけが`BracketRow`であり、balanced second rowはmalformed required
headとなる。

## 7. 構成

[Standalone `TypeExpression` core](type-expression-core.md)がordinary head、RHS、周囲のtailを
定める。[syntax content model](../conventions/syntax-content-model.md)、[Rowan CST
notation](../conventions/rowan-cst.md)、[recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md)は共有する`syntax-v0`規約を
定める。
