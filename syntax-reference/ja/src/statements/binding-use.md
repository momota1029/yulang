# Bindingと`use`のstatement form

## 権威と対象範囲

このページは`syntax-v0`で受理するBindingと`use`のstatement form、およびその直接Rowan CSTを定める。
Bindingの生成規則、配置、CST、layoutは、`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`のAuthoritativeな「canonical `Statement`のbinding / use declaration拡張」節が定める。
`UseTree`の生成規則とCSTは、同じ設計記録のAuthoritativeな「Complete `use` declaration grammar and projection」節が定める。
同節の「Oracle state machine」と「UseQualifiers」、「UseAnchor」小節がanchorの受理を定める。
Bindingのcurrent-Item recoveryは、Authoritativeな`notes/design/2026-09-08-successor-binding-current-item-recovery.md`が定める。
`UseGroupForeignClose`は、Authoritativeな`notes/design/2026-09-12-successor-use-group-foreign-close-topology.md`が定める。

[構文の内容モデル](../conventions/syntax-content-model.md)は配置の一覧であり、これらの権威を置き換えない。

## 配置と受理する表層構文

Bindingと`use`は、`Root`と入れ子のstatement ownerで受理する。
`Root`では、`BindingStatement`または`UseDeclaration`を直接の子に置く。
入れ子のstatement ownerでは、`Statement`を1個置き、その直接の子に`BindingStatement`または`UseDeclaration`を1個置く。
`BindingDeclaration`を`Root`または`Statement`の直接の子にしてはならない。

root専用のoperator definitionは、このページのstatement formではない。
`Root`直下の`OperatorHeader`と、それに続く兄弟の`OperatorChain`は、入れ子の`Statement`内に置かない。

```text
BindingStatement :=
    VisibilityKw Gbind Pattern
    [ Gbind Equals BindingBody ]

VisibilityKw := MyKw | OurKw | PubKw

BindingBody :=
    G0* OperatorChain
  | IndentedStatementBlock

UseDeclaration := [ VisibilityKw I+ ] UseKw I+ UseTree

UseTree :=
    UseGroup GroupSuffix
  | ModKw I+ ModPath UsePathSuffix
  | RealmKw Slash SeparatorTarget
  | BandKw ColonColon SeparatorTarget
  | UsePath UsePathSuffix

UsePathSuffix :=
    SingleSuffix
  | TerminalJoin UseGroup GroupSuffix
  | TerminalJoin UseGlob GlobSuffix

SeparatorTarget :=
    UsePath UsePathSuffix
  | UseGroup GroupSuffix
  | UseGlob GlobSuffix

SingleSuffix := (I+ UseAlias)* UseQualifiers?
GroupSuffix := (I+ UseAlias)* UseQualifiers?
GlobSuffix := UseQualifiers?

TerminalJoin := ColonColon | Slash
UsePath := PathSegment ((ColonColon | Slash) PathSegment)*
ModPath := Identifier ((ColonColon | Slash) PathSegment)*
PathSegment := Identifier | OperatorName
OperatorName := LParen Operator RParen

UseGroup := LBrace G* (UseTree G* (Comma G*)?)* RBrace
UseAlias := AsKw I+ Identifier
UseGlob := Star (I+ UseAlias)*
    (I+ WithoutKw I+ UseExclusion (Comma G* UseExclusion)*)?
UseQualifiers := I+ UseVersion (I+ UseAnchor)? | I+ UseAnchor
UseVersion := Version
UseAnchor := WithKw I+ UseAnchorPath
UseAnchorPath := Identifier ((ColonColon | Slash) Identifier)*
UseExclusion := Identifier | OperatorName | Star | UseExclusionGroup
UseExclusionGroup :=
    LParen G* (UseTree G* (Comma G*)?)* RParen
  | LBrace G* (UseTree G* (Comma G*)?)* RBrace
```

`I`は1個以上のinline trivia tokenであり、`G`はその位置で使うmaximal triviaである。
`G*`はphysical newlineを含めるが、`I+`は含めない。
`UseGroup`と`UseExclusionGroup`で隣接する`UseTree`は、commaまたはphysical newlineを含む間の`G*`で区切る。
top-levelの`without` listでは、最初のexclusionの前にinline triviaが必要であり、後続のexclusionはcommaで区切る。
`UseGroup`はspec startまたはseparator targetの後でだけ受理する。
`UseGlob`はseparator targetの後でだけ受理する。
`mod`は`ModPath`の最初に`Identifier`を必要とする。
`realm/`と`band::`は、`SeparatorTarget`の前にそのqualifying separatorを消費する。
ほかのspellingは通常の`UsePath` segmentのままである。
`ModPath`は、最初のsegmentが`Identifier`である点を除き、`UsePath`と同じCST nodeを作る。
`UseAnchorPath`も`UsePath` CST nodeを作るが、anchor pathのすべてのsegmentは`Identifier`である。

## 直接Rowan CST

`BindingStatement`は、`BindingHeader`をちょうど1個、`BindingBody`を0個または1個持つ。
`BindingHeader`は、`VisibilityKw`、`Gbind`、`Pattern`、受理した場合の`Gbind`と`Equals`をsource orderで持つ。
bodyを持たないBindingには空の`BindingBody`を作らない。
accepted `Equals`ごとに`BindingBody`を1個作る。
`BindingBody`のstructural childは、inlineの`OperatorChain`またはindentedの`IndentedStatementBlock`のいずれか1個だけである。

`UseDeclaration`は、任意の`VisibilityKw`と直後の`I+`、`UseKw`、直後の`I+`、`UseTree`をsource orderで持つ。
`UseTree`はちょうど1個である。
visibilityがないとき、そのtokenまたはzero-width nodeを作らない。

spec-start groupの`UseTree`は、`UseGroup`をちょうど1個、`UseAlias`を0個以上、任意の`UseQualifiers`をsource orderで持つ。
`mod`の`UseTree`は、`ModKw`、`I+`、identifier-firstの`UsePath`をちょうど1個、続いて選んだ`UsePathSuffix`のchildを持つ。
`realm/`または`band::`の`UseTree`は、form markerのtoken 2個、続いて選んだ`SeparatorTarget`のchildを持つ。
通常のpathの`UseTree`は、`UsePath`をちょうど1個、続いて選んだ`UsePathSuffix`のchildを持つ。
`TerminalJoin`はwrapper nodeを作らず、`UseTree`の直接tokenである。

Single suffixは、`UseAlias`を0個以上、任意の`UseQualifiers`を持つ。
group terminalは、直接の`UseGroup`をちょうど1個、続いて`UseAlias`を0個以上、任意の`UseQualifiers`を持つ。
glob terminalは、直接の`UseGlob`をちょうど1個、続いて任意の`UseQualifiers`を持つ。

non-emptyの`UsePath`は、`PathSegment` 1個、続いてseparator tokenと`PathSegment`の対を0個以上持つ。
各segmentはwrapperなしの`Identifier`または`OperatorName` 1個である。
`UseAlias`は`AsKw`、`I+`、`Identifier`をちょうど1個ずつ持つ。
`UseQualifiers`は`UseVersion` 1個と任意の`UseAnchor`、または`UseAnchor` 1個を持つ。
`UseAnchor`は、`WithKw`、`I+`、すべてのsegmentが`Identifier` tokenである`UsePath`をちょうど1個持つ。
`UseExclusion`は`Identifier`、`OperatorName`、`Star`、`UseExclusionGroup`のいずれか1個を持つ。
`UseGlob`、`UseGroup`、`UseExclusionGroup`は、上の表層構文どおりにtoken、trivia、itemを直接の子としてsource orderで持つ。

すべてのdirect childはsource orderを保つ。
triviaとliteral tokenはlossless CSTに残る。

## 境界、layout、構成

`Gbind`は、physical newlineを含まない最大のtrivia、または次のindentがbindingの開始indentより深いphysical newlineを含む最大のtriviaである。
equal-or-shallower newlineはBindingへ入らず、外側のstatement ownerへ返す。

exact `=`の後にphysical newlineがなければ、`BindingBody`のstructural childはinlineの`OperatorChain`である。
physical newlineがあり、次のindentがbindingの開始indentより深ければ、structural childはnon-emptyの`IndentedStatementBlock`である。
statement separator、dedent、matching close、outer comma、companion stopは外側のownerが所有する。

`use` pathはphysical newlineをまたがない。
`UseGroup`のbraceとcomma、`UseExclusionGroup`のdelimiterとcommaは、それぞれのgroupが所有する。

[Rowan CST表記](../conventions/rowan-cst.md)、[layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md)、[recoveryの`Error` tokenと`Invalid` nodeのtopology](../conventions/recovery-error-invalid-topology.md)も参照する。

## 受理するsourceとCSTの例

次はgroupを持つaccepted `use` declarationである。

```text
use std::io::{read, write}
```

対応するXMLに似たRowan表記は次である。

```xml
<UseDeclaration>
  <UseKw text="use"/>
  <Whitespace text=" "/>
  <UseTree>
    <UsePath>
      <Identifier text="std"/>
      <ColonColon text="::"/>
      <Identifier text="io"/>
    </UsePath>
    <ColonColon text="::"/>
    <UseGroup>
      <LBrace text="{"/>
      <UseTree><UsePath><Identifier text="read"/></UsePath></UseTree>
      <Comma text=","/>
      <Whitespace text=" "/>
      <UseTree><UsePath><Identifier text="write"/></UsePath></UseTree>
      <RBrace text="}"/>
    </UseGroup>
  </UseTree>
</UseDeclaration>
```

## Recovery CST

Binding targetの欠落はtarget slotのzero-width `Missing`であり、targetのmalformed runはmaximal non-empty `Error`である。
validなPatternへretryするときは、同じtarget slotを使う。
exact `=`を受理した後のbody欠落は`BindingBody`内のzero-width `Missing`である。
inline bodyのmalformed runはmaximal non-empty `Error`であり、boundaryに達した後はbody Missingを重ねない。
indented Binding bodyはcompleted child ownerであり、outer Bindingはそのrecoveryを重複させない。

`use` pathの欠落はpath slotのzero-width `Missing`である。
group itemの欠落はgroup内のzero-width `Missing(GroupEntry)`であり、group-entryのmalformed runはdirect `Error+`である。
group terminal phaseでcloseが欠落するとき、`UseGroup`または`UseExclusionGroup`はopenerに対応するzero-width `Missing(Close)`を直接の終端childに置く。

locally consumedのunclaimed mismatched `RParen`または`RBrace`だけは、outer-close protectionの後にtransparentな`UseGroupForeignClose`を作る。

```text
UseGroupForeignClose := Error+
```

このwrapperは、1個のconsumed foreign closeごとに1個であり、non-emptyのraw `Error` token leafだけを持つ。
native trivia、`Missing`、`Invalid`、accepted punctuation、`UseTree`は持たない。
direct group-entry `Error+`はwrapperに入れない。
`RBracket`、accepted local close、protected outer close、`recover_group`内のforeign closeはこのwrapperを作らない。

## 定めないこと

このページは、bindingのdestructuring、visibility、body result、recursive scope、loweringを定めない。
`use`については、lexical import scope、module resolution、export、versionとanchorの意味、qualifierのprojectionを定めない。

ほかのdeclarationやcontrol statement、将来のPattern surface、declaration companion、`derives`、method attachmentもこのページの対象外である。
