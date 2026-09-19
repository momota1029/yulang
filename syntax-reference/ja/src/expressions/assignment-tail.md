# Assignment tail

## 1. 権威と対象範囲

このページは、`syntax-v0`のterminal `AssignmentTail`を定める。
2026年9月9日のexpression assignment tail設計にある`Assignment`節が、assignment role、admission、tail topologyを定める。
direct inline RHS slotは同日のAuthoritative error-admission schema sliceで定める。
2026年9月8日のindented Statement role transportは、indented RHSのshared block recoveryだけを定める。

対象は、`=`、direct inline RHS、deeper introduced lineの`IndentedStatementBlock` RHS、これらの直接CSTとrecoveryである。
assignmentの評価意味、left operandの解釈、演算子の結合、HIR、型は定めない。

## 2. 受理構文

```text
AssignmentTail := "=" AssignmentRhs
AssignmentRhs := OperatorChain | IndentedStatementBlock
```

outermostでenabledかつnon-MLのcontinuationだけがassignmentを受理する。
admitted dynamic LED operatorが不成立になった後、tailは一つだけの`=`を取得する。
strictly deeper introduced lineは`IndentedStatementBlock`を選ぶ。
それ以外は一つのinline `OperatorChain`を選ぶ。
inline RHSはcommaを所有するlistではない。

## 3. Admissionとboundary

lower thresholdまたはML argumentでのcandidateはpendingのまま残り、`AssignmentTail`もrecoveryも作らない。
`x=-y`では`-y`はinline RHSである。
`x==y`ではdynamic LED operatorの受理が優先し、assignment tailにはならない。

RHSが成功するとtailは閉じ、別のouter continuationを走査しない。
inline slotでactive stop、separator、close、non-NUD bracket opener、non-continuing layout、fence boundary、EOFがRHSを妨げると、slotはabsenceをrecoverする。
protected itemとそのunowned leadingはpendingのまま残る。

## 4. 直接 Rowan CST

`AssignmentTail`はleft expressionを所有もwrapもしない。
enclosing `OperatorChain`がleft childrenと`=`前のtriviaを所有し、続けて一つの`AssignmentTail`を置く。

```text
OperatorChain := <left-expression children and pre-`=` trivia> AssignmentTail
AssignmentTail := Equals (OperatorChain | IndentedStatementBlock)
```

direct inline alternativeでは、`AssignmentTail`は`Equals`、native leading trivia、一つのRHS `OperatorChain`をsource orderで持つ。
`InlineRhs` nodeは存在しない。
indented alternativeでは、`Equals`の後に`IndentedStatementBlock`をdirect childとして持つ。

## 5. Recovery CST

inline RHSがabsentなら、`AssignmentTail`は`Assignment(Rhs)` slotにzero-widthの`Missing`を一つ置く。
ordinary EOFではtailが所有するleadingを先に置ける。
protected boundaryではboundary itemとunowned leadingをtail childにしない。

non-boundaryかつnon-NUDのinline runは、`AssignmentTail`直下のmaximal raw `Error` groupである。
initial rejected-item leadingはgroupの外に残る。
interior leadingはgroupに属する。
retryのleadingは新しいRHS `OperatorChain`に属する。
retryがadmittedなら同じRHS slotを満たす。
groupがprotected boundaryへ達すると、そのboundaryを残し、同じ原因の`Missing`を追加しない。

indented alternativeのblock-entryとchild Statement slotの`Missing`またはraw `Error`は、`Assignment(IndentedStatement)` roleをtransportする`IndentedStatementBlock`自身に属する。
inline raw groupは`Invalid`でwrapしない。

## 6. Source/CST例

`x = y`はdirect inline RHSを持つ。

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="x" /></IdentifierExpression>
  <Whitespace text=" " />
  <AssignmentTail>
    <Equals text="=" />
    <Whitespace text=" " />
    <OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain>
  </AssignmentTail>
</OperatorChain>
```

`x = @ y`ではraw groupの後のchainが同じinline RHS slotを満たす。

```xml
<AssignmentTail>
  <Equals text="=" />
  <Whitespace text=" " />
  <Error text="@" />
  <OperatorChain><IdentifierExpression><Whitespace text=" " /><Identifier text="y" /></IdentifierExpression></OperatorChain>
</AssignmentTail>
```

次のsourceはindented alternativeを選ぶ。

```text
x =
  y
```

この`AssignmentTail`は、`Equals`の後に一つのdirect `IndentedStatementBlock` childを持つ。
そのordered contentsはshared block constructが所有する。

## 7. Composition

`AssignmentTail`は[dynamic operator chain](operator-chain.md)のterminal continuationである。
inline RHSはそのchainの通常のoperandとtail規則を使う。
indented RHSはshared `IndentedStatementBlock`へ委譲し、nested Statement recoveryをassignment tailへ移さない。
