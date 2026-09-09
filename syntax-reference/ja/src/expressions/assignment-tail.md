# Assignment tail

## 1. 対象範囲と受理

このページは、`AssignmentTail`の direct inline `Assignment(Rhs)` slot を定める。
対象は、この slot の source-order Rowan CST、recovery shape、後続の diagnostic projection である。

例は、可逆な`text` attribute escape を含む site-wide の[Rowan CST表記](../conventions/rowan-cst.md)を使う。

Assignment は、`OperatorChain`の終端 outer continuation である。
admitted dynamic LED operator が不成立になった後、1 個の`=`を取得する。
continuation は enabled、outermost、かつ ML argument の外でなければならない。
lower-threshold または ML の candidate は source を pending のまま残す。
`AssignmentTail`と recovery element は emit しない。
したがって、`x=-y`は prefix RHS を持つ assignment である。
`x==y`は dynamic infix expression のままである。

direct inline slot は RHS を 1 個要求する。
comma を所有する inline list ではない。
RHS を受理した後、`AssignmentTail`は閉じる。
さらに outer continuation は走査しない。

## 2. Source-order CST

`AssignmentTail`は左辺を所有も wrap もしない。
enclosing `OperatorChain`が、左辺の child と`=`より前の trivia を所有する。
その後に 1 個の`AssignmentTail` node を追加する。

direct inline の child alternative を次に示す。
この grammar は alternative を読みやすくするため、trivia を省略している。
trivia の位置は後の節で明示する。

```text
OperatorChain := <left-expression children and pre-`=` trivia> AssignmentTail
AssignmentTail := Equals (Missing | Error+ | Error+ OperatorChain | OperatorChain)
Equals := "="
```

accepted inline RHS では、`AssignmentTail`は`Equals` token、native leading trivia、1 個の concrete な RHS `OperatorChain`をこの順で持つ。
`InlineRhs` node は存在しない。

```xml
<AssignmentTail>
  <Equals text="=" />
  <Whitespace text=" " />
  <OperatorChain>
    <IdentifierExpression>
      <Identifier text="y" />
    </IdentifierExpression>
  </OperatorChain>
</AssignmentTail>
```

accepted direct RHS または initially rejected direct RHS の前にある initial leading は、`AssignmentTail`の直下に native trivia として置く。
その trivia は RHS `OperatorChain`または direct `Error` token より前に置く。
admitted retry の leading は、新しい RHS `OperatorChain`に入る native trivia である。
直前の raw group には含めない。

## 3. RHS の absence と raw form

admitted stop、boundary、separator、close、non-NUD bracket opener、non-continuing layout、EOF では、必要な inline RHS がない。
tail は`Assignment(Rhs)` slot に zero-width の`Missing`を 1 個置く。

```xml
<AssignmentTail>
  <Equals text="=" />
  <Whitespace text=" " />
  <Missing />
</AssignmentTail>
```

ordinary EOF では、`AssignmentTail`が所有する leading trivia を先に emit してよい。
そのとき`Missing`の range は physical EOF になる。
protected boundary では、boundary item 全体と未所有の leading は pending のまま残る。
これらは`AssignmentTail`の child にならない。

non-boundary かつ non-NUD の run が RHS を始めるとき、tail は最大の raw group を隣接した direct `Error` token として emit する。
initial rejected-item leading は group の外に残る。
interior leading は group に含める。
terminal group は protected boundary を変更せずに返す。
同じ原因の`Missing`は追加しない。

```xml
<AssignmentTail>
  <Equals text="=" />
  <Whitespace text=" " />
  <Error text="@" />
  <Error text="  " />
  <Error text="@" />
</AssignmentTail>
```

raw group の後で inline expression を受理できる場合、その expression は同じ RHS slot を満たす。
retry-leading whitespace は新しい RHS child に属する。

```xml
<AssignmentTail>
  <Equals text="=" />
  <Whitespace text=" " />
  <Error text="@" />
  <OperatorChain>
    <IdentifierExpression>
      <Whitespace text=" " />
      <Identifier text="y" />
    </IdentifierExpression>
  </OperatorChain>
</AssignmentTail>
```

raw group を`Invalid`で wrap してはならない。
`Error`は token leaf である。
隣接する leaf は physical fragment を表す。
そこに新しい grammar は作らない。

## 4. Slot projection と nested ownership

この direct inline slot では、`Missing` node と最大の raw `Error` group は、それぞれ`Assignment(Rhs)`へ project する。
expected syntax は`Expression`である。
primary expectation index は 0 である。
`Missing`は zero-width CST range に project する。
raw group は、隣接する`Error` token の combined range に 1 回だけ project する。
これは 2 個目の`Missing`でも unexpected payload でもない。

入れ子の recovery は、入れ子の grammar slot に属する。
たとえば、RHS `OperatorChain`内の`FieldTail`にある`Missing`は、`Assignment(Rhs)`の recovery occurrence にならない。

CST 由来 diagnostic の publication は実装待ちである。
ここで定めた node range と最大の direct `Error` group を使う。
[Source root、header、diagnosticの責務](../conventions/source-root-and-diagnostics.md)は、その publication boundary を定める。

## 5. 除外事項

より深く導入した行にある RHS は、`IndentedStatementBlock`へ delegate する。
その block entry、child slot、recovery、diagnostic projection は、このページでは定めない。

このページは、AST、HIR association、operator table の変更、完全な slot inventory、後続の public diagnostic result を定めない。
