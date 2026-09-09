# Assignment tail

## 1. 対象範囲

Assignment は、`OperatorChain` の終端 outer continuation である。
1 文字の `=` と、その直後に置く 1 個の右辺を受け付ける。
このページは、surface spelling、CST、recovery だけを定める。

Assignment は outer-only continuation である。
continuation が enabled であり、ML argument の外にある場合だけ受理する。
より低い binding-threshold context または ML argument の candidate は、source を consume せず、CST/recovery output を出さずに reject する。

右辺は inline `Expression` または indented `Statement` block のどちらか一方である。
comma を所有する inline list にはならない。

## 2. 受理する表記

次は assignment の inline form である。

```text
x = y
x=-y
```

assignment は、admitted dynamic LED operator より後に判定する。
そのため、`x == y` は assignment と後続の `=` ではなく dynamic infix のままである。

## 3. Flat source-order CST

`AssignmentTail` は左辺を所有も wrap もしない。
完了した左辺の source-order child の後へ、開いている `OperatorChain` が `AssignmentTail` を追加する。
Rowan CST では、`AssignmentTail` node は flat `OperatorChain` の中に置く。

```text
OperatorChain :=
    <left-expression children in source order>
    AssignmentTail

AssignmentTail :=
    "=" G* Expression
  | "=" <existing indented Statement block>
```

committed `=` より前の trivia は `OperatorChain` の direct child に残る。
`AssignmentTail` は `=`、その後に受理した leading trivia、右辺を source order で所有する。

改行後の indent が導入位置より厳密に深いとき、右辺は existing indented `Statement` block になる。
それ以外では、`AssignmentTail` は inline `Expression` を 1 個だけ要求する。

## 4. 終端性

右辺が成功すると、`AssignmentTail` は閉じる。
その exit を enclosing owner へ返し、さらに outer-chain continuation は走査しない。

この規則は assignment にだけ適用する。
`as Type` annotation は別の tail であり、このページはその構文を定めない。

## 5. Recovery

inline 右辺を開始できない fence、abstract boundary、active stop、line stop、separator、close、non-NUD bracket opener、non-continuing layout、EOF では、`AssignmentTail` の RHS slot に zero-width `Missing` を 1 個置く。
ordinary EOF では、`AssignmentTail` は所有する leading trivia を先に発行してよく、`Missing` は physical EOF に anchor する。
protected boundary では、その item 全体と未所有の leading trivia を pending のまま残す。

boundary ではない non-NUD material が右辺の先頭にある場合、最初の leading trivia は `Error` の外に残る。
assignment は maximal lexical run を `Error` として消費する。
malformed `Error` run の内部の leading trivia は `Error` に含める。retry または protected boundary の前の leading trivia は `Error` の外に残す。
その後に受理できる右辺があれば、同じ 1 個の RHS slot を retry する。
run が protected boundary に達した場合は `Error` を返し、追加の `Missing` は置かない。

入れ子の `Expression` recovery は既存の role を保つ。
この tail はそれらを再分類しない。

このページで使う `Missing` と `Error` の表記は、[Rowan CST表記](../conventions/rowan-cst.md)に従う。
current と approved の `Error` / `Invalid` rendering は site-wide convention が定める。
このページは、実装待ちの topology migration が有効になったとは述べない。

## 6. 除外事項

この構文は canonical AST materialization、HIR association、operator table の変更、declaration equality の scanning を定めない。
`AssignmentTail` は flat CST の構文形であり、semantic target を持たない。
