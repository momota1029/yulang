# C441 — 正式な異種 positional 比較と literal 実例の fixed carrier 境界

## 既存 comparator が本当に出すもの

actual table の同名 constructor が `[row covariant, value invariant]` なら、任意の row points `e₁,e₂` と value intervals `(l₁,u₁),(l₂,u₂)` に対する既存 `compileContext` の出力は

```
[rowLe e₁ e₂, tyLe l₁ u₁, tyLe l₁ u₂, tyLe l₂ u₁, tyLe l₂ u₂]
```

その typed positions を交換した入力は admission できない。explicit inherited invariant の中では row も区間となり、4 row 比較、続いて 4 value 比較を出す。名指しした符号つき occurrence により、同じ実 assignment・同じ Int 値位置でも row の順方向のみが可能なことを `ContextDerives` で検証。任意の新規 checked source use の declared table は実 original formals に同じ順序で由来する。

## §6.2 の literal `ref _ int` は狭い R21 とは別

既存 `SourceHead` を **named lane** に固定し、元の singleton argument の上下へ実際に届く全ての authored origin が `ref` row point / ordinary Int point であるとする（関係のない原点は任意）。元の catalogue が本当に `[row,type]`、元の mode table が上記の順序なら、literal `ref _ int` の `SourceHead` は構成できない。

1. 普通の centered translator は primitive の全引数が value、nominal legacy でも全引数が type の場合だけ。従って混合 `[row,type]` ではない。これは legacy branch の型付き構文の制約。
2. `DeepRead` の ordinary 構成子は binder。nominal 構成子は native nominal endpoint を両側に要求する。元の `.ordinary (.base .int)` を rigid nullary `.app intName []` として読む構成子がない。この穴を variable に読み替えない。
3. 残りの joined variant source は元の literal app の構文と一致しない。

同じ実 source fixture の literal 版には適合モデルがあり、元の row と `.ordinary (.base .int)` の型比較が成立する。その事実をもって旧 literal head の証拠を作れない。言語の拒否／型エラーを追加しない。将来 literal を実装する際は、旧証拠を使い回すのではなく、実 primitive metadata・exact ordinary value を独立に照合する表現の承認と変換が別途必要（仕様の受理を決め直す話ではない）。§4.6 の bound `'f` 本体の rank-2 lowering は別の B3。

対象の新 production / standalone Audit は公式 Lean 4.35.0 strict にて 12 定理の標準公理のみ。旧 source/証拠/報告は無変更。
