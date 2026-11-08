# `|` はあらゆる計算を流す (conduit のように) (2026-11-08)

状態: 構想と、spec 3.9 への方向の反映。細部は未決。

## ユーザーの訂正 (2026-11-08)

「パイプの左辺を値としてでなく計算として受け取る」のは `catch` の特別扱いではない。**あらゆる計算が `|` を通して流せる**はずで、そうでないと conduit のような構成ができない。E7（`x | catch:` の左辺の effect が handler に届く）は、その一例にすぎない。

## 未決

1. 右辺が**値**を受け取る関数のとき（`x | print` のように）、左辺をいつ評価するか。「型が求められたときだけ」の需要駆動（`labeled` の cast と同じ流儀）で、値が求められたら評価して渡す、とするのが自然に見える。
2. 計算どうしをつなぐ `|` の意味。conduit なら `producer | transformer | consumer` で、producer の `yield` を consumer が受ける。Yulang では effect と handler で書けるはずだが、どの effect の対応で「つなぐ」のかを決める。
3. 結合力（3.9、`|` は全演算子で最も弱い）との整合。
4. 評価順と、effect の届き方（hygiene）。左辺の effect が右辺のどの handler に届くか。
5. 型。右辺の引数の型が「計算」（effect の行つき）であることの表し方。`['e] 'a` の計算を受け取る関数の型。

## 関連

`spec/03-expressions.md` 3.7（`catch:`）、3.9（パイプライン）、`spec/05-effects.md`、`notes/ideas/2026-11-08-label-receiving-values.md`（需要駆動の cast）。
