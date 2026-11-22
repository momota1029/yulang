# I-60: record の下端・上端を読めても、実中心の由来だけが未完了の場合

## 案 1（遅延・現証人境界のまま）

下端と上端の支持があれば候補照合はできる。実中心の record 捕捉を正当化する supported read または承認済みの区間射影がなければ、候補を確定・発行しないで保留する。未完了出力の等式自体は通常状態に保持する。根 K2 はこの例にはなく、I-58 の共有変数の等式欠落で保留にした例でもない。

## 案 2（別の、支持だけを使う record 射影が承認される場合）

両端の実支持、区間と record の構造が独立に十分なら、未完了側の RHS を使わずに実中心の可視 field・残余を通常の構造射影で再構成する。それができる場合だけ進める。等式が真というだけで支持へ昇格する案や、旧 Local に合わせて普通行を読む案ではない。どの record 射影が承認済みか、特に open/closed の残余の扱いを確かめたい。

## Yulang での状況（模式例）

```yulang
role Hold 'u:
    type witness
role W 'u:
    type out
role Pick 't:
    type out

impl W 'u:
    where 'u: Hold
    type out = {x: int, y: int}

impl Pick {x: 'a, ..'rest}:
    type out = 'a
```

需要は `'u: W(out = 'center)` と `'center: Pick(out = 'result)`。別のソース制約から `'lo <= 'center <= 'hi`、両端の record 頭は分かるが、実中心の record 行の由来は未解決の `Hold` を持つ W の出力のみ、という状態を考える。上の断片そのものを Rust 実行してこの状態に到達したとの主張ではない。

## Lean で確認済みの切れ目

`GeneralDeclarativeWitnessCut334`。checked な実 record impl、支持された両端、有効な通常モデル、I-59 の非循環、実コンパイラによる固定出力 `5=3`、同じ ordinary receipt を持つ。旧 `Local59 / Staged` は selected。現証人分類では、実中心名 1 に届く支持された alias が他名にならず、名 1 の RHS の由来は未完了 owner 100 のみ。named・inline・現行 projected のどれでも中心を読めないことを証明し、pending、selected 辞書なしを確認した。旧 solver が実際にこの状態を返すこと、または言語全体の不一致は未証明。案 2 は未証明・未実装。
