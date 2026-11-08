# 到達不能な後続 case arm の静的 effect 行

状態: **解消(2026-11-08, ユーザーの決定): 選択肢 1(保守的に含める)を採用する。** case 全体の静的な effect 行は、全 arm の guard と body の行を合流する。到達不能な arm の effect も含める。`spec/03-expressions.md` 3.7 に書いた。証明側は、`generate_common_case_exact` の行の規則を、全 arm の行の合流として定義してよい(独立 Common case 型規則も同じ)。実行の部分正当性(最初に合う arm だけが選ばれ、実 trace に到達不能な arm の effect は現れない)は別に証明する。

(原文)状態: 要確認。B2 の全 case 生成定理で必要になる行規則の選択。仕様変更・定理変更としては未承認。

## 既存の決定

- [spec/03-expressions.md §3.7](../../spec/03-expressions.md) は、最初に pattern が合い guard が真になる arm を選ぶ。
- [spec/03b-patterns.md §3b.3](../../spec/03b-patterns.md) は、先行部分が miss すれば残りの default を評価せず、そこでの effect も起こらない。
- [Common pattern 設計](../design/2026-11-07-common-pattern-environment.md) は、fallback 行を静的な上界とし、全 case の行・failure・coverage 接続を未完としている。
- 既存 `Core.CommonSyntax.Typing.branch` は両枝の行を上界へ合流する。これだけから case の到達不能 arm 規則を決めたとは扱わない。

## 問い

`emit : int → bool` が `Tick` を起こす既存関数であるとする。次の source は、実行時には必ず第一 arm を選び、`emit` を呼ばない。

```yulang
case 0:
    _ -> 1
    x if emit x -> 2
```

推論して表示する **case 全体の静的 effect 行**には、この到達不能な第二 arm の `Tick` を含めるか。

1. **推奨: 保守的に含める。** 全 arm を静的に型検査し、その guard/body 行の上界を合流する。実行順と実 trace から `emit` が呼ばれないことは別に証明する。既存 branch の行規則と揃えやすい。
2. 到達不能であることを静的に証明できる arm の行は含めない。全 arm の通常の型検査は保持するが、行の合流には ordered coverage / 到達可能性の証拠を使う。

第一 arm が effectful default を持つ場合や guard 付きの場合は、単なる coverage=true だけで後続の到達不能を結論しない。上の問いは、default も guard もない先頭 wildcard だけに限定する。

## 証明側への影響

どちらでも実 first-match evaluator と観測 path の定理は同じである。異なるのは、独立 Common case 型規則と、その行制約を生成する実アルゴリズムの statement。
承認前にこの選択を既成の仕様として `generate_common_case_exact` へ埋め込まない。
B2 worker は、既存の単相共有環境・source default scope・全モデル solved family・実行の部分正当性・整数 coverage の証明を継続する。
