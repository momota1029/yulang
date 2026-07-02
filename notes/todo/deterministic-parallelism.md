# 決定的並列性 TODO（地平線トラック）

出典: notes/design/2026-07-02-parting-assessment.md §7（Claude Fable 5、ユーザ承認済み）。
性格: **地平線トラック**。実装を急がない。ただし「定理」の部分は今すぐ使える。

## 主張

Yulang の設計原点は「並列が直列に見える」だった。現在の実行系に並列は
存在しないが、2026-07-02 までの決定群は**決定的並列性の条件をすべて
満たしている**:

1. state は純粋継続スレッディング — データ競合が構造的に不可能。
2. junction / undet の分岐は構成上独立（v1 決定2: 分岐ごとの snapshot と
   独立 commit）。
3. 非決定性はすべて host act registry の漏斗を通る — 並列化しても
   観測順序を registry で直列化・記録できる。

したがって:

> **junction の all / undet の探索を物理的に並列実行しても、
> プログラムの観測される意味は変わらない（決定的並列性）。**

commit の到達順（last-write-wins、v1 決定2）だけが並列化で変わりうるが、
これは仕様上すでに「到達順」と定義されており、直列実行でも保証していない。

## 今すぐ使える部分（実装ゼロ）

- 松田先生への研究相談資料に一節を足す: effect row 推論 + 純粋 state +
  handler ベース資源管理の組が、決定的並列性を「定理として」与えること。
  row subtraction の話と独立に立つ主張であり、teaser として強い。
- アドカレ / 公開文書の締めに使う: 中学生の頃の構想が、寿命・FFI・証明と
  同じ数本の原理から導かれる形になったという物語の結び。

## 実装するとしたら（順序だけ固定）

1. **意味論の文書化が先**: 「並列 all」の仕様を書く（どの分岐が並列可能か、
   host act の直列化点、commit 順の非保証の明文化）。実装より先に
   手計算で反例を探す。
2. worker 化の最小単位は「junction all の独立分岐」。continuation が
   Send にできるか（Rc → Arc の壁）が最初の技術的関門。これは
   Cranelift 継続表現（v2 R1）の選定と同時に検討するのが安い。
3. scheduler は structured-concurrency（notes/todo/structured-concurrency.md）
   の scheduler と同一物にする。並列とキャンセルを別機構にしない。
4. 計測 gate: 並列化は performance-localization の物差しに載せ、
   直列 VM を遅くしないことを維持条件にする。

## やってはいけないこと

- 定理の前提を崩す機能追加（可変な host 型、漏斗外の非決定性、
  scope なし ambient）。このトラックは他の全 TODO への**制約**として働く。
- 意味論文書より先に worker を書き始めること。
