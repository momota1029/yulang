# ChatGPT Pro への次の依頼 (M1 の後に出す, 2026-11-07)

M1(型モデルの統一, ブランチ `integration/m1-lemmas`)が戻ってから出す。
回数制なので、M1 の結果を確認してから、まとめて 1 回で頼む。

```text
yulang の yulang3 ブランチ(https://github.com/momota1029/yulang)を pull して、続きを進めてください。
(前の依頼で積んだブランチ integration/m1-lemmas は私が確認して取り込み済みです。)
途中で私に確認を取らずに、できるところまで自走し、こまめに push してください。

## 進め方
- 小さな単位で commit と push を繰り返す。push 先は yulang3。
- 仕様(spec/)が黙っていて決められない所は、止まらずに notes/questions/ に問いとして積む
  (1 問ずつ・例つき・選択肢つき・あなたの推奨を先頭)。仮の前提と明記して、依存しない部分を進める。
- sorry、追加の公理、native_decide を使わない。lake build と lake env lean --trust=0 Audit.lean を通す。
- 既存の定理の主張を弱めない。README の「示さないこと」の列を、証明した範囲と一致させる。

## 読むもの
1. notes/design/2026-11-07-yulang2-lowering-hotspots.md(Yulang2 の遅さの整理と、Yulang3 への含み)
2. notes/handoff/2026-11-05-lean-proof-handoff.md(決定 1〜47)
3. notes/design/2026-11-06-integrated-inference-plan.md、notes/design/2026-11-06-rust-oracle-plan.md
4. lean/README.md

## 作業 1: 速さの根拠になる理論(最優先)
目的: 「速くしても正しい」の根拠を Lean の定理にする。参照実装の抽象的なコストモデルでよい。
1. 局所性の定理: SCC 確定時の selection(`x.method`)の解決(MethodResolution、決定 29)が、
   他の SCC の解決順序に依らない。全体の固定点ループが要らないことの根拠。
2. コストの上界: 飽和(saturate_capacity は証明済み)に加えて、selection の解決・scheme の具体化・
   簡約(TypeSimplification)のステップ数の上界を、入力の大きさの関数として示す。
3. cache の正しさ: モジュール M のソースと、M が依存するモジュールの interface(標準形、
   spec/07-display.md 7.4b と 4.7b)が変わらなければ、M の interface は変わらない。
   標準形が interface の同値を完全に決める(等しい interface ⇔ 同じ標準形)こと。
4. 増分更新の正しさ: 変更したモジュールの依存先だけを再計算した結果が、全体を再計算した結果と、
   標準形で等しい。accepted_export_independent(公開型は後続の補完に依存しない)との関係。

## 作業 2: 名前解決と lowering の設計(Rust の oracle の設計メモへの節)
notes/design/2026-11-06-rust-oracle-plan.md に節を足す。Yulang2 の `lower.bodies`・`lower.drain`・
`lower.resolve` の熱い所(上のメモ)を避ける、Rust の前段の設計。
- 名前・path・演算子の解決: arena、path の intern、モジュールの map を持続的な構造にする。
- selection の解決を SCC ごとに一度にする設計(role の method 名の索引)。
- 「全 binding を lowering し終えるまで量化できない」制約(Yulang2)を、モジュール単位の量化でどう外すか。
- 測りたいこと(メモの 4 節)を、最初のベンチとして決める。

## 作業 3: M1 の残り
M1 の結果(README の M1 の節)で、閉じていない補題が残っていれば、続けて進める。
統合の入口 `Core.infer` が、lambda・application・branch・let・pair・variant・record・recordDefault・field を含む
断片で、完全な主型性(Typing ↔ ∃ S ∈ infer e, S の具体化 ≤ c)を満たし、`.unsupported` が出ないこと。

## 返信に含めてほしいこと
1. 追加した定理の名前と、日本語で読める主張(量化子と前提を省略しない)
2. 閉じていない所と、欠けている補題
3. ビルドと Audit の結果の末尾
4. notes/questions/ に積んだ新しい問いの一覧
```
