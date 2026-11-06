# ChatGPT Pro への次の依頼 (M1 の後に出す, 2026-11-07)

M1 の途中結果を `integration/types` に取り込んだ後に出す(2026-11-07)。
回数制なので、M1 の結果を確認してから、まとめて 1 回で頼む。

```text
yulang の integration/types ブランチ(https://github.com/momota1029/yulang)を pull して、続きを進めてください。
(前の依頼で積んだ integration/m1-lemmas は、私が確認して integration/types に取り込み済みです。)
途中で私に確認を取らずに、できるところまで自走し、こまめに push してください。

## ブランチ
integration/types から新しいブランチ integration/m1-solver を切って、そこへ push する。
integration/types と yulang3 には push しない(別のエージェントが integration/types 側で M2 を進めています)。
作業の途中で origin/yulang3 に仕様の更新が入ることがあるので、時々 merge して、ビルドと Audit が通ることを確かめる。

## 進め方
- 小さな単位で commit と push を繰り返す。
- 仕様(spec/)が黙っていて決められない所は、止まらずに notes/questions/ に問いとして積む。
  **ユーザーに見える Yulang のコードで違いが書ける問いだけ**にすること。Lean の内部モデルの都合
  (mask、layer、cache の形など)は、自分で決めて、決めた理由と代案を問いではなく設計メモに書く。
  問いは 1 問ずつ・Yulang のコードの例つき・選択肢つき・あなたの推奨を先頭。専門用語は、使う前に説明する。
- sorry、追加の公理、native_decide を使わない。lake build と lake env lean --trust=0 Audit.lean を通す。
- 既存の定理の主張を弱めない。README の「示さないこと」の列を、証明した範囲と一致させる。

## 読むもの
1. lean/README.md の「Core (M0)」「M1」の節と、notes/questions/2026-11-06-m1-model-contracts.md、
   notes/questions/2026-11-07-demand-model-contracts.md(Q1 と Q5 は回答済み。Q4 は原則に従う仮の前提)
2. notes/design/2026-11-07-yulang2-lowering-hotspots.md(Yulang2 の遅さの整理と、Yulang3 への含み)
3. notes/handoff/2026-11-05-lean-proof-handoff.md(決定 1〜47)
4. spec/04-types.md の 4.3(record の残りへの要求の回し方)と 4.7b、spec/07-display.md の 7.4b
5. notes/design/2026-11-06-integrated-inference-plan.md、notes/design/2026-11-06-rust-oracle-plan.md

## 作業 1: M1 の残り(最優先。新しい数学の部分)
目的: 統合した入口 `Core.infer` が、lambda・application・branch・let・pair・variant・record・recordDefault・field を
含む断片で、完全な主型性を満たす。
   Typing [] e c  ↔  ∃ S ∈ infer e, ∃ parameters, S の具体化 ≤ c
推論成功・solver の解・fuel を前提にしない。`.rejected` ↔ 型付け不能。この断片で `.unsupported` は出ない。
旧入口との関係は決定 46 の形(旧 instance ⇒ 新 instance。新 instance からは要求で等しい旧 instance がある)。
README の M1 の節に残っている契約を順に閉じる:
1. constructor を含む全入力に対する分岐付き飽和と、受理枝から Closed cache を得ること
2. variable・mask・regular graph を含む target 引数への、arrow の完全な分解(README の「示さないこと」)
3. 新しい solver の solved instance への接続(presence_solve_complete、presence_generate_exact の具体モデル版)
4. 由来のない非 guarded な tail の循環の求解、具体的な mask family の構成
行き詰まる所は、欠けている補題を正確に書いて、別の項目へ進む。

## 作業 2: 速さの根拠になる理論
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

## 作業 3: 名前解決と lowering の設計(Rust の oracle の設計メモへの節)
notes/design/2026-11-06-rust-oracle-plan.md に節を足す。Yulang2 の lower.bodies・lower.drain・lower.resolve の
熱い所(上の 2 のメモ)を避ける、Rust の前段の設計。
- 名前・path・演算子の解決: arena、path の intern、モジュールの map を持続的な構造にする。
- selection の解決を SCC ごとに一度にする設計(role の method 名の索引)。
- 「全 binding を lowering し終えるまで量化できない」制約(Yulang2)を、モジュール単位の量化でどう外すか。
- 測りたいこと(メモの 4 節)を、最初のベンチとして決める。

## 返信に含めてほしいこと
1. 追加した定理の名前と、日本語で読める主張(量化子と前提を省略しない)
2. 閉じていない所と、欠けている補題
3. ビルドと Audit の結果の末尾
4. notes/questions/ に積んだ新しい問いの一覧
```
