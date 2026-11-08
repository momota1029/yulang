# 監査用 dot の常設の指示 (Yulang2 再現監査) (2026-11-08)

このファイルは、**監査用の dot** が起きるたび（毎時の定期実行）に最初に読む、変わらない手順。具体的な指示は `notes/plan/dots-inbox-audit.md`。
Lean の証明用の dot（`dots-standing-orders.md`）とは別の dot・別のブランチ（`work/dots-audit`）。会話の履歴は毎回は渡らないので、状態はリポジトリに置く。

## 目的

旧世代 Yulang2 にあった規則で、新しい spec（`spec/`）と Lean の核に持ち込まれていないものを、ユーザーの記憶に頼らず、**Yulang2 の文書・実装・動く処理系**から洗い出す（計画表 T15）。権威はユーザーの決定で、Yulang2 の挙動は**素材**。作業者は意味論を決めない。

## 1 サイクルの手順（開始から 55 分、待機を作らない）

0. 最初に開始時刻を記録する（`date -u`）。
1. `integration/m1-final` を取得し、`notes/plan/dots-inbox-audit.md` を読む。`STOP` なら、何もせず報告に「STOP を確認」とだけ書いて終わる。
2. 前回の報告（`work/dots-audit` の `notes/audit/cycle-<N>.md` の最新）と、`notes/audit/` の表を読む。クラウド PC に前回の作業が残っていればそれを続ける。
3. **Yulang2 の処理系を用意する**（初回のみ。残っていれば再利用）: `git worktree add ../yulang-y2 origin/main --detach`（または `main` を別のクローンへ取得）、`cd ../yulang-y2 && cargo build --release -p yulang --offline`（約 1.5 分。`--offline` が通らなければ通常の `cargo build --release -p yulang`）。実行は `./target/release/yulang --std-root lib check|dump --poly|run <file>`。**初回の `dump` は標準ライブラリの処理で約 10 分かかる**（以後はキャッシュ）。実行時間の長い処理は、セッションが保持するバックグラウンド実行で回し、ログをファイルに取る。
4. inbox の「現在の指示」を実行する。調べた主張は、`notes/audit/` の表に 1 行ずつ足す（形式は下）。
5. 公開: push はできないので、GitHub アプリ経由で `work/dots-audit` ブランチに、**`notes/audit/` 以下の追加・変更ファイルだけ**を公開する。20 分ごとに中間公開する。
6. サイクルの最後（50〜55 分）に、`notes/audit/cycle-<N>.md`（N は 1 から連番）を書いて公開し、公開した tree を取得して照合する。報告には、扱った文書と主張の数、分類の内訳（一致／違う／欠落／未確認）、実機の実行回数と所要時間、型推論の核（B4/B5/B6）に響く欠落・違いの一覧、質問ノートを積んだか、できなかったことを書く。
7. 次のサイクルまで何もしない。**サイクルを早く終わらせない**: 指示の範囲が片付いたら、inbox の「次の文書」へ進む。

## 主張の表の形式（`notes/audit/y2-claims-<グループ>.md`）

1 行 1 主張。列: `ID`（例 `Y2-EFF-012`）／`出典`（ファイルと節または行）／`規則`（Yulang2 の主張を 1〜2 文で。日本語）／`例`（最小の Yulang のコード）／`実機の結果`（Yulang2 の型・診断・実行結果。実行したコマンドと一緒に。未実行なら「未実行」）／`新 spec`（該当する節、または「無い」）／`Lean`（該当する定理や定義、または「無い／未確認」）／`分類`（一致／違う／欠落／未確認）／`備考`。分類は根拠を備考に書く。文書と実機が食い違うときは、両方を書く。

## 守ること

- 意味論は決めない。「違う」「欠落」で、spec に入れるべきかに選択が要る点は、`notes/questions/` に質問ノートを 1 本（Yulang の例つき、遅延する案を先頭に）。確実な「欠落」（Yulang2 の文書・実機が一致して明確に定めている規則）は、spec の追記案として `notes/audit/spec-proposals.md` にまとめる。**`spec/` は編集しない**。
- 書き込みは `work/dots-audit` の `notes/audit/` と、質問ノート（`notes/questions/`）だけ。`integration/m1-final`、`yulang3`、`main`、`spec/`、`lean/`、`notes/plan/` には書き込まない。
- 実機の出力は、そのまま記録する。解釈は備考に分けて書く。型の表示は効果の行が省かれることがあるので、効果の規則は診断や実行の挙動と併せて確かめる。
- 確かめていないことを、確かめたと書かない。
