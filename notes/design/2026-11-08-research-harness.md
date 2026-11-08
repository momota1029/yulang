# 研究ハーネス: 作業者が替わっても Lean の証明研究が進む作り (2026-11-08)

状態: 構想と最初の実装（スクリプト 2 本とスキル）。意味論の決定ではない。
経緯: 2026-11-08 の M1 作業で、Pro・Terra・Sol・Astra と作業者が替わり、セッションが落ち、検証を毎回手で行った。
OpenAI の dots（常時稼働の定期エージェント。不安定な新システム）も使えそうなので、道具が落ちても研究が進む形を先に作る。

## 原則

1. **リポジトリが窓口**: 作業者は、`notes/` と branch の内容だけで再開できる。会話の記憶に頼らない。
2. **検証は作業者に依存させない（目標）**: 同じスクリプトで、誰が書いた成果も同じ基準で判定する。ただし現在の `verify-lean.sh` は作業者の checkout の中で作業者の Lean コードをビルドするため、敵対的な成果物に対しては安全でない（下の「検証スクリプトの限界」）。
3. **読み取り中心の定期ジョブから任せる**: 書き込み（commit・push・spec の編集）は、判断が要るので監督役が行う。ただし `verify-lean.sh` の実行は未検証の Lean コードのビルド（コード実行）なので、読み取り専用ではない。dots に任せる場合はサンドボックスか使い捨ての環境で行う。
4. **「証明できた」と「正しいものを証明した」を分ける**: 適合例（`notes/handoff/2026-11-08-m1-spec-examples-conformance.md`）を常設の物差しにする。
5. **ユーザーの設計判断は台帳に集める**: spec と復旧文書に分散した決定を、全作業者の入口にする（未実装: 下の「次」）。

## 構成要素

| 要素 | 場所 | 状態 |
| --- | --- | --- |
| 検証スクリプト | `tools/verify-lean.sh <repo-dir> <base-rev>` | 実装済み（Opus の点検を受けて強化）。build / Audit / 公理の集計 / 削除行 / sorry・axiom 系 / lake 設定の変更 / 新規ファイルの種類と import / Audit.lean の追記位置 / base の存在と祖先 / 未コミット変更 / 監督役の公理ゲート `tools/AxiomGate.lean` |
| 停止検知 | `tools/branch-stall.sh <remote/branch> <minutes>` | 実装済み。`lean/Yulang` と `lean/SpecExamples.lean` に触れる non-merge commit の最後の経過時間 |
| Codex の見張り | `tools/codex-watch.sh` | 既存 |
| 委譲の手順 | `rules/codex-delegation.md` と skill `codex-delegation` | 既存 |
| ハーネス全体の手順 | skill `yulang-lean-harness` | 新規 |
| 復旧用の依頼文書 | `notes/handoff/2026-11-08-chatgpt-prompt-m1-recovery.md` | 既存。決定が増えるたびに更新 |
| 適合例 | `lean/SpecExamples.lean` と上の一覧 | 既存。作業者が増やす |

## 作業者ごとの運用メモ（2026-11-08 の観察）

- **ChatGPT Pro**: 長く走って橋を積むのに強い。約 1 時間でセッションが落ちた。復旧は依頼文書の貼り直し。push 済みの状態から再開できる。
- **Codex（Terra / Sol / Astra）**: 1 巡 10〜40 分。sandbox の `.git` が読み取り専用で、commit は監督役が代行する。ネットワークなし。毎巡、検証の通る進みを出すが、核心の橋の手前で部品を足す方向に偏りやすい。設計ノートを先に書かせ、上から作らせると、枠は閉じる（Sol）。
- **dots（OpenAI）**: 常時稼働、定期実行つき、GPT-6 Astra で動く。API は未発表（第三者の記事による。一次情報で要確認）。不安定さがあるので、状態は常にリポジトリから復元できること。最初は検証・停止検知・記録だけを任せる。

## 検証スクリプトの限界

- 判定するのは機械的な条件のみ。定理の主張が元の主張と一致するか、モデルが本物の solver に合っているか、外側の定理が未証明の仮定（例: `FrontierExact`）を持っていないかは、人の読みと適合例で確かめる。
- **作業者がジャッジを操作できる経路が残る**: 作業者の checkout のビルドは、作業者の `lean/.lake`（古い `.olean` の再利用）と作業者の Lean コード（`run_cmd`・`#eval`・`elab` などの実行）を使う。スクリプトは、メタプログラミングの追加を `REVIEW` として出し（人が読む）、`lakefile`・`lean-toolchain`・manifest の変更、`lean/Yulang/*.lean` と `SpecExamples.lean` 以外の新規ファイル、import されない新規モジュール、Audit.lean の途中への挿入を FAIL にする。それでも敵対的な作業者に対しては、使い捨ての環境で、監督役が取得した commit の新しい worktree と、監督役が自分で作った `.lake` で検証するのが正しい（未実装。`lean4checker` による環境の再生も候補）。
- 公理の検査は二重: `Audit.lean` 自身の許可リストと、監督役所有の `tools/AxiomGate.lean`（`Init`/`Std`/`Lean`/`Lake` 以外の全モジュールの全定数を検査）。許可は propext / Classical.choice / Quot.sound。
- `Audit.lean` の出力は長く折り返されるため、`#print axioms` の集計は出力を連結してから行う（出力形式が変わると誤判定しうる）。
- `--no-build` は差分の検査だけで、PASS に「NO build」と表示する。

## 次

- 検証を、取得した commit の新しい worktree で行う形にする（`.lake` は監督役の `base` のビルドから複製）。
- 決定の台帳（日付つき、ユーザーの言葉つき）を一箇所に作り、spec と復旧文書をそこから参照する。
- 各巡の記録（所要時間、トークン、通った定理、未達）を `notes/` に残す形式を決める。
- dots に任せる最初のジョブ: 「`tools/branch-stall.sh` と `tools/verify-lean.sh` を定期的に回し、結果を報告する」。書き込み権限は与えない。
