# 引き継ぎ 2026-11-04: 白紙化・日本語仕様・パーサの穴の解消

別チャットで続けるための引き継ぎ。Claude のメモリ `yulang3-restart-spec-and-parser-closure-2026-11-04` と同じ内容。
状態: ブランチ `yulang3`、`origin/yulang3` に push 済み（この文書を足す commit を除く）。

## 現状

- 10 月の自走型証明スプリント（約 6800 commit、閉じた定理 0）を tag `archive/proof-sprint-2026-11-04`（`7c889aa9c`）に凍結した。
  型推論器、HIR、runtime、Lean、sprint 運用は作業ツリーから外してある。必要なものは `git checkout archive/proof-sprint-2026-11-04 -- <path>` で**一つずつ**取り出す。まとめて戻さない。
- 残している実装は `crates/chasa-recover`、`crates/yu-syntax`、`tools/xtask`。
- `AGENTS.md` と `rules/` は新運用に書き直した（自走ループ、sprint、question board は廃止）。
- `spec/` に日本語の言語仕様を起こした（章 1〜9）。状態の凡例は 確定 / 要確認 / 未定。出典のない文は書かない。意味論はユーザーが決める。
  罠台帳は `spec/traps.md`（T1〜T6）、素材の所在は `spec/00-sources.md`。
- パーサの穴 11 件を全部塞いだ。設計と判断の記録は `notes/design/2026-11-04-parser-gap-closure-addendum.md`（Authoritative）。
  `spec/` の構文例 80 個はすべて `Error` / `Missing` / `Invalid` なしで読める。`spec/parser-gaps.md` は空。
- `cargo test --workspace` は全部通る（`yu-syntax` は 1559 件と統合 11 件）。

## 次の入口（ユーザーに聞いたまま未回答）

1. `spec/` の `要確認` 約 45 節を **1 問ずつ**潰す。ユーザーはファイルを直接読まないので、質問には例と詳細をチャットに書く。
   保留中の質問: M2（`case` / `catch` の再帰 label の書き方）、N1（`act copy` で helper が source の operation を呼ぶときの付け替え）。
2. 型推論の核の計算体系を Lean と日本語文書で先に書く。実装は核から導く。旧 Lean の 717 定理は採掘場で、土台にしない。
   手がかりは T1〜T6、章 5.5、章 6 の cast 合流（union を保持し、期待型で cast し、期待がなければ警告）。

## 暫定・未完了

- 章 5.5 と 7.3 の「型変数に属性を足す」という説明枠と、`@∅` などの表示は暫定。撤廃・変更の可能性が高く、`'e?` 記法が入る見込み。入る前に固定したい振る舞いがあれば先に聞く（J6）。
- 意図的に残している未完了: 選ばれた `yulang` Yumark fence の本文。埋め込み Yulang の AST と direct CST の等価性の証明、および gate 3・4 の完了認定（O6）。
- `yu-syntax` のテスト時間は、深さ 10,000 のテストのせいで約 18 秒。

## 作業の仕方

- パーサ修正は Codex に 1 項目ずつ委譲した（`codex_execute` / `codex_continue`、`terminal: false`、`model` と `reasoningEffort` は呼び出しパラメータで明示）。
  モデル名は古くなるので、呼ぶ前に `models_cache.json` で確認する。出力が巨大でトークン超過したら、保存先 json を `jq -r '.status,.agentMessage'` で読む。
- Codex の報告は鵜呑みにしない。`cargo test -p yu-syntax`、`cargo fmt --check`、実 parser で自分で確かめてから commit する。
- Codex が既存テストの期待値との衝突で止まったときの基準:
  1. 見本の token を置き換えれば契約が保てる → 置換する（WP コメント付き）。
  2. 契約自体が成り立たなくなった → その行だけ削除し、新しい真実を別のテストで固定する。
  3. 本物の挙動変更 → 止めて報告する。
  設計文書どうしが衝突したら、後発で明示的に訂正・延期したほうが勝つ。
- 実 parser で仕様例を確かめる道具は一時物。`crates/yu-syntax/examples/` に dump 用 example を置いて build し、バイナリを `/tmp` へ退避してから example を**消す**（`git add -A` で混入させない）。
