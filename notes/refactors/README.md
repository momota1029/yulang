# Yulang リファクタ候補ノート

建て増しを重ねた Yulang のソース（約 19.7 万行 / 11 クレート）を一周見渡して、「ここ匂うかも」と感じたスポットをクレート別に書き出したものだよ。直す前の "嗅ぎメモ" であって、どれを実際に直すかは別の話。優先度や順序は後で考える前提で、まずは並べてあるだけ。

各ファイルの中身は、

- **場所** (`file.rs:行`)
- **匂い** (一行で分類)
- **スニペット** (実際のコード 15〜30 行)
- **所感** (どう変か、もし直すならどの方向か、提案調で)

という形式に揃えてあるよ。

## クレート別ノート

| ファイル | 対象 | 見つけた匂いの数 | 大まかな問題感 |
| --- | --- | --- | --- |
| [yulang-parser.md](./yulang-parser.md) | `yulang-parser` (16k 行) | 12 件 | sink start/finish の繰り返し、`emit_invalid` の不揃い、深い match ピラミッド |
| [yulang-infer-core.md](./yulang-infer-core.md) | `yulang-infer/src/` (export 除く) | 12 件 | `LowerState` の肥大化、`freeze` ラッパ多段、`DeferredSelection` の暗黙順序、RefCell 密集 |
| [yulang-infer-export.md](./yulang-infer-export.md) | `yulang-infer/src/export/` | 12 件 | `principal.rs` と `complete_principal.rs` が並走している疑い、プロファイル計測がロジックに混ざる |
| [yulang-runtime.md](./yulang-runtime.md) | `yulang-runtime` (60k 行) | 14 件 | `principal_unify.rs` (9000 行)、`substitution.rs` のブール引数だらけ、巨大関数 |
| [other-crates.md](./other-crates.md) | `yulang-native` / `yulang` / `yulang-sources` / `yulang-wasm` / `yulang-editor` | 12 件 | `cps_repr_cranelift.rs` (8680 行)、`main.rs` (5881 行)、`_legacy` 残骸 |

## ざっくり共通している匂い

- **巨大ファイル**: `principal_unify.rs` 9039 行 / `cps_repr_cranelift.rs` 8680 行 / `cps_lower.rs` 6496 行 / `main.rs` 5881 行 / `check.rs` 5298 行 など、2000 行超のファイルが二桁ある。
- **ほぼ並走している兄弟ファイル**: `principal.rs` ↔ `complete_principal.rs`、`lower_effect_stmt` ↔ `lower_effect_terminator`、`remove_consumed_effects` ↔ `select_consumed_effects` など、責務が近すぎるものが散見される。
- **ブール盲目**: 引数に `bool` が複数並ぶ関数。意味が引数名に書かれていても、組み合わせの意味は本人しか知らない状態になりやすい。
- **プロファイル/ログがロジックに混ざる**: `eprintln!` や `Duration` 計測がパス本体に直接書かれているため、行数の体感ほど純粋なロジックは多くないファイルもある。逆に "業務ロジックとクロスカッティング" の分離余地。
- **`_legacy` / `_old` / `_v2` の名残**: `inject_extra_handlers_legacy` のように、置き換え済みの旧版が残っている箇所が複数。
- **`unwrap()` / `expect()` の前提条件が暗黙**: パスごとの不変条件がコメントなしで `unwrap` に集約されているところは、後から読むと「ここ落ちる条件は？」と詰まりやすい。

## 使い方の提案

このまま全部に手を出すと体力が持たないから、もし着手するなら次の順で重みを見て選んでみるのが楽かも:

1. **小さく独立な勝ち筋** — `yulang-parser.md` 1〜2 件 と `other-crates.md` の `_legacy` 削除あたりは、影響範囲が局所的で取り掛かりやすそう。
2. **`principal.rs` ↔ `complete_principal.rs` の構造調査** — 直す前に「本当に並走か / 微妙にズレているか」を一度確かめると、今後の意思決定が軽くなりそう。
3. **`LowerState` / `Infer` 分割の設計検討** — これは大物。手を出す前に notes に設計メモを書いてから動く方が安全。

直さなくていい、と聞いてるので、ここでは候補出しまでで止めておくね〜。
