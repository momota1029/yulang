# 素材の所在地

取り出し方: `git show main:<path>`（main）、`git show archive/proof-sprint-2026-11-04:<path>`（旧スプリント）。
どれも**仕様ではなく素材**。そのまま写さず、読んで起こし直す。

注意: main の文書は effect 行の旧表記 `[a; 'b]`（`;` 区切り）を使っている。起こすときは新表記 `[a, 'b]` に直す（[traps.md](traps.md) T1）。

## main — 言語の説明（日本語が多い）

| 素材 | 行数 | 使いどころ |
| --- | --- | --- |
| `notes/design/yulang-language-report.md` | 1638 | 実装から抽出した全体レポート（日本語）。章立ての骨格にする |
| `docs/language/overview.ja.md` | 586 | 言語概要 |
| `web/docs/ja/reference/*.md` | 約30 | 利用者向けリファレンス（types, effects, functions, patterns, modules, casts, errors, operators, type-theory ほか） |
| `web/docs/ja/guide/pitfalls.md` | 166 | 既知の落とし穴（構文寄り） |
| `docs/language/stable-core.md` | 106 | 契約 v0 が約束する範囲 |

## main — 型・effect の意味論

| 素材 | 行数 | 使いどころ |
| --- | --- | --- |
| `spec/2026-05-31-effect-variable-subtractable.md` | 957 | effect subtraction、directed stack weight、handler hygiene |
| `spec/2026-06-02-role-system.md` | — | role、不変区間規則 |
| `spec/2026-06-04-method-selection.md` | — | `x.meth` の解決 |
| `spec/2026-06-06-invariant-type-sandwich.md` | 168 | compact 表現と中心変数の消去 |
| `spec/2026-06-13-computed-fetch-value-restriction.md` | — | 値制限 |
| `spec/2026-06-25-act-copy.md` | — | `act copy` |
| `notes/design/handler-row-subtraction.md` | 800 | handler による row 減算の設計 |
| `notes/design/2026-07-03-hover-public-type-projection.md` | 237 | 表示型の public projection（注釈と表示の乖離に関わる） |
| `notes/debugs/std-var-ref-effect-annotation.md` | 67 | 型引数注釈の effect 行が畳まれない例 |
| `docs/effect-inference-brief.md` | 139 | effect 推論の概説 |
| `docs/hidden-effect-evidence.ja.md` | 364 | 隠れた effect の証拠 |

## main — 標準 API・資源

`spec/2026-07-01-*`, `spec/2026-07-02-*`（file / server / instant / stable API）、`docs/language/*-contract.md`。
型推論の核とは別の層なので、後回し。

## archive tag — 旧スプリントの意味論文書（日本語）

`docs/yulang-semantics-and-soundness-ja.md`、`docs/yulang-whole-language-semantics-ja.tex`、`docs/yulang-proof-index-ja.md` など。
スプリント中に増築されたもので、実装の形に引きずられている可能性が高い。仕様の正本にはせず、「どんな性質を示そうとしていたか」の参照に使う。
