# Yulang Hardening Phase

2026-06-23 からしばらくは、Yulang を「アドホックに動く言語」から
「理論の不変量に守られて動く言語」へ寄せる hardening phase として扱う。

目的は機能追加ではなく、今回の `ref.update` / directed stack weight 修正で得た不変量を、
テスト・文書・metrics・release 運用へ固定することである。

## 直近一週間

### 1. Stabilization Freeze

新機能を足さない。次だけを見る。

- ハング再発テスト
- public signature golden test
- std smoke
- playground smoke
- solver trace の整理
- panic / timeout / exponential blowup の分類

型表示だけではなく、推論結果の構造が守られていることを見る。

固定したい性質:

- public signature に stack evidence が出ない。
- 内部には必要な evidence が残る。
- escape すべきでない row / stack id が public scheme へ出ない。
- handler boundary を越えて private evidence が漏れない。

### 2. Solver Invariant Document

`docs/infer-solver-invariants.md` を solver hardening の入口にする。
実装を触る前に、public type boundary / row-tail polarity / replay termination /
handler hygiene のどれに関わるかを明示する。

### 3. Metrics Are Observation-Only

まだ高速化しない。
まず opt-in metrics で、どの pass が重いかだけを見る。

見たいもの:

- slot count
- row variable count
- edge / bound count
- SCC count
- replay count
- max replay depth
- cache hit rate
- infer / mono / run の phase time

metrics は環境変数か feature flag で有効化し、デフォルト出力を汚さない。
現行で拾える counter と不足している counter は `notes/todo/static-analysis-speed.md` の
`2026-06-23 hardening metrics inventory` に置く。

2026-06-24 時点で `check-poly` timing block に出る hardening metrics:

- `infer.type_var_count`
- `infer.row_tail_var_count`
- `infer.type_node_count`
- `constraint.edge_count`
- `constraint.replay_generated`
- `constraint.replay_enqueued`
- `constraint.replay_accepted`
- `constraint.replay_duplicate`
- `constraint.replay_trivial`
- `constraint.max_replay_inputs`
- `constraint.max_replay_generated`
- `constraint.max_replay_enqueued`
- `constraint.max_replay_accepted`
- `constraint.max_replay_duplicate`
- `constraint.max_replay_trivial`
- `constraint.max_replay_var_var`
- `analysis.scc_component_count`
- `analysis.quantify_max_component_defs`
- `analysis.quantify_generalize_roots_with_restarts`
- `analysis.quantify_generalize_max_iterations_per_root`
- `analysis.quantify_generalize_max_restarts_per_root`
- `analysis.role_demand_count`
- `analysis.role_resolve_candidate_scans`
- `analysis.role_resolve_prerequisite_candidate_scans`
- `analysis.role_resolve_candidate_cache_hits`
- `analysis.role_resolve_candidate_cache_misses`

すぐ使うコマンド:

```sh
timeout 180s cargo run -q -p yulang -- --std-root lib check-poly-std examples/showcase.yu
timeout 240s cargo run -q -p yulang -- --std-root lib --runtime-phase-timings --no-cache run --print-roots examples/showcase.yu
```

現時点では、新しい探索停止や高速化は入れない。

### 4. Public Signature Golden Tests

標準ライブラリの public surface を canary として固定する。

優先対象:

- `std.control.var.ref.update`
- parser combinator smoke
- `each` / list smoke
- handler / catch / resume の小さい例

見たい性質:

- stack evidence が public 型に漏れない。
- effect row が期待する残り方をする。
- 型表示だけでなく、必要なら内部正規化結果も検査する。

## 次の一ヶ月の柱

### A. 型推論コアの公理化

実装上の名前と理論概念を対応させる。

- `AllExcept`
- stack evidence
- signed displacement
- replay graph
- public type normalization
- `std.control.var.ref.update` の高階 effect

成果物:

- solver invariant doc
- code anchor の対応表
- open question の一覧

### B. Playground / LS / Docs の見せ物化

表では次を見せる。

- Python 風に軽く書ける。
- JS 風に playground で遊べる。
- ML 風に型が強い。
- effect で `each` / parser / warning / early return が自然に書ける。
- Zed と playground で同じ surface を見せる。

理論は最初から前面に出さず、触ったあとに深掘りできる導線として出す。

初期の外向け入口は `docs/effect-inference-brief.md`。
ここでは `principal type` を単独で強く主張せず、
`principal-style public signatures` と `handler hygiene` を前面に出す。
説明用の小さい入力は `examples/effect-hygiene/` に置く。

### C. Release 運用の固定

playground が `main` 直結だと、型推論改革のたびに公開物が揺れる。
次の分離を検討する。

| 対象 | 役割 |
| --- | --- |
| `main` | 基本安定 |
| feature branch | Codex / 実験作業場 |
| release tag | stable playground が参照 |
| nightly playground | 壊れてよい実験場 |
| stable playground | README / 記事から飛ばす場所 |

初期対応は `notes/todo/release.md` へ具体化する。

## Codex に投げる単位

### 1. Invariant Doc

```text
Goal:
型推論 solver の理論的不変量を docs/infer-solver-invariants.md に整理する。

含める内容:
- public type boundary
- stack evidence visibility
- row-tail polarity
- replay graph termination
- signed displacement cycle
- handler hygiene
- std.control.var.ref.update が守るべき性質

制約:
- 実装変更はしない。
- 現在のコード名と理論概念を対応づける。
- 未確定の部分は Open question として明示する。
```

### 2. Metrics

```text
Goal:
infer / mono / run の主要 pass に軽量な metrics を追加し、重い smoke で何が増えているか見えるようにする。

見たいもの:
- slot count
- row variable count
- edge count
- SCC count
- replay count
- max replay depth
- solve_slots time
- role demand count

制約:
- デフォルト出力は汚さない。
- 環境変数か feature flag で有効化。
- 最適化はしない。
```

### 3. Public Type Golden Tests

```text
Goal:
標準ライブラリの public signature golden tests を追加する。

対象:
- std.control.var.ref.update
- parser combinator smoke
- each/list smoke
- handler/catch/resume の小さい例

見たい性質:
- stack evidence が public 型に漏れない。
- effect row が期待する残り方をする。
- 型表示だけでなく内部正規化結果も検査する。

制約:
- 見た目だけの修正は禁止。
- 失敗時にどの evidence が漏れたか分かる diagnostics を出す。
```

## 今日は深追いしないこと

- solver 大改造
- mono 高速化
- VM 高速化
- parser 機能追加
- native backend 復活
- Zed 拡張の深掘り
- 記事本文の執筆

今日やるなら、デプロイ確認、作戦メモ、Codex 用タスク文面、fixture / golden の最初の固定まで。
