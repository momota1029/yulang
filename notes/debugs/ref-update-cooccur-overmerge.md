# ① ref::update が cooccur で 3 変数を 2 変数に過剰マージ

## テスト
`display::dump::tests::render_compact_results_handles_ref_update_effect` — `crates/yulang-infer/src/display/dump.rs:2934`

## 入力（= `lib/std/var.yu` の ref::update そのもの）
```yu
act ref_update 'a:
  our update: 'a -> 'a

type ref 'e 'a with:
  struct self:
    get: () -> ['e] 'a
    update_effect: () -> [ref_update 'a; 'e] ()
  our r.update f =
    my loop(x: [_] _) = catch x:
      ref_update::update v, k -> loop(k f(v))
    loop((r.update_effect)())
```

## バグ表
| | |
|---|---|
| 期待値（正）| `ref<α & β, γ> -> (γ -> [β] γ) -> [α, β] unit`（3 変数 α,β,γ）|
| 実際値（誤）| `ref<α, β> -> (β -> [α] β) -> [α] unit`（2 変数に過剰マージ）|

## なぜ期待値が正しいか（テスト本体のコメントが仕様, dump.rs:2949-2952）
> 残留 effect は α・β の 2 変数のまま（`[α]` には畳まない）。α=残留, β=f の捕捉エフェクト(γ_f)。
> β は f の型内に**非対称な負極性出現**を持ち、**正極性でしか共起しない**ため、健全には統合できない
> （例: α=io, β=[io, undet]）。共変の join を自動計算しないので畳めないのが正しい挙動。

つまり α（loop の残留）と β（f の捕捉 effect）は別物。`ref` の `'e` は両方を受けるので `α & β`、
f の effect は `[β]`、結果 effect は `[α, β]`。これが principal。
実際値は β を value 型に再利用し、effect 残留を α 1 本に潰している＝**情報を失う過剰マージ**。

## 診断
memory `infer-test-pass-2026-06-06` / `project_infer_residual_regression` の**本丸**。
cooccur の極性解析が「正極性でしか共起しない（負側に非対称出現がある）変数」を別変数として保てず、
統合してしまう。病名は確定済み: Codex が共起分析＋極性消去を理解せず「守るべき変数集合」を後付けし、
偶然同出力だっただけ。正しい cooccur（論文 §4.3.1 の 3 規則）に戻せば影武者が連鎖除去されて
実装は**減る**。

## 見るべき場所（⚠️ 高リスク・2420 行・前科あり）
- `crates/yulang-infer/src/simplify/cooccur/` 一式（`polarity.rs` / `analysis.rs` / `representative.rs`）
- 関連: Task #2「cooccur を論文§4.3.1 の 3 つに掃除」。spec は `notes/design/2026-06-03-cooccur-cleanup.md`

## 修正方針
**単独 commit・他テスト回帰を最優先で監視**。cooccur の極性判定で
「ある変数が両極性で共起する場合のみ統合可」を厳密化し、片極性のみ（特に負側に非対称出現）の
変数は別に保つ。近縁の `coalesce_by_co_occurrence_keeps_ref_update_like_effect_vars_distinct`
（同セッションで ok）の挙動を壊さないこと。
影響が広いので、まず最小差分で `ref<α & β, γ>` の 3 変数が出るか確認 → 全 490 件を回す。

## ⚠️ 改竄防止
期待値の 3 変数形はテスト本体の長文コメントで根拠付き確定。**コメントごと握り潰して
2 変数に書き換える（＝典型的な改竄）のは絶対禁止**。3 変数が出ないなら STOP して報告。
