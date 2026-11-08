# record pattern/default 順序: 上限付き試験

旧Y2 `d4c8bc8fc8a49173180932cd25921a2c41057354`、no-prelude、各CLI5秒上限。初期4入力12件に、明示許可された構文修正2入力6件を追加して計18件。repo変更・公開・buildなし。

| ID | 出典 | 規則 | 例 | 実機結果 | 新spec | Lean | 分類 | 備考 |
|---|---|---|---|---|---|---|---|---|
| PAT-ORDER-001 | spec/03b-patterns.md §3b.3 | 先行record subpatternがmissなら後続defaultを評価せずeffectも起こさない | run()でcaseを実行し外側catch。pattern `{x:1,y=ping::get()}`、scrutineeのx=0/1を対照 | 修正版miss: check0/dump0/run0 roots[20]。match: check0/dump0/run1 runtime unsupported-runtime-feature: direct abortive continuation binding | §3b.3左→右照合・打切り | 今回対応定理は未照合 | 未確認 | missでfallback20を得た点は規則に整合。match側はruntime未対応で値99を取得できず、効果観測対照は完了していない。成功した完全な順序試験とはしない。 |

原ログは `raw.json`（初期12件）、`fixed-raw.json`（修正6件）、`runtime-cycle-2-pattern-order.md`（全件）。初期inline catchの4入力は最終閉じ括弧位置の構文エラーでcheck/run1。dump exit0だけで受理成功にしない。修正版は別関数 `our run() = case ...` と `catch (run()): ...` を使用。

handler armを `ping::get(), k -> 99` としたため、その経路の実行で `direct abortive continuation binding` が未対応となった。matchでこのエラーを観測したことは記録するが、backend内部traceを取っておらずdefault effectが確実に起きた証明に置き換えない。追加実行枠を使い切ったため再修正なし。default式は先行binderを参照しておらず、binder scopeとの交絡は意図的に避けた。
