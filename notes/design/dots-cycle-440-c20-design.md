# C440 — C20 の狭い source/check/sound の設計

基準: integration/m1-final `1d2084ac7278aa7b9eb29eea86caaf740a7bc567`、C439 技術 tree `3fa551ff461d24ab106f9dca1f55cdefd742b49e`。I-74（一行のみ）、I-78、I-79。範囲: §6.5 L431–435、C423 C20（X14/X17/X19）。
 
- 既存の `ModeWindow`/`DeepRead` に、元の一つの `Outer(Inner 'a)` 候補、元の修飾された source endpoint、および実際の宣言 mode を渡す。外側は unary invariant、内側は unary used value mode。内側の端点を一つの点に潰さず、継承した invariant で両側・交差を検証する。where/出力なしに限る。中心名は比較の成功から推定せず、元の中間名と対応する明示的な raw 観測を記録する。
- K2 は source で裏づけられた一つの raw 行だけを調べてはならない。元の raw グラフ上で実際に訪れる可能性のある root と、該当する nominal 行の第一引数がすべて同じ中の site を指すことを検証し、その両方を別々に検査する。葉の binder はその先を調べない。追加の raw 行が競合するか証明書外なら scoped checker は false。言語の拒否とは言わない。
- 従来の R19/check/sound の定義は無変更。実際の独立 source match と同じ state の有限 trace/元の capture から辞書を出し、追加 witness は元の観測の位置と raw 証明データ（答え、capture された型、見かけの意味論を渡さない）だけ。定理は同じ外形: `check ... = true → ClassifiedAs ... ∧ ∀ m, Fits ... m → ReportEvidence ...`。正の真の nested source と、宣言モード・逆向き obligation・raw cycle を識別する負例を実入口で検証して初めて scoped 行を閉じる。
- 深さ 2 は入口の証明書範囲で、言語の再帰的な比較に深さ上限を入れない。固定された `list (list int)/list (list float)` のような非合致について、rows 不足を新しいエラー判断に置き換えない。既存の再帰的 ContextDerives と比較できる control を別途検証する。
