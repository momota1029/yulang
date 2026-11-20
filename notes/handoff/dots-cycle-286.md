# dots-main cycle 286: 入れ子出力の実初期状態からの全経路

対象は実 252/271 の葉一つ。入力 `F(Int)` と宣言の出力テンプレート `F(F(a))` から、出力座標 3 の型が `F(F(F(Int)))` に同値になる。今回は 285 が扱った据付後だけでなく、実初期状態からのすべての mixed-kernel 経路を扱った。

## 結果

- **健全性・完全性（据付の前後）**: `GeneralRebaseDepthPreAnchor286.initial_models/advance` と `GeneralRebaseDepthPreInstall286.installed_check`。任意の据付前到達点・完全割当てについて、生 snapshot と全 journal のモデルは元の条件と同値（0,1 は Int、2 は F(Int)、3 と他の型座標は自由）。見直しはこれを保存する。その位置にある実候補について `PreAvailable286.offers` はどの前半経路後にも据付可能であることを示す。許された据付は、その完全割当ての 3 に三重 F の条件を加える。直後の生 snapshot だけのモデルは引き続き元の条件 (`CrossAnchor286.raw_check`)。全 journal と生 snapshot を同一視していない。
- **停止性・補助（実経路）**: `GeneralRebaseDepthFullRank286.initial_accessible/complete_bound` と `GeneralRebaseDepthFullTrace286.decomposes/maximal_result/finishes`。この実初期状態からの任意の経路は、認証済み refresh のみか、refresh・一度の据付・refresh に分解される。最大は 3 手で、任意の途中から安定点に延長できる。どの極大経路も必ず一度据え付け、V8 で `.selected 0 []` と対象範囲の EvidenceAt が得られる。
- **健全性・完全性（停止条件と順序）**: `GeneralRebaseDepthSchedule286.exact_terminal`、`GeneralRebaseDepthScheduleWord286.permutation`、`GeneralRebaseDepthTraceCost286.maximal_trace_exact`、`GeneralRebaseDepthBudgetExact286.attained_from_prefix`。任意の実到達点で、未認識の 0 と 1 はそれぞれ単独で認識できる (`ScalarOffer286.offers`)。据付済みで両方が認識された場合に限って生の Step がない。極大経路は、一度の据付と一度の同時 refresh（2 手）、または一度の据付と二度の個別 refresh（3 手）。同時 refresh は据付の前後どちらでも実現し、個別の 3 手は全 6 順序が実在する。任意の途中から、測度「据付が未了なら 1 ＋ 未認識の 0,1 の数」と同じ手数をかける極大延長が存在する。
- **健全性・完全性（辞書とモデル）**: `GeneralRebaseDepthPreEvidence286.exact_before/same_joint_everywhere/pre_noncoverage` と `GeneralRebaseDepthReachableReadback286.public_exact/public_inflation/canonical_from_initial`。任意の実到達点・同じ完全割当て・任意の payload について、全 Models と生 Evidence の同時成立は三重 F を含む型の検査と葉 `.node 0 []` に一致する。据付前にも出力条件を満たす割当てには条件付きの証拠があるが、出力条件を満たさない生モデルには証拠がない。他の行を自由に選んで正準補完できる。出力を計算した補完割当てを、任意の元の割当てと取り違えない。
- **健全性・完全性（ドライバとの対応）**: `GeneralRebaseDepthSimulation286.shadow/exact_lift/visible_iff_install` と `GeneralRebaseDepthSemanticTransitions286.same_view_iff_same_models/visible_iff_strict/raw_halt_iff`。任意の実到達点で 271 のコンパイル済み一歩は実据付と双方向に対応し、すべての refresh は射影上で静か。任意の二つの実到達点の射影が等しい iff 全 Models が完全割当てごとに等しい。射影が変わるのは全 Models が真に狭まる場合だけ。ドライバが止まった直後も生の Step は残りうる。
- **補助・反例（商の限界）**: `GeneralRebaseDepthExactEnd286.exact_terminal_known/output_gap` と `GeneralRebaseDepthNonunique286.not_raw_unique`。すべての実極大終点で生 Known 座標はちょうど 0,1,2。3 は全モデルで値が決まっても生 Known ではない。終点間で全 Models と同じ割当ての Evidence は一致するが、生終点の同一性は偽。実 2 手の終点二つを作り、一方の認証済み refresh に反射的な型制約を入れると、生の ordinary リスト長が違う。

## 追加ファイルと検証

- 新しい `lean/Yulang/GeneralRebaseDepth*286.lean` は 29 本。前半・据付: `PreAnchor`, `PrePlan`, `PreInstall`, `CrossAnchor`, `CrossWitness`, `EnableShape`, `EnableSafety`, `PreAvailable`。経路・測度: `Phase`, `FullRank`, `FullTrace`, `PreSharp`, `RefreshTrust`, `ScalarMark`, `ScalarOffer`, `Schedule`, `ScheduleWord`, `ExactEnd`, `Batch`, `TraceCost`, `BudgetExact`。観測: `PostQueries`, `Confluence`, `Nonunique`, `ProjectedPath`, `Simulation`, `PreEvidence`, `ReachableReadback`, `SemanticTransitions`。barrel は追記のみ。既存の proof・仕様・実行系・`lean/Audit.lean`・`lean/README.md` を変更していない。
- Lean 4.35.0、`lake env lean --trust=0 -M 3200 -DwarningAsError=true` で 29 モジュール、独立監査 8 本（90 宣言）、既存回帰 13 本が exit 0。公理監査は `propext / Classical.choice / Quot.sound` のみ。基準の 285 と統合 `b9bb2a19d271…` の差分検査 `tools/verify-lean.sh --no-build` も exit 0。再現コマンドとログは [verification](../verification/cycle286/) に保存。全体 build・全体検証・CI は実行していない。
- 開始時に `integration/m1-final` の `b9bb2a19d271447d6f03f8b99e8ec97c9ee50363` から standing orders と inbox を取得。ACTIVE / I-53、凍結と小分け監査を確認。285 完了 pin は `e5057c2b5bbb16af2d7e835e2225286f5fa3dd18`。Yulang2 の `55574b6052ef1534fd0fc36d6d3617ebede59a0e` にある C3-ROLE-01/02、親と where 子の実機記録を照合した。今回の Lean 例を Yulang2 で新たに実行したとはしていない。
- 定刻 01:30、実開始 2026-11-20T01:30:20Z。途中の確認 pin は `9dffe08e`（開始）、`8c404bb7`、`ddf8682c`、`bf25cbfe`、`17b0a652`、`e73e90c55`、`49d82f43`（02:13:51Z の心拍、検証済み成果）。開始時に未完了周の復旧は不要、途中の環境更新後も同じツリーを保持。利用枠は不明、終盤の空きは約 52 GiB。前周から 54 パス。private `work/dots-main` のみへ expected-head・非強制で公開。

## 未達と次の候補

この例だけの実停止と、既存の有限後継ドライバとのモデル対応。任意の T1c/B4 の停止性、全選択分岐の完全性、主型性、239/240 の一般移植、任意の深い出力を生 Known にする完全性は未証明。旧回帰の再検査を後継への移植とは数えない。仕様判断を要する新しい質問ノートはない。

残る橋の候補は (1) 実 where 子を出す非葉と効果行を同一 fixture にし、型が同じで行だけが異なる二割当ての判定を実際に分離、(2) その子の生の静かな更新にも実到達性から測度を出す、(3) 239/240 を後継の実状態・実射影に移して一般 B4 への不足を確認。[次の設計](../design/2026-11-20-cycle286-next-bridges.md)。


報告を固定した時刻: 2026-11-20T02:21:15Z（経過 50.92 分）。
