# dots-main cycle 470: I-93 最小商の単項回帰

道具: モデル不明、Lean 4.35.0; 委譲: モデル不明、1回、task /root/yulang302_resume（追加委譲なし、Codex thread なし）

- 実開始 2026-11-27T17:30:13.943Z、通常終了 2026-11-27T18:20:16.087Z UTC。+20 に C469 反例採用（I-92）、+30 で監督統合 5c1f515d4e6fdf99730fef55419e346929d60faa の **I-93**（inbox 0e8f12dc7e6438ee8aa512feaa1e30c39773bfa9）を確認。正本 yulang3 `fcc2aba451c3cfc7e443092d296e84aa044f1482` の §6.3 K2 L505 が、等しい再帰型の最小商で循環を判定する、と明記。
- [設計・回帰ノート](../design/dots-cycle-470-i93-quotient-regression.md)（blob 79adf4850291a6c77450d690648495e9f1ba65da）。C469 は raw に名前・行を足さず、実選択 inline source occurrence と既存 raw point 5 の有限構造対応を区別する。独立の単項数学転記で inline の商 K2 は true。label77 の別 stem は循環に到達するが商の循環上にはない。子閉包と有限深さでの観測差により非循環を独立に証明し、正 witness の欠落を安全とはしない。
- 元位置: C463 の `locateRoute` は実 raw 子名付き path が前提。正規化後と元物理位置、隠れ同名 field、未訪問 sibling、同形の別 occurrence を代用しない。実 constructor の対応と同じ商の点での循環を要し、単に到達するだけでは足りない。全 Model の値の等しさは checker 入力にしない。
- **検証:** 独立 `Std` 回帰は Lean 4.35.0 `--trust=0 -DwarningAsError=true --stdin`、5 標準集合内の公理照合、2 実行列 PASS。旧キャッシュの不足を回復し、監督は exact C464 の focused replay にも成功。回復後の**未公開の狭い対照**では実 C464 prechecked head と元 raw 行0/1 から (4,30,5) を読み、指定した inline payload と名5は全同じ `FitsFull` で同値、元 raw の点5は実循環。誤 point と bare binder は読まない。3 追加公理照合は worker と監督が strict PASS。これは累積入口での exact diagnostic や一般商の健全性・完全性でない。
- **G04 未完、24 行中 20 行残り。** 実 compiler event の元 occurrence との一般接続、既存入口の exact report、一般の商での安全証人は未実装。既存 `CommonRoleGraphBisimulation` の有限対応を再利用し、nominal 根を除外する旧 `regularAt` の側は現仕様と区別する。過去 Yulang2 を再認定しない。State/spec/checker/既存 raw/Lean tree `caebfa827aa0c0ab1e84fc87818b2a7353ecfb6b` 不変。project Lean を公開せず、全体 build・Yulang2 実機なし。expected-parent 非 force の work/dots-main のみ、設計・心拍・本報告の3 paths。使用量枠不明。
