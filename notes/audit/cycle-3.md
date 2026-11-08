# Audit cycle 3 — interrupted, reconstructed in cycle 4

## 状態

開始13:29:24 UTC、最後の公開心拍13:48:52 UTC、ローカル最終commit `80e0d0455` は13:51:49 UTC。最終報告は無く、14:25 UTCの復旧でこの報告を作成した。クラッシュの内部原因・正確な停止時刻・総稼働時間は不明。常設手順上は心拍停止と報告欠損により中断と扱う。

## 保存された成果

新spec基点 `816ed8f1d`、旧Y2 `d4c8bc8fc`。主に functions/application/effects、principal-monomorphization、control-flow、patterns、types/record spread と対応実装を監査した。復旧時にrawログを機械集計したところ、runtime-cycle-3*.md は539呼出記録（exit0 419、exit1 105、signal -9 2、外部timeout None 13）。記録された時間の合計1264.839秒は並行実行を含むため壁時計所要時間ではない。dump exit0でもdiagnosticsを含む場合があり、419を意味論的成功数と呼ばない。

cycle3専用の主張表6本には38行あり、26一致・6違う・6未確認。完全性側の受理候補10件は別表に保存。既存oracleへの追記と同じ観測の重複があるため、これらを合算した独立主張数とはしない。

## 主要結果

- ordinary actualの未使用引数の効果は直接呼出/pipeで起動するが、推論高階経由では起動しない具体例を観測。引数効果と本体効果を別operationにした対照はdirect11、高階22、eta wrapper11。VM/interpreter、mono形も保存。独立castを扱うF2への回帰候補であり、新specを旧実装に合わせて変更しない。
- 明示effectful戻り型の高階applicationはcheck成功でもmonoで失敗する境界を保存。
- record whole-spread自体は全recordを返すが、後段projectionで拒否される対照。source箇所とlist/guardの制限を保存。
- 旧label直接apply、新.again綴り、enum constructor名解決、パターンの受理例を分類。明示的な新spec変更を欠落扱いしない。
- F1独立castは新specで確定済み。Common arrow subtypeに特例がないことをそのまま欠落と呼ばない。strictApp局所定理とsurface高階cast挿入は別。

## 検証・限界

これは旧実機監査で、Lean全体buildは行っていない。原ログの中断・初回不正な試験sourceも保存し、修正後の観測と区別。標準preludeとno-prelude、backend、surface綴りの差を各表に記載。一般soundness/completeness/principalityの証明ではない。

cycle3には合計39ファイルの変更がローカルcommitに保存されており、そのうち22ファイルは途中公開済み。未公開分はcycle4で復元。既存ソース・spec・Leanの変更なし。公開復旧の正確な照合結果はcycle4報告/心拍を参照。使用量計上は不明。

## 14:52 UTC 以降の短い復旧追記

この報告自体を保全した。全ログの公開復旧完了を意味しない。未公開の大きなログを含む原本は local `1794212d8` に残る。最新の保全範囲は `2026-11-08-short-recovery-checkpoint.md` を参照。
