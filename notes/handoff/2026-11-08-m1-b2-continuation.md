# B2: 有限 prefix の coverage 接続 (2026-11-08)

作業 0 の監査後の続き。元の B2 statement は変更していない。
optional field の case 照合と到達不能 arm の静的 effect 行の問いは未決のまま残す。

## 1. record の no-miss 証明書を、非停止を許す計算へ移す

`CommonPatternPrefixNoMiss.record_noMiss`:

- 任意のイベント型 `E`、エラー型 `R`、default コード型 `D`、任意の callback
  `Bindings Empty → D → Computation E R (Value Empty)` を量化する。
  callback の停止、成功、決定性、型、行について前提を置かない。
- 任意の有限 record 仕様 `specification`、source pattern `pattern`、その既存の
  独立証明書 `CommonRecordNoMiss.Total specification pattern`、任意の実 field 列と
  `Domain specification fields`、任意の累積環境について、既存の
  `CommonPatternComputations.run` を有限 prefix の `ops` で実行した計算は、
  いかなる有限 trace に対しても `some (.ok none)` という終了観測を持たない。
- 未終了 prefix (`none`) と、終了した照合失敗 (`some (.ok none)`) を区別する。
  default の非停止やエラーを、照合成功または値の返却と呼ばない。

補助の `everyValue_noMiss` は任意の値、float 型と比較、source default callback に対する
同じ結論を、既存の `EveryValue` 証明書から導く。
`supported_noMiss` は literal・pair・single-tag variant の既存 base-cell 被覆を移す。
`returns_bind` は先行計算が成功して返ったときだけ後続を実行する有限 prefix の定義から
終了成功の分解を証明する。record の field/rest は元の record 全体を保持し、
型／role の tail を任意の代入で選ぶ操作は導入していない。

検証: 新 module の `lake build --wfail Yulang.CommonPatternPrefixNoMiss` 成功。
既存全体の `lake build --wfail` は 1009 jobs で成功。
`--trust=0` で `returns_bind` は公理なし、`everyValue_noMiss`・`supported_noMiss`・
`record_noMiss` は `propext` のみ。統合側の `Audit.lean` への登録は親が行う。

## 2. joint-record の pure witness も prefix 計算へ移す

`CommonPurePatternPrefixNoMiss.pure_noMiss` は、任意の float 型と比較、イベント／エラー型、
source default callback、default を含まない任意の pattern、任意の実値と環境を量化する。
既存の有限 pure matcher がその値を受理すれば、同じ pattern を任意の default-code 型へ
埋め込んだ実 prefix matcher に、終了した miss は存在しない。
list の前後方向、nominal の型／constructor ID、float 比較も runtime の定理として保持する。
これらの Common 型付けが完成したという主張ではない。

`joint_record_witness` は、任意の元 source arm 列、有限 record 仕様とその任意の実 record、
任意の callback／環境を量化し、既存の pure record coverage checker が真なら、
元 arm 列の中に、guard が無く、その実 record について上の no-miss 性を持つ arm が
存在することを示す。元列中の default を持つ arm は取り除かない。
pure witness の抽出と source 構文への戻しは、既存の `erase_exact` を使う。

検証: 新 module の warnings-as-errors build 成功。

## 3. 元の first-match case 全体で、終了した全 arm miss を除く

`CommonCasePrefixCoverage.covered_noMiss`:

- 任意のイベント／エラー型、default・guard・body コード型とその任意の有限 prefix callback、
  元環境、有限 arm 列、開始 index を量化する。
- 既存の `CommonCaseRecordDefaultCoverage.check` が真であり、実 record が指定された
  `Domain` に入ることだけを前提に、その元 arm 列を `CommonCaseComputations.runArms` で
  順番どおり実行した計算には、終了した全 arm miss の観測が存在しない。
- guard は coverage の witness に数えない。先行 arm の default／guard のエラーや非停止、
  選択後の body のエラーや非停止を認める。後続 arm に進むのは実際に終了した miss／偽の
  guard の後だけである。

`eval_noMiss` は、返った subject がその record domain に入るという前提の下で、
subject の評価を含む同じ結論を示す。次の solved-family 接続では、この前提を
subject の型付けと生成した record 上界から内部で導く。

`safe_selected_result` は既存の全有限 prefix の行上界・成功時の型保存と、この no-miss 性を
合わせ、終了成功なら必ず `some` に入った型付きの選択結果を持つことを示す。
返却自体の存在／停止を結論に加えていない。

## 未完の範囲

これは既存の十分な coverage 証明書の運用上の意味を拡張する定理であり、
すべての default 依存 pattern matrix の被覆を決める算法ではない。
全 case と返却 scheme への接続、source 一般式からの実 prefix producer と adequacy、
source presence の合法性、list/nominal/float/merged-row の新 carrier、
独立した全 case 型付けと公開三契約は依然区別する。B2 の E1/E2 完了とは数えない。
