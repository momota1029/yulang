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

## 未完の範囲

これは既存の十分な coverage 証明書の運用上の意味を拡張する定理であり、
すべての default 依存 pattern matrix の被覆を決める算法ではない。
全 case と返却 scheme への接続、source 一般式からの実 prefix producer と adequacy、
source presence の合法性、list/nominal/float/merged-row の新 carrier、
独立した全 case 型付けと公開三契約は依然区別する。B2 の E1/E2 完了とは数えない。
