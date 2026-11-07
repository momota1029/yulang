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

## 4. 実 Core 生成・record 上界・coverage・全 parameter を一つにつなぐ

`CommonCaseCoreRecordPrefixSolved.generatePremises_exact` は、任意の Core subject、有限 arm 列、
record 仕様、任意の型／行 assignment と captured 環境を量化する。通常の二つの環境解釈関係を
前提に、実際の有限生成が満たされることと、次の独立した前提の conjunction を同値にする。

1. 元の subject と全 arm の共有環境・default/guard/body の row 上界の型付け。
2. subject 型が指定された record 型以下であること。
3. 全実 record に対する pure witness、または guard 無しの独立した default no-miss 証明書。

`PureCoverage` は、pure pattern が source pattern の literal map image であることと、
実 pure matcher が各 record を受理することで定義する。finite checker／solver の別名ではない。

`premises_instances_exact` は、空 captured 環境と任意の `Fin 3` assignment について、
この conjunction の全 model と、実 `solvePremises` が返す scheme の全 parameter による
instance を同値にする。各 value slot は Common 要求同値まで、各 row は文字通り同じ値へ戻す。
`no_premises_exact` は空の返却 list と model 不存在を同値にする。

`all_parameter_case_prefixes` は、任意の実返却 scheme と**任意の**その parameter、
任意の source/event/error 行解釈と prefix evaluator を量化する。
既存の独立した全域契約 `CommonPatternCorePrefixBridge.EvaluationSound` を前提に、元順序の
実 `CommonCaseComputations.eval` の全有限観測で行が返却 cap 以下となり、終了成功なら
必ず `some` に入った、返却 target 型を持つ値になることを示す。
domain、coverage、selected arm、default の成功、ResidualHolds は返却後の前提に置かない。
subject の domain は、その実成功 prefix の型保存と、同じ有限生成の record 上界から導く。

この結果は、既存の `all_parameter_case_prefixes` が許していた「終了成功だが全 arm miss」
を、同じ solver family の内部で排除したもの。一般式の実 prefix producer を構成した、
またはその adequacy を証明した、という意味ではない。

## 5. default-only の実 Core family が空でないこと

`CommonCaseCoreRecordPrefixExamples.real_scheme_instance` は、subject が Core の空 record、
唯一の arm が `defaultField 0 (literal 7) (bind 0) recordEnd`、body が Core の `var 0`
である実入力について、上の `solvePremises` が scheme を返し、具体的な assignment を
表す parameter が存在することを示す。input は exact-empty、result は int、cap は空行。
default result と absent-field payload の union が同じ生成済み monomorphic binder に入り、
その binder を body が参照する。pure arm 列は空なので、pure coverage による例ではない。

この実例は independent constructor judgment から model を構成し、有限 solver の
完全性で scheme を得る。終了／default 成功を仮定して family を作っていない。
source presence annotation を解決したという主張も加えていない。

検証: `lake build --wfail Yulang.CommonCaseCoreRecordPrefixExamples` 成功。
`--trust=0` による `real_generated_model` / `real_scheme_instance` の監査で、許可された
`propext` / `Classical.choice` / `Quot.sound` 以外の公理は使わない。

## 6. 元の indexed Core data を実行する有限 evaluator

`CommonCoreDataEvaluation` は、元の `Required.Term` の literal/data/var/pair/fst/snd/
emptyRecord/record/recordDefault/field/variant/leaf を直接評価する。
Core index をそのまま環境の添字に使い、shadow された名前で再解決しない。
全 source visit を trace に記録し、record の二項は既存 data evaluator と同じ書かれた順序で
評価する。pattern default の遅延は、引き続き元 canonical matcher 側が決める。
関数・再帰・effect・let・nested case などは、明示的な `unsupported` error になる。
unsupported を silent computation に変えて全域安全性を得る方法は取らない。

`typing_evaluates` は、上の独立した `Supported` fragment の任意の元 Core term、
任意の indexed captured environment と全 result computation について、通常の独立した
Common constructor typing と環境内各 binding instance の値型から、実 evaluator の成功と
返却値型を導く。成功・停止・interpreter soundness を前提にしない。
`supported_exact` は有限 Bool gate と独立した fragment 構文を同値にする。
この局所での停止は有限で効果のない選択済み fragment の性質であり、一般 default には課さない。

検証: 新 module の warnings-as-errors build と `trust=0` 監査が成功。
この packet の時点では source gate と prefix family の接続は次の作業である。

## 7. 実 source trace の全有限 prefix

`CommonCoreDataPrefixes.ofLogged` は、未終了観測を実 trace の prefix とし、終了観測を
実 trace 全体と元の厳密な result とする。`pending_exact` / `completed_exact` は、
この対応を両方向に示す。source visit を削ったり、unsupported error を未終了に変えたりしない。

`typing_prefixes` は §6 の独立した型付けから、固定された実 evaluator の全 prefix に対する
安全性を導く。source fragment の visit は純粋であり、その行解釈は空行。error 行は任意。
成功時には result 型を保持し、型付きの supported source は §6 により error を返さない。
`binding_prefixes` は実 pattern の pure monomorphic prefix 環境を indexed logical environment に
接続する。どちらも `EvaluationSound` という外部 premise は持たない。

検証: 新 module の warnings-as-errors build と `trust=0` 監査が成功。

## 8. subject/default/guard/body 全出現の実 source gate

`CommonCaseCoreDataGate.check_exact` は、実 subject と元 arm 列のすべての default 出現、
guard、body に対する有限 Bool 検査を、独立した `Supported` fragment judgment の全成立と
同値にする。両側の or pattern と、後続の到達不能かもしれない arm も検査する。
これは静的 effect policy の選択ではなく、この限定された evaluator を使うための source 範囲である。

`strengthen_defaults` / `arm_typing` は、元の aligned pattern／Core arm の独立型付けから、
各実 source code の fragment judgment を伴う型付けを導く。
元の binder order、同じ slot、Q4 累積環境、right-or の name alignment は変えない。

検証: 新 module の warnings-as-errors build と `trust=0` 監査が成功。
主要三定理は `propext` / `Quot.sound` のみ。

## 9. 限定 Core data family から EvaluationSound premise を除く

`CommonCaseCoreDataPrefixSolved.principal` は §8 の実 source gate を §4 の同じ実有限 formula の
前に置き、unsupported な subject/default/guard/body を solver の前で除く。
`principal_exact` / `premises_instances_exact` / `no_premises_exact` は、独立した bounded Core
record premise と `Supported` judgment の conjunction に対する、同じ unrestricted family の
厳密性・完全性・空性を証明する。returned parameter に新たな述語は課さない。

`all_parameter_case_prefixes` は任意の実返却 scheme と任意のその parameter、任意の error 行を
量化する。source evaluator は §6–7 の実 evaluator に固定し、guard は同じ値を Bool として読み、
無効値では実 expectedBool error を返す。型付けからその無効枝を内部で排除する。
元 arm 列を同じ canonical prefix matcher で順に実行した全有限観測について、返却 cap 以下の行と、
終了成功時に `some` に入った返却 target 型の値を得る。

この限定された source fragment では **EvaluationSound は前提から除かれた**。
source support・default 成功・selected arm・coverage・domain・ResidualHolds を外部に要求しない。
一般式・効果・関数・再帰の evaluator／adequacy を解決したとは主張しない。

検証: 新 module の warnings-as-errors build と主要四定理の `trust=0` 監査が成功。
許可された `propext` / `Classical.choice` / `Quot.sound` 以外の公理は使わない。

## 未完の範囲

これは既存の十分な coverage 証明書の運用上の意味を拡張する定理であり、
すべての default 依存 pattern matrix の被覆を決める算法ではない。
record に対する coverage/environment/row-upper-bound factor と返却 scheme の接続は閉じた。
元 B2 の残りは次のとおり。

- source 一般式から実 prefix producer を構成し、`EvaluationSound` と実実行の adequacy を証明する。
  §6–9 の有限な純粋 Core data fragment については実 producer と局所安全性を構成し、
  対応する実 family の theorem から外部 `EvaluationSound` を除いた。
  現在の data-only value carrier では関数などをまだ表さないため、B3/B5 の橋が必要。
- required field の default 拒否を含む、source presence metadata の合法性を有限生成へ接続する。
- list/nominal/float/merged-row を含む declaration-aware carrier と全 pattern judgment を接続する。
- すべての default 依存 matrix を扱う coverage と、guard／failure／静的行の全 case 規則を確定・証明する。
- その独立した full case 型付けと実生成の iff、同一の公開三契約を閉じる。

B2 の E1/E2 完了とは数えない。optional field と到達不能 arm の静的行の既存の問いは変更していない。
