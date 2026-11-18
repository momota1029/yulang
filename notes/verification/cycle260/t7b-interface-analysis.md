# T7b: cycle260 roots sensitivity（読取解析・削除なし）

通常Reachは34の選択rootから164/220到達。住所分離・probe・run予算・固定fixture回帰を明示interfaceとして50rootへ選び直して再解析した。根を増やすだけで完成した一般言語定理になるわけではなく、ここでは独立したinterface定理の利用範囲を調べる。全リポジトリMain到達解析ではない。

CYCLE260-INTERFACE-REACH: 200/220 explicit declarations reached from 50 selected final roots

旧選択で未到達、新選択で到達した宣言（41本）：

- `Yulang.GeneralDefaultRebaseRun260.next_exact`
- `Yulang.GeneralDefaultRebaseRun260.one_step_bound`
- `Yulang.GeneralDefaultRebaseRun260.settle_final`
- `Yulang.GeneralDefaultRebaseRun260.settle_initial`
- `Yulang.GeneralDefaultRebaseSource260.stop`
- `Yulang.GeneralOutputRebasePublic260.requested_output_exact`
- `Yulang.GeneralOutputRebaseRun260.next_exact`
- `Yulang.GeneralOutputRebaseRun260.one_step_bound`
- `Yulang.GeneralOutputRebaseRun260.settle_final`
- `Yulang.GeneralOutputRebaseRun260.settle_initial`
- `Yulang.GeneralOutputRebaseSource260.stop`
- `Yulang.GeneralOwnedOutputDecoder260.translated`
- `Yulang.GeneralRebaseBodyActual260.distinct_default_target`
- `Yulang.GeneralRebaseBodyActual260.explicitProposal`
- `Yulang.GeneralRebaseBodyActual260.explicit_exact`
- `Yulang.GeneralRebaseBodyActual260.reflexive_default_target`
- `Yulang.GeneralRebaseEqualOutputs260.translated`
- `Yulang.GeneralRebaseNamedRequest260.code_injective`
- `Yulang.GeneralRebaseNamedRequest260.compile`
- `Yulang.GeneralRebaseNamedRequest260.lookup_unique`
- `Yulang.GeneralRebaseNamedRequest260.outputs_separate`
- `Yulang.GeneralRebaseNamedRequest260.probe_repaired`
- `Yulang.GeneralRebaseOutputDecoder260.translated`
- `Yulang.GeneralRebaseOutputFamilyRun260.batch_initial`
- `Yulang.GeneralRebaseOutputFamilyRun260.finish`
- `Yulang.GeneralRebaseOutputFamilyRun260.finish_exact`
- `Yulang.GeneralRebaseOutputFamilyRun260.finish_settle`
- `Yulang.GeneralRebaseOutputFamilyRun260.flattened`
- `Yulang.GeneralRebaseOutputFamilyRun260.settle_initial`
- `Yulang.GeneralRebaseOutputFamilyRun260.translated_iff`
- `Yulang.GeneralRebaseOutputFamilyRun260.untranslated`
- `Yulang.GeneralRebaseOwnedOutputKeys260.owners_separate`
- `Yulang.GeneralRebaseRequestBodyKeys260.key`
- `Yulang.GeneralRebaseRequestBodyKeys260.key_identity`
- `Yulang.GeneralRebaseRequestBodyKeys260.kinds_separate`
- `Yulang.GeneralRebaseRequestBodyKeys260.probe_repaired`
- `Yulang.GeneralRebaseRequestBodyKeys260.requests_separate`
- `Yulang.GeneralRebaseRequestBodyKeys260.space_identity`
- `Yulang.GeneralReflexiveDefaultRegression260.no_strict_model_refinement`
- `Yulang.GeneralReflexiveDefaultRun260.one_step_bound`
- `Yulang.GeneralReflexiveDefaultRun260.settle_initial`

新選択で未到達の宣言：

- `Yulang.GeneralRebaseOutputKeys260.below_offset`
- `Yulang.GeneralRebaseOutputKeys260.length`
- `Yulang.GeneralOutputRebaseSource260.closed`
- `Yulang.GeneralOutputRebaseSource260.terminating`
- `Yulang.GeneralOutputRebaseModels260.initial_exact`
- `Yulang.GeneralOutputRebaseModels260.bad_initial_not_final`
- `Yulang.GeneralOutputRebaseRun260.stop`
- `Yulang.GeneralOutputRebasePublic260.installed_public`
- `Yulang.GeneralRebaseOwnedOutputKeys260.capture_separate`
- `Yulang.GeneralRebaseOwnedOutputKeys260.length`
- `Yulang.GeneralRebaseOutputFamily260.length`
- `Yulang.GeneralDefaultRebaseBody260.schema_exact`
- `Yulang.GeneralDefaultRebaseSource260.closed`
- `Yulang.GeneralDefaultRebaseSource260.terminating`
- `Yulang.GeneralDefaultRebaseModels260.initial_exact`
- `Yulang.GeneralDefaultRebaseInstalled260.counter_removed`
- `Yulang.GeneralDefaultRebaseRun260.stop`
- `Yulang.GeneralReflexiveDefaultSource260.schema_exact`
- `Yulang.GeneralReflexiveDefaultRun260.stop`
- `Yulang.GeneralRebaseBodyActual260.target_not_interchangeable`

根集合は包含でなく目的別の選び直しなので、以前到達して新選択で未到達の宣言も5本ある。未到達は死んだコード・削除可能性を意味しない。特に公開count/translate/error補助定理は直接APIとして使える。ソースは一切削除・弱化していない。`InterfaceReach.lean`はYulangだけをimportし、独立strict Leanで検査した。

## importグラフも別に観測

新module間のimportグラフを読み取りで抽出した。これは証明termの依存とは別。

- `GeneralRebaseBodyDecoder260` は新module 19 本を推移的にimportする。
- `GeneralRebaseRequestBodyKeys260` は新module 25 本を推移的にimportする。
- `GeneralRebaseNamedRequest260` は新module 26 本を推移的にimportする。
- `GeneralRebaseEqualOutputs260` は新module 27 本を推移的にimportする。

順にcheckpointを接続したimport鎖にはfixtureを通じた依存がある。一般body/schema部分の直接必要importへ分離できるかは、将来の統合・compile費用の検討候補。ただし今回の凍結規則の下で既存moduleを変更したり、未到達helperを削除したりしていない。importが多いことだけで証明の仮定が増えたとは言えず、公理監査とは別の観測である。
