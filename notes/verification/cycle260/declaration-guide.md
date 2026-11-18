# cycle260 宣言の日本語案内

各節は量化範囲・前提・射程。全宣言の正確な引数と型は `alltypes-final.txt`、公理依存は `complete-final.txt`。

## 1. GeneralRebaseOutputKeys260

任意Schemaとoffsetについて、実equation列のindexをbinder factへ符号化する。全keyのHolds iff Schema.Holds、index注入性とoffset未満のcaptureとの分離。新しいsource名を割り当てる定理ではない。

`key`, `keys`, `Holds`, `key_injective`, `member`, `at_index`, `all_exact`, `below_offset`, `length`

## 2. GeneralRebaseOutputDecoder260

任意Planの実emittedSchemaが翻訳済みで実capture reportの復号が成功した場合だけ、capture factsと出力方程式keysを返す。unknown出力と未対応reportは別error。任意sourceの意味的健全性をこれだけで認証しない。

`compile`, `translated`, `successful`

## 3. GeneralOutputRebaseSource260

実252 sourceのreportと一つのemitted equationから6factsを構成し、実proposal一致・Closed・初回一歩・停止・Accを示す。有限stateから任意sourceのinspectionを行う一般compilerではない。

`facts`, `atom`, `schema`, `schema_exact`, `capture_exact`, `output_keys`, `proposal`, `proposal_exact`, `initialState`, `finalState`, `observe`, `observe_exact`, `closed`, `write_initial`, `first`, `stop`, `terminating`

## 4. GeneralOutputRebaseModels260

252固定layoutで任意finiteStateの意味をraw snapshot Models＋present factsで定義する。終点Models iff実packet Holdsは同一assignment。全subsetに意味を定義するが全subset到達可能性を主張しない。

`factHolds`, `Models`, `output_meaning`, `initial_exact`, `final_exact`, `final_packet`, `completed`, `bad_initial_not_final`

## 5. GeneralOutputRebaseInstalled260

252の実Holdsから旧InstallationModelsとleaf Evidenceを構成する。新終点Models iff旧installed journal Modelsは全assignmentの同値。実children空・ready等の具体条件を使い、任意Planの一般橋ではない。

`installation`, `installed_packet`, `same_assignment`, `evidence`

## 6. GeneralOutputRebaseRun260

252の実decoderとchecked commitを接続する。decode/outside errorを区別し、実runのStep iff・初回成功・以後none・settle完了・成功Step数≤1。observer内部計算や旧Step数の時間上界ではない。

`run`, `run_exact`, `run_step`, `first`, `stop`, `next_exact`, `settle_initial`, `settle_final`, `one_step_bound`

## 7. GeneralOutputRebasePublic260

252初期任意rawモデルのslot3型だけを補完し、他の全Comp成分・全rowsを保持してcurrent/Holds/installed/newfinal/Evidenceを同じassignmentで満たす。任意subsetの公開存在モデル同値。全初期モデルをそのまま終点モデルにする主張ではない。

`public_models`, `installed_public`, `certificate`, `run_certificate`, `requested_output_exact`

## 8. GeneralRebaseOwnedOutputKeys260

任意ownerとequation indexを既存pair注入符号でkey化し、owner/index双方の非衝突とcapture0/1からの分離を証明。固定source layoutにおける有限table住所であってsource名ではない。

`key`, `keys`, `Holds`, `key_identity`, `key_injective`, `member`, `at_index`, `all_exact`, `capture_separate`, `owners_separate`, `length`

## 9. GeneralRebaseOutputFamily260

任意有限owners列と固定owner別schema/variablesについて、列挙したkeys全体のHolds iff全ownerのSchema.Holds。owners重複可、長さは重複込み。閉包は与えた有限表に対して導出、sourceから表を生成する証明ではない。

`Layout`, `basis`, `Holds`, `member`, `owner_exact`, `all_exact`, `proposal_closed`, `length`

## 10. GeneralRebaseOutputFamilyRun260

固定output表の全proposalはbasis内で、settleは全表を書いたstateに終わる。finishはunknown flagを別検査する。モデル存在判定・言語受理判定ではない。

`proposals`, `observe`, `closed`, `flattened`, `batch_initial`, `settle_initial`, `untranslated`, `finish`, `translated_iff`, `finish_exact`, `finish_settle`

## 11. GeneralOwnedOutputDecoder260

単一Planのemitted出力keysをownerで分けたdecoder。capture binder0/1は依然共有され、全consumerに対する複数owner compilerとは主張しない。

`compile`, `translated`, `successful`

## 12. GeneralOwnedOutputActual260

252のowner0,index0が従来binder2と一致し、新owned decoder/runが既存runに等しいことから同じcomplete certificateを再利用。一般ownerへ252の意味証明を拡張しない。

`keys_exact`, `proposal`, `proposal_exact`, `run`, `run_equal`, `run_certificate`

## 13. GeneralDefaultRebaseBody260

206の実lookup/default body/schemaとClassEffectsの対応を示す。BodyHoldsとClassEffectsはoutput0型≃inputcenter1型で、current journal Models iff raw snapshot Models。実requestsの所属・一意性も証明する。

`body`, `schema`, `lookup_exact`, `schema_exact`, `body_meaning`, `request_exact`, `request_present`, `classes_exact`, `current_source`

## 14. GeneralDefaultRebaseSource260

206実reportはblocked/conflict/arity/capture空と確認し、実defaultを独立obligationとして2facts化する。専用入口であり一般empty capture reportを無条件受理する変更ではない。初回/停止/Acc/Closedは固定source限定。

`report`, `report_clear`, `facts`, `output_keys`, `proposal`, `proposal_exact`, `initialState`, `finalState`, `observe`, `observe_exact`, `closed`, `write_initial`, `first`, `stop`, `terminating`

## 15. GeneralDefaultRebaseModels260

206のcurrent journal Models＋present factsを意味とし、終点 iff current Models∧実ClassEffectsを同一assignmentで証明する。packet Holds単独では不足する義務を維持する。

`factHolds`, `Models`, `output_meaning`, `initial_exact`, `final_exact`

## 16. GeneralDefaultRebaseInstalled260

206の新終点Models iff実旧installed Modelsを同一assignmentで証明し、leaf Evidenceと旧bottom counter除去を接続。任意sourceや未到達状態の一般インストール健全性ではない。

`installation`, `installed_exact`, `same_assignment`, `evidence`, `counter_removed`

## 17. GeneralDefaultRebaseRun260

206の専用decoderとchecked commitによるrun、初回一歩・以後noop・settle完了・成功Step数≤1。error分類を保持する。

`run`, `run_exact`, `run_step`, `first`, `stop`, `next_exact`, `settle_initial`, `settle_final`, `one_step_bound`

## 18. GeneralDefaultRebaseCompletion260

206のraw snapshotが読まないslot0型だけを入力center1型へ補完する。rawモデル保存とdefault成立を示し、slot0以外の全Compと全rowをliteralに保持する。

`identity`, `view`, `models_exact`, `unused_output`, `source_iff`, `complete`, `rows`, `outside`, `source_exact`, `classes`, `final`

## 19. GeneralDefaultRebasePublic260

206初期raw Models iff内部slot0型だけを解放した公開境界の有限stateモデル存在。任意subsetに成立するが到達可能性は別。同一completeでcurrent/Holds/ClassEffects/installed/newfinal/Evidenceを構成。

`Agree`, `completion_agrees`, `source_agree`, `completed`, `public_models`, `certificate`, `run_certificate`

## 20. GeneralRebaseBodyDecoder260

任意Planと指定outputの実lookup/bodySchemaを使い、targetとexplicit/defaultの変数scopeを保って単一bodyを翻訳する。成功はlookup＋unknown=falseの構文条件。実requests所属・全要求coverage・EqualOutputsの証明ではない。

`compile`, `successful`, `equation_meaning`

## 21. GeneralReflexiveDefaultSource260

202実sourceの要求target1とinputcenter1を保つdefault翻訳。実reportから同じ2fact住所が得られるが206のschema意味とは別。固定sourceの初回/停止/Acc/Closed。

`body`, `schema`, `facts`, `initialState`, `finalState`, `report`, `schema_exact`, `output_keys`, `body_meaning`, `report_clear`, `proposal`, `proposal_exact`, `observe`, `observe_equal`

## 22. GeneralReflexiveDefaultModels260

202 defaultは全assignmentで反射的に成立し、任意finite subset stateのModels iff current journal Models。同一assignmentのまま全subsetの意味が等しく、元のEvidenceも保持する。

`factHolds`, `Models`, `output_meaning`, `all_facts`, `models_exact`, `same_assignment`, `evidence`

## 23. GeneralReflexiveDefaultRun260

202の専用runとchecked commitの接続、実初回成功・以後none・settle完了・成功Step数≤1。別error型の206runとの誤同一視はせず実成功戻りで比較する。

`run`, `run_exact`, `run_step`, `first_step`, `first`, `stop`, `settle_initial`, `one_step_bound`

## 24. GeneralReflexiveDefaultRegression260

202旧kernelは既にStableでStep不可。新初回fact書込みは同一assignmentでモデル集合不変のsemantic stutter。真のモデル集合細分化や旧install一歩のsimulationとは区別し、runと旧Evidenceを接続する。

`old_no_step`, `fact_step_semantic_stutter`, `no_strict_model_refinement`, `run_certificate`

## 25. GeneralRebaseBodyActual260

252の実capture reportと実body requestを合成/重複除去して既存factsに一致させる。206 output0と202 output1の実target別入口も確認。両source schema不等を証明し、同じ有限key住所から同じpayload意味を推論しない。

`explicitProposal`, `explicit_exact`, `distinct_default_target`, `reflexive_default_target`, `target_not_interchangeable`

## 26. GeneralRebaseRequestBodyKeys260

任意owner/kind/request/equationの4成分を注入的に符号化し、要求別・種類別のkey分離と固定request bodyの意味を証明する。206内部probeの異なるrequest番号は異なるproposalになる。installed markerもnamespace化された表markerで、旧owner commitmentへの接続は未実装。実requests coverage・index割当・EqualOutputs・一般Step接続の証明ではない。

`space`, `key`, `space_identity`, `key_identity`, `compile`, `successful`, `equation_meaning`, `requests_separate`, `kinds_separate`, `probe_repaired`

## 27. GeneralRebaseNamedRequest260

requestの(name,target)を注入符号化した安定住所を供給する。可変alias列の位置を使わず、異なるname/targetを分離。同じPlan固定でlookup body一意、単一body意味は保存する。sourceから有限request候補を得る証明・全class coverage・実行runner接続は別。

`code`, `code_injective`, `compile`, `outputs_separate`, `lookup_unique`, `equation_meaning`, `probe_repaired`

## 独立RequestAddressProbe

206同一planに実要求output0と、実requestsに属さない内部引数output1を渡すと、単一body decoderは同じkey列を返す。一方、既存counterではoutput0のBodyHoldsが偽、output1が反射的に真。同一owner複数requestを共有layoutへ無造作に合成できないという内部decoder境界であり、source到達反例・言語拒否・非停止・I50深さ上界の反例ではない。

`alternate_not_requested`, `same_address`, `alternate_holds`, `actual_fails`, `address_does_not_determine_payload`
