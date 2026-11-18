# cycle261 宣言の日本語案内

正確な引数・全量化型は alltypes-final.txt、公理依存は complete-final.txt。全source停止性・有限候補producer・SAT判定は未証明。

## 1. GeneralRebaseBodyTable261

任意固定Planの実lookup/bodySchemaを保持する要求表。missingは空schemaかつunknown。全key成立 iff全要求のBodyHolds。name/target別住所と位置非依存bodyの意味を区別する。

`schema`, `variables`, `address`, `keys`, `facts`, `localHolds`, `Holds`, `schema_meaning`, `translated`, `member`, `local_exact`, `all_exact`, `different_requests`, `reordered`

## 2. GeneralRebaseClassTable261

固定要求列についてbody義務と全同名pairのEqualOutputsを合成。全facts iff ClassEffects、終点は任意baseとの連言。初期kind2 equality住所は固定schema内indexであり、可変表の安定住所ではない。

`equalityAddress`, `equalityKeys`, `equalityHolds`, `facts`, `Holds`, `Effects`, `equality_exact`, `all_exact`, `kinds_separate`, `actualFacts`, `actual_exact`, `Models`, `initial_exact`, `done_exact`

## 3. GeneralRebaseClassCheck261

固定要求列のmissing bodyとunknown翻訳を別errorで検査する。check成功 iff Ready。意味的充足性やプログラム受理は判定しない。

`missing`, `untranslated`, `Ready`, `check`, `untranslated_empty`, `missing_empty`, `check_exact`, `ready_meaning`, `actual_ready`, `missing_error`, `untranslated_error`

## 4. GeneralRebaseClassRun261

固定要求表のrunはReady時にchecked writeへ一致。初回進行にはfacts非空が必要。固定表のsettle/AccはReadyなしでも成立し、モデル存在を意味しない。

`observe`, `closed`, `write_all`, `run`, `run_exact`, `run_step`, `stops`, `first`, `settle_initial`, `terminating`, `done_semantics`

## 5. GeneralRebaseMergeRequests261

AllocMerge実alias classの全requests membershipが2要求列と一致、両targetは異なる。実lookup/bodySchema/Ready/ClassEffectsまで接続するが、旧V7と現行versionedのtrace到達は別。

`outputs`, `first_present`, `last_present`, `requests_exact`, `requests_distinct`, `packet`, `candidate`, `body`, `lookup_exact`, `schema_exact`, `ready`, `effects_exact`

## 6. GeneralRebaseMergeMeaning261

実二要求のClassEffectsは両target Int。既存parent履歴はa=Int,b=Variant Intを要求する。履歴とEqualOutputsまたは両bodyは不整合。raw-only uniformは新Effectsを満たす。

`body_meaning`, `effects_exact`, `history_outputs`, `history_equal_impossible`, `history_effects_impossible`, `uniform_effects`

## 7. GeneralRebaseMergeRun261

具体6factの初回成功・以後停止。履歴保持終点は不充足、Good下raw-only終点は充足。旧V7実到達終点・rejectedへの接続は現行versioned到達証明ではない。

`facts`, `initialState`, `finalState`, `observe`, `run`, `History`, `Models`, `facts_count`, `nonempty`, `first`, `stop`, `first_step`, `settle_initial`, `initial_inhabited`, `final_exact`, `final_uninhabited`, `raw_only_inhabited`, `old_final_regression`

## 8. GeneralRebaseMergeFrame261

GoodとSupportedの具体atoms-stageから現行versioned Frameを構成。capture/report空、ordinary、fresh等を実fixtureで解消する。任意sourceのFrame生成ではない。

`report_empty`, `bindings_empty`, `ordinary`, `head_models`, `fresh`, `prepared`, `frame`

## 9. GeneralRebaseMergePacket261

具体stageのraw Modelsと実Effectsから現行packet Holds、Good＋Supportedからleaf Evidence。raw-only uniformのEvidenceは履歴モデルを意味しない。実children/head空・emitted Intを使用する。

`head_schema`, `emissions_empty`, `emitted_schema`, `children_empty`, `actual_ready`, `packet_holds`, `evidence`, `raw_only_evidence`

## 10. GeneralRebaseMergeHistory261

当該stage familyの既存履歴を初期snapshot Models＋固定2出力制約へ全assignmentで同値圧縮。任意の増大journal有限化ではない。新全subsetのModels同値と終点不充足を保持。

`Base`, `history_exact`, `Models`, `models_exact`, `initial_inhabited`, `final_uninhabited`, `uniform_not_base`

## 11. GeneralRebasePairKeys261

ownerと二つの(name,target)をkind3に注入符号化し位置非依存のEqualOutputs住所を作る。全key iff同名pair型同値、subset包含・並べ替えに対するmembership不変。旧kind2と混ぜない。

`code`, `key`, `code_injective`, `key_injective`, `facts`, `Holds`, `at_key`, `member`, `all_exact`, `monotone`, `reordered`, `body_separate`

## 12. GeneralRebaseStableBody261

固定Planについて全requestを量化したkey意味。住所一意性により観測subsetのbody義務と厳密一致。subset変更に意味は依存しないが、Plan変更は別の橋が必要。

`Holds`, `collision`, `all_exact`, `pair_outside`, `at_pair`, `pair_at_body`, `monotone`

## 13. GeneralRebaseStableClass261

安定body＋pair表。全facts iff観測要求列のEffects。有限candidateに要求が含まれる前提で、書込み後Models iff書込み前Models＋実ClassEffects。

`facts`, `Holds`, `all_exact`, `monotone`, `reordered`, `Models`, `write_exact`, `actual_write`

## 14. GeneralRebaseCandidateDriver261

任意state依存request選択について全要求が固定候補列に入るCoveredを明示。Closed・settle完了・成功Step上限とモデル変化を証明。Ready・充足性・source候補producerを仮定から自動生成しない。

`observe`, `Covered`, `closed`, `completion`, `step_exact`, `terminating`

## 15. GeneralRebaseCandidateTrace261

成功Stepで実際に選んだrequest列を記録するTraceとRunsを長さ保存で対応。同じ記録が全assignmentに対し終点Models iff開始Models＋全履歴Effectsを満たす。監査証人でruntime履歴storageではない。

`from_runs`, `to_runs`, `models_exact`, `successful_history`

`Trace` 帰納型とその生成宣言も Full 監査対象。

## 16. GeneralRebaseStableMerge261

新kind3でも6factの終点意味は旧表の履歴保持終点と同一assignmentで同値。任意atoms-stageの実requests coverageを実証。固定Plan解釈であり動的Planとの橋は次節。

`facts`, `initialState`, `finalState`, `Models`, `facts_count`, `initial_exact`, `final_exact`, `final_uninhabited`, `requests_covered`, `select`, `covered`, `completion`

## 17. GeneralRebaseMergeObservation261

この具体familyのbodyは全atoms-stageでIntなので、固定Plan表のEffectsと実観測stageの実Plan ClassEffectsが一致。Good/Supported/raw Modelsを明示して実packetとleaf Evidenceへ接続。一般Plan変更の不変性ではない。

`effects_reordered`, `changing_plan`, `actual_write`, `packet_evidence`

## 18. GeneralRebaseStableMergeDriver261

任意state→atoms観測でも実requestsのmembershipが同じため、実proposalのwriteは固定6facts書込みへ一致。noncomputable実観測runと実行可能固定表runが関数等号。初回一歩・以後停止・Runs≤1は具体family限定。

`proposal`, `membership`, `write_full`, `write_actual`, `try_actual`, `run`, `executable`, `run_exact`, `function_exact`, `first`, `stops`, `observe`, `step_final`, `no_step_final`, `budget`

## 19. GeneralRebaseCandidateValidation261

固定有限candidate全体のmissing/unknown検査とcovered schedulerを接続。成功なら全traceのReadyと正確なModels連言。未使用candidateのunknownも内部errorになり得るため言語拒否ではない。

`finish`, `ready_selected`, `success_exact`, `layout_error`, `completion`, `trace_ready`, `successful_trace`

## 20. GeneralRebaseStableMergeFinish261

具体fixtureでは任意観測・任意finiteStateから唯一終端doneへsettle/finishが成功する。ただし履歴保持doneは不充足。翻訳/制約生成成功と充足性/プログラム受理を区別する閉じた回帰。

`terminal_final`, `settle_exact`, `finish`, `finish_exact`, `success_not_satisfiability`

## 21. GeneralRebaseSourceSnapshot261

任意固定source snapshotの全site outputsを実行可能な有限candidate列にする。任意rootの実alias requestsを仮定なしで包含し、その固定snapshot上の動的root選択でClosed/完了/実ClassEffects書込みを示す。sourceやPlanは固定、一般trace共通pool・Frame生成・言語停止性ではない。

`candidates`, `covered`, `select`, `all_covered`, `completion`, `step_actual`, `initial_models`

## 22. GeneralRebaseSourcePool261

実center mergeとrefreshはsnapshot candidate列をliteralに保存する。versioned installは既存Absorbed前提の下でcandidate membershipを保存し、全rootの新requestsが旧poolに入る。新childを無条件で吸収すると仮定せず、list長・意味・全trace閉包の保存とは区別する。

`same_sites`, `merge_pool`, `refresh_pool`, `absorbed_install`, `installed_requests_covered`

## CandidateBoundaryProbe

実fixture Planに実requestsに属さない未定義name1を内部candidateとして加える。空observerならschedulerは即完了するがlayout検査はmissing errorを返す。未使用candidate全体検査の保守性を示し、source到達反例や言語拒否とは主張しない。

`unused_missing`, `empty_selection_covered`, `empty_settles`, `unused_layout_error`
