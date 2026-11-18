# cycle259 宣言の日本語案内

各節はmoduleの量化範囲・前提・主張。各宣言の全引数を含む正確な型は `alltypes-final.txt`、公理監査は `complete-final.txt`。定義・補助補題も列挙する。

## 1. GeneralRebaseReportDecoder259

固定I45 sourceのreport構文を有限factsへ復号する。capture名0と端点2/4だけを受理する局所decoderで、任意reportの言語的健全性は主張しない。

`atom`, `capture`, `captures`, `compile`, `source_atoms`, `no_private_atom`, `empty_rejected`, `actual`

## 2. GeneralDictionaryObservedRebase259

任意段階nの実packet reportを投影して得たproposalは固定factsと一致する。これを使う有限Stepは初回だけ進み、全状態Acc。ただしobserveAtは外部段階を受け取る。

`observeAt`, `observed_exact`, `ObservedStep`, `step_exact`, `initial_install`, `stops`, `decreasing`, `terminating`, `no_two`

## 3. GeneralDictionaryRebaseCertificate259

任意初期rawモデルから同一complete assignmentを構成し、現journal・実plan Holds・次journal・有限終点モデルを同時に満たす。初期0〜4全成分と全rowを保持し内部binder型は補完する。

`certificate`, `initial_install`, `old_new`, `certificate_source`, `certificate_exact`

## 4. GeneralDictionaryRebaseRun259

実reportのdecoderとtryWriteを接続したrunと有限Stepのiff。初回成功・以後noopとcertificateを証明するが、証明書はPropであって実行時モデル判定ではない。

`run`, `run_exact`, `run_step`, `initial_runs`, `final_noop`, `repeat_noop`, `run_certificate`

## 5. GeneralNominalTypeObservation259

任意二assignmentの全type成分が等しければOrigin観測が同値。rowを任意に変えられる局所補題であり全モデルの同値ではない。

`observes`, `observes_iff`

## 6. GeneralDictionaryRebaseCurrent259

I45 runをstage0だけで実行し、任意段階のrunと関数値等号で一致する。実行定義には増大する段階番号が不要。

`run`, `all_stages`, `first`, `stops`, `certificate`

## 7. GeneralVersionRowsRaw259

具体239 familyの既存typeモデルへ任意row関数を付けたassignmentを構成する。rawのordinary成立はここでは明示仮定。

`withRows`, `base_models`, `raw_models`

## 8. GeneralVersionRowsHead259

同じ239 assignmentでhead projection/merge/schemaを満たす。実ordinary条件と固定source構造を使い、任意headの一般定理ではない。

`observed_value`, `seen0`, `seen1`, `model_lower`, `model_upper`, `fit_observed`, `raw_projection`, `merge_model`, `head_model`

## 9. GeneralVersionRowsPacket259

239の実packet Holdsをordinary条件下で構成する。raw/head/観測の証明をまとめ、未証明producerを仮定しない。

`actual_value`, `head_holds`, `packet_holds`

## 10. GeneralVersionRowsStages259

実239履歴について帰納的にordinary条件を解消し、任意rowを持つ同一assignmentが全段階journalと実packetを満たす。

`atoms_valid`, `packet_holds`, `initial_raw`, `all_stages`

## 11. GeneralVersionBoundaryCompletion259

任意239初期モデルの初期0〜3全成分・全rowをliteralに保存して内部typeを補完する。初期typeのEquivalentから全段階モデルを得る。

`complete`, `Agree`, `agrees`, `second_scalar`, `initial_types`, `equivalent`, `all_stages`, `packet_holds`

## 12. GeneralVersionPublicProjection259

固定239 familyで、公開境界を保つ各段階または同一assignmentの全段階モデル存在 iff 初期rawモデル。任意sourceには一般化しない。

`initial_exact`, `source_agree`, `model_source`, `stage_models`, `simultaneous_models`

## 13. GeneralRebaseFiniteReport259

有限contextとownerとslot→atom写像を引数とするreport構文decoder。capture名0等の制約を持ち、任意Reportの正当性を認証するものではない。

`capture`, `captures`, `compile`, `empty_rejected`

## 14. GeneralVersionReportProjection259

任意239段階の実reportを初期4slotへ投影すると初回reportに一致し、実decoderのproposalが固定5factsと一致する。

`projection`, `original_projection`, `anchor_projection`, `bounds`, `transport`, `actual_report`

## 15. GeneralVersionRebaseStep259

239実reportから有限Stepを実行する。初回一度だけ進み、以後noop、全状態Acc。旧slot数や旧Stepの停止性とは別。

`facts`, `atom`, `initialState`, `finalState`, `proposal`, `proposal_exact`, `observeAt`, `run`, `observe_exact`, `run_exact`, `write_initial`, `run_first`, `first_step`, `stop`, `run_stop`, `terminating`, `first_unique`, `no_two`

## 16. GeneralVersionRebaseModels259

任意remaining subsetにsnapshot Models＋present factsの意味を定義する。初期/終点の正確な意味と、内部binder型補完を許す公開モデル存在同値。全subset到達は主張しない。

`factHolds`, `Models`, `initial_exact`, `final_exact`, `completed_binder`, `completed`, `public_models`

## 17. GeneralVersionRebaseCertificate259

239の同一complete assignmentで現journal・実plan・次journal・有限終点を接続。旧completed roundの射影stutterを示すが、旧microstep simulationではない。

`project`, `certificate`, `old_new`, `run_certificate`, `completed_round_simulation`, `old_novel_new_noop`

## 18. GeneralRebaseFactSemantics259

任意basis/state/proposalの低level writeについてpresent所属とModelsを厳密に記述。意味に加わるのはproposal∩basisだけで、basis外はwriteが無視する。

`present_iff`, `present_write`, `Models`, `write_exact`, `initial_exact`, `done_exact`

## 19. GeneralDictionaryRebaseFacts259

I45にも全subsetの明示的present-fact意味を与え、snapshotのPair制約から2≤4を導いてcompleteを構成。初期0〜4全成分と全row固定の公開存在同値。

`value`, `factHolds`, `Models`, `initial_exact`, `final_exact`, `prior_final_exact`, `completed`, `public_models`, `write_exact`

## 20. GeneralRebaseCheckedWrite259

proposalのbasis外を先に検査するchecked commit。成功なら全proposalがbasis内で、書込み後Models iff旧Models＋全proposal成立。errorは状態を返さず当該commitの部分書込みをしない。

`outside`, `commit`, `outside_member`, `closed_iff`, `accepted`, `supported`, `unsupported`, `accepted_models`

## 21. GeneralRebaseCheckedFixtures259

I45/239の実decoderをchecked commitへ接続する。初回成功・以後noop。手作り不正proposalのerrorは内部診断で、到達source拒否反例ではない。

`looseRun`, `versionRun`, `loose_exact`, `version_exact`, `loose_first`, `loose_stop`, `version_first`, `version_stop`, `unsupported_mixed`, `version_unsupported`

## 22. GeneralRebaseScheduler259

有限proposal列を順に検査しnoopを飛ばして最初のerror/進捗を返す。進捗後の後続proposalはそのpassでは未検査。成功は有限Step、全noopならquiescent。

`scan`, `next`, `scan_installed`, `next_step`, `scan_none`, `terminal`

## 23. GeneralRebaseSettle259

任意observerをremaining長で整礎反復するsettle。成功時に有限Runs、長さ上界、終端・quiescence。途中成功後errorもあり得るので全履歴rollbackは主張しない。

`settle`, `successful_terminal`, `successful_path`, `successful_budget`, `successful_quiescent`

## 24. GeneralRebaseClosedObserver259

全state・全proposalがbasis内という明示Closed仮定からerrorなしと有限完了を証明。一般source compilerがこの仮定を満たすことは未証明。

`Closed`, `scan_error`, `next_no_error`, `settle_no_error`, `completion`

## 25. GeneralRebaseDriverFixtures259

I45/239の実report observerはClosedで、settle初期=終点・終点=自身。noopを飛ばす実例も検証する。両固定family限定。

`loose_closed`, `version_closed`, `loose_next`, `version_next`, `loose_final`, `loose_initial`, `version_final`, `version_initial`, `skip_noop`

## 26. GeneralRebaseWriteAlgebra259

任意proposalのwrite可換・append・空・固定点・batch flattenをfilter代数で証明。basis外を無視する低level操作の結果である。

`commute`, `append`, `empty`, `fixed_iff`, `batch`, `batch_exact`

## 27. GeneralRebaseBatchTerminal259

固定proposal列observerかつ全proposal⊆basisの場合に、settle結果はbatchとliteral State等号。可変observerの合流性や言語正規形の一意性ではない。

`absorb`, `batch_absorb`, `no_write_iff`, `batch_fixed`, `terminal_batch`, `path_absorb`, `settle_batch`

## 28. GeneralRebaseBatchOrder259

外側リストでproposal自体のmembershipが一致する固定batchは同結果。閉包仮定下でsettleも等しく、順序交換・重複を許す。不正proposal errorの順序独立や動的observer合流性は主張しない。

`write_membership`, `batch_membership`, `settle_membership`, `swap`, `duplicate`

## 付録：独立した検証probe（数学module185宣言の集計外）

### DriverProbe
- `changesAfterInstall`: 239の有限stateを引数に取り、remainingが空でなければ既存5facts、空ならbasis外のinstalled999を提案する、意図的に不正なobserverの定義。
- `initial_progress`: このobserverのnextは具体initialStateから具体finalStateを返す。source一般の一歩ではない。
- `later_unsupported`: 同じobserverのnextは具体finalStateでinstalled999の内部errorを返す。
- `no_whole_run_rollback_claim`: 同observerのsettleは具体initialStateからそのerrorを返す。2つのnext結果を使う。中間書込みがあった事実と、純関数の最終返値がerrorだけであることを区別する。
- 3つの#evalはI45/239の終点remaining=0、不正observerのunsupported件数=1を表示する煙試験。証明ではない。

### OutputCoverageProbe
- `atom`: 252の具体snapshotのslot2だけをatom0へ写す部分写像。他slotはnone。
- `facts`: owner0のinstalled、lower/upper atom0、binder0/1という具体5facts。
- `actual_decoder_accepts`: 252の実packet reportをcompileすると上記factsを返す。report_exactを使う構文の計算定理。
- `checked_write_accepts`: 上記factsを同じbasisの初期有限stateへchecked commitするとdoneを返す。basis内閉包と差分だけを保証する。
- `accepted_report_not_output_certificate`: 同じ実reportの構文受理、実prepared Frame、具体replace bottom assignmentの初期journal Models、同assignmentでのpacket Holds不成立を同時に示す。既存258のframe_not_packetを利用する。252用のfinite fact意味表や公開モデル同値を新たに主張したものではない。
