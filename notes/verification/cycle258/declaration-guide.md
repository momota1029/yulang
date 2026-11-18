# cycle258 宣言の日本語案内

各節はmodule共通の量化範囲・前提・主張。各個別宣言の正確な型（暗黙引数を含む）は `alltypes-final.txt`、公理は `complete-final.txt` を参照。定義・補助補題も省かず列挙する。

## 1. GeneralDictionaryFamilyRecognition258

任意の数値名について、有限探索の判定と実I45 lower/upper無限生成族への所属を同値にする。indexより生成名が大きいことと両族の非交差を使う。

`index_lower`, `index_upper`, `isLower`, `isUpper`, `lower_iff`, `upper_iff`, `disjoint`, `small`

## 2. GeneralDictionaryUniformFill258

任意assignmentのlower族の型をslot2、upper族の型をslot4へ置き換える。全段階で同じ関数を使い、初期0〜4、実binderの全成分、全rowを保存する。

`fill`, `rows`, `initial`, `lower_value`, `upper_value`, `actual_tags`, `actual_fixed`, `outside`, `idempotent`, `agrees`

## 3. GeneralDictionaryUniformBlock258

任意assignmentと任意段階nについて、このfill後にその段階までの実history定義blockがすべて成立する。任意sourceではなく固定I45族である。

`lower_equation`, `upper_equation`, `all_blocks`

## 4. GeneralDictionaryUniformView258

任意段階n・assignmentについて、fill後のraw/journal意味を有限Viewと同値にする。正段階のjournalに対応するbinder条件を省かない。

`support_small`, `view_exact`, `binder_exact`, `journal_view_exact`, `raw_exact`, `journal_exact`

## 5. GeneralDictionaryUniformJournal258

任意assignmentについて、正段階の有限journal Viewを満たすことと同じfillが全段階journalを満たすことが同値。存在assignmentと全段階の量化は具体的fillで交換する。

`all_stages`, `agree_trans`, `simultaneous_models`, `positive_models`, `recovered`, `future`

## 6. GeneralDictionaryUniformAlias258

任意assignmentについて固定type alias/row identityの解釈がfillと一致する。alias表を有限サイズで列挙したという主張ではない。

`target`, `mapping`, `read_exact`, `initial`, `actual_fixed`, `idempotent`, `type_exact`, `row_exact`, `atom_exact`

## 7. GeneralDictionaryDirectView258

任意段階nについてhistory再生なしのalias compileと展開Viewの意味を接続するが、slot数n+5とordinary数4+16nは増える。

`view`, `raw_exact`, `finite_exact`, `positive_exact`, `slots`, `ordinary_length`, `public_models`

## 8. GeneralDictionaryInitialFill258

任意assignmentについて内部binder型をslot2へ変更してからfillするcompleteを定義。初期0〜4全成分と全rowを保存し、初期rawモデル iff 完成後の全段階journalモデル。

`bind`, `complete`, `rows`, `initial`, `binder`, `view_exact`, `raw_initial`, `all_stages`, `public_agrees`, `complete_binder`

## 9. GeneralDictionarySourceExtension258

任意境界assignmentについて、初期0〜4全成分と全rowを固定する同一assignmentが全段階journalを満たす存在命題 iff 初期rawモデル。内部binder固定を要求しない。

`view_agree`, `model_initial`, `simultaneous_models`, `stage_models`, `exchange`

## 10. GeneralDictionaryPrivateBoundary258

提示したbad seedは初期モデルだが内部binderがbottom。旧binderまで固定する強いAgreeでは正段階モデルへ延長不能。任意境界の延長不能ではない。

`seed_not_binder`, `complete_holds`, `changes_seed`, `seed_extended`, `retained_binder_impossible`

## 11. GeneralDictionaryEarlySearch258

lower包絡が単調で各family indexより小さいという明示前提のもと、早期停止探索 iff 指定fuel区間内の一致。I45の両族へ適用する。

`search`, `lower_mono`, `exact`, `fastLower`, `fastUpper`, `lower_exact`, `upper_envelope`, `upper_exact`, `lower_refines`, `upper_refines`

## 12. GeneralDictionarySearchCost258

任意探索について訪問数≤fuel。対応する生成index iに到達する単独探索は≤i+1。巨大整数演算、名前生成、full fillのlower+upper合計時間は対象外。

`probes`, `fuel_bound`, `envelope_bound`, `match_bound`, `lower_match`, `upper_match`

## 13. GeneralDictionaryFastFill258

早期探索版fill/completeは旧関数と関数等号で一致。公開境界と全段階モデル定理をこの等号で継承する。

`lower`, `upper`, `lower_exact`, `upper_exact`, `fill`, `fill_exact`, `complete`, `complete_exact`, `all_stages`, `public_agrees`, `idempotent`

## 14. GeneralDictionaryPendingOutput258

具体252 sourceで任意出力Tyをslot3へ置いても初期raw/journalモデルは保存される。Outputs成立はそのTyが要求Foo(Foo(slot2))と意味同値であることが必要。

`replace`, `other`, `target`, `base_models`, `source_models`, `initial_models`, `rhs_fixed`, `outputs_exact`

## 15. GeneralDictionaryOutputPremise258

具体bottom出力で初期モデルとprepared Frameは成立するがOutputs/Holdsは成立しない。Frameだけから出力Evidenceを得る強化を否定する。

`bottom_not_expected`, `initial_not_outputs`, `initial_not_packet`, `frame_not_packet`, `expected_outputs`

## 16. GeneralDictionaryOutputInputs258

当該具体packet Inputsは任意assignmentで成立し、Holdsを初期rawモデルとOutputsへ正確に分解する。一般packet全体のInputs定理ではない。

`projection`, `ordinary`, `head_holds`, `inputs`, `packet_exact`

## 17. GeneralNominalActiveSupport258

任意Viewと任意二assignmentについて、実際に使う型成分および全rowが一致すればModels同値。未使用slot型は除けるがordinary/head RHS/descriptor parameterは追跡する。Step invariantではない。

`used`, `targetReads`, `perSlot`, `support`, `slot_member`, `target_member`, `head_member`, `descriptor_member`, `head_used`, `nominal_used`, `interval_left`, `interval_right`, `models_iff`

## 18. GeneralDictionaryOutputFrame258

具体252の初期identity Viewで実型supportは0〜2に限られる。slot3型だけを要求出力へ補完しても他の全成分と全rowを保存し、初期rawモデル同値を得る。

`identity`, `view`, `models_exact`, `support_small`, `unused_output`, `source_iff`, `complete`, `rows`, `outside`, `source_exact`

## 19. GeneralDictionaryOutputCompletion258

任意初期rawモデルのslot3補完後に実packet Holdsと既存installation effectのModelsを得る。旧言語Stepを書き換えていない。

`expected`, `rhs_exact`, `outputs_exact`, `completed_outputs`, `packet_exact`, `classes`, `installation`, `installed_models`

## 20. GeneralDictionaryOutputEvidence258

提示bottom seedには任意payloadのroot Evidenceがない。一方、任意初期rawモデルを補完したassignmentには明示leaf Evidenceを構成できる。

`no_initial_evidence`, `completed_evidence`

## 21. GeneralDictionaryOutputPublic258

任意公開境界について、slot3型だけを解放し他の全成分と全rowを固定するinstalledモデルの存在 iff 元の初期rawモデル。

`Agree`, `completion_agrees`, `source_agree`, `installed_initial`, `installed_exact`, `public_models`

## 22. GeneralDictionaryCompletedReadback258

固定の閉じた展開代表の深さは4。任意初期rawモデルの補完後にその代表の意味が成立する。補完前bottomにはEvidenceなし。一般sourceの深さ上界ではない。

`closed`, `meaning`, `depth`, `uniform`, `not_before_completion`

## 23. GeneralRebaseStep258

任意有限basisと任意observerについて、remainingがbasisのsublistである状態をfilterし、実差分のあるwriteだけをStepとする。各Stepでremaining長が厳密減少し全状態Acc。observerの言語的正当性は別の未証明義務。

`state_ext`, `initial`, `done`, `Proposal`, `write`, `Observer`, `tryWrite`, `Step`, `tryWrite_exact`, `filter_strict`, `decreases`, `accessible`, `no_self_step`, `present`, `lowerAtoms`, `upperAtoms`, `binderFacts`

## 24. GeneralDictionaryRebaseStep258

固定I45 fixtureの5事実を提案するobserverについて、初期から一度だけinstallして終端へ達する。二歩不能、全正段階の旧completed state投影は終端。同じ意味の一般inspection実装とはまだ接続していない。

`facts`, `initialState`, `finalState`, `observe`, `project`, `writes_once`, `first_step`, `final_stops`, `first_unique`, `no_two_steps`, `terminating`, `fixed_aggregates`, `old_positive_project`, `old_repetition_blocked`

## 25. GeneralDictionaryRebasePublic258

任意段階nと公開境界について、旧completed state nと新project nの存在モデルが同値。初期0〜4全成分と全row固定、内部binderは解放。中間subsetの言語的正当性や全microstep simulationは主張しない。

`Models`, `initial_exact`, `final_exact`, `final_public`, `projected_public`, `old_new`

## 26. GeneralRebaseBudget258

任意新Step run長nについて n+終点remaining長≤始点remaining長。初期からbasis長以内、固定I45では1以内。同じproposalのwriteは冪等で次のtryWriteはnone。旧Stepや実時間の上界ではない。

`budget`, `source_budget`, `idempotent`, `duplicate_noop`, `fixture_budget`
