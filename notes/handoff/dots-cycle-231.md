# dots cycle 231 — I44版付きaggregateと非空モデル拡張

開始: 2026-11-17 03:33:16 UTC。研究締切04:18:16、公開照合締切04:28:16。
I44を既定の監督inbox手順上の判断として確認して実行。言語意味論の新判断なし。
最新確認integration: 6437ed3b1（I44/standing-orders差分なし）。
質問ノート追加なし。cycle230の旧V8 EvidenceNode反例はそのまま有効。

## 結果と厳密な範囲

版付きlower/upperのID、Fresh、予約、capture、merge、total packet、
frame、evidence部品を同じ命名に揃えた。実際の230 terminal例について、
旧journalを全部保持した再構成状態を明示し、次をLeanで証明した。

* 任意の旧full journalモデルmに対し、新2nameだけを(m 2).1へ割り当てる
  extend mが再構成状態のモデルとなる。旧journalSourcesにある全sourceの
  Assignment値そのものを保全する（型の同値だけではない）。
* 再構成状態のModelsは「旧full Modelsかつ新merge方程式」と同値。
* 再構成状態にはモデルが存在し、その全モデルについて、現行frameの
  versioned total Evidenceが存在する。旧Evidenceや必要な結論を仮定していない。
* 同一観測の再訪では版/keyが同じ。観測端点列が違えばIDが違う。
  actual中心、出力target、child identity/順序、元sourceを変えない。

これは新operational boundaryの完成ではない。reconstructedで使う
Journal.refreshはデータ構成子であり、旧Refresh/Stepの証明ではない。
新Reachable/Stable、12laws、V8 EvidenceAt、一般EvidenceNodeは未証明。
旧counterexampleを消した、M1が完成した、停止性を回復したとは主張しない。

## 追加Lean（28 modules）と主要な定理

量化子は以下で明示。全定義・補題名の索引:
notes/verification/cycle231/declaration-index.txt。正確な型と証明は各source。

### 命名・割当（一般のstate/registry/packet/modelについて）

1. GeneralNominalAggregateVersion231: code/versionの単射性、slot_eq_iff。
   任意の同一seed/root/decl/purpose/nameで、slot一致と順序付きoccurrences一致が同値。
   新positionは正であり、legacy position0と異なる。
2. GeneralNominalVersionedAllocation231: propagate_models。
   任意state/registry/root/decl/bindings/modelで、伝播後Modelsは旧Models、
   Compatible、および新merge全式と同値。Fresh/予約/所有keyも版に整合。
3. GeneralNominalVersionedCapture231: capture_interval_exact/propagated_capture_exact。
   明示されたCompatible/merge・宣言名条件の下で、capture区間と元boundsの
   lower/upper意味が一致。singletonは元source pair。
4. GeneralDictionaryVersionedSupport231: journal_support。
   230の全journal supportが具体8-IDリストに包含される。
5. GeneralDictionaryVersionedNames231: version_changed/fresh_outside/retains_journal。
   230の旧新boundsで版が違い、新2nameは全旧support外。具体拡張は旧Modelsを保持。
6. GeneralDictionaryVersionedMerge231: common_model。
   旧journalと新raw mergesを満たす共通モデルの存在。旧lower/actual値も保持。

### 完全packetと保存

7. GeneralNominalVersionedFrame231: binder_eq、child中心/identity/role/count保存。
   任意packet/planでactual中心は旧と一致。入力endpointそのものの一致は主張しない。
8. GeneralNominalVersionedPlans231: 新Ordinary/privateState/SchemaHolds/Inputs/
   Outputs/Holds。旧total packet条件を削らず、capture経由の参照だけ整合的に変更。
9. GeneralDictionaryVersionedProjection231: 具体230の新projection/selfChecks/HeadModels。
10. GeneralDictionaryVersionedPacket231: packet_holds。
    具体拡張モデルで新total Holds。関連出力Oと全head/capture条件を含む。
11. GeneralNominalVersionedPool231: reserved_included。
    bindingsが明示有限候補list内ならreservedはそのsourcePool内。同一観測の再訪key一致。
12. GeneralNominalVersionedCandidates231: Prepared/Survivor/Unique等の新部品。
    Freshは各located boundsに依存。出力をhead-only選択に混ぜない。
13. GeneralNominalVersionedEffects231: bodyHolds_iff/class_effects_iff。
    任意plan/modelで新actual/default bodyと旧bodyの意味が一致。出力共有条件を保持。
14. GeneralDictionaryVersionedPrepared231: 230の新Fresh/Prepared/Survivor/Unique。
15. GeneralNominalVersionedRefinement231: current→new privateStateのRefines。
    元source/row/known、Models制限、key所有、Linked保存を実証。
16. GeneralNominalVersionedRevisit231: 通常propagateではinspection/版/key不変、
    fixed-view Modelsの冪等性。観測変更を含む実traceの停止性ではない。
17. GeneralNominalVersionedTransport231: holds_iff。
    任意追加reserved/atoms/allocatedとmodelで、固定観測の拡張planのHoldsは
    元Holdsかつ追加atoms全部と同値。
18. GeneralNominalVersionedEvidence231: 新Frame/Certificate/Evidence部品。
    certificate_of_semanticsは新total Holds、全子、Ready、ClassEffectsから構成。
    SourceBoundaryのEvidenceAtという名前に置き換えた仮定ではない。
19. GeneralDictionaryVersionedEvidence231: common_model_evidence。
    旧full journal、新Holds、新Evidenceを共に満たし、同じモデルの旧Evidenceは偽。

### 再構成・任意旧モデルの保全

20. GeneralNominalVersionedConservative231: terminal_holds_iff。
    任意terminal plan/modelで、全入力endpoint値の明示一致を仮定すると
    新旧total Holdsが同値。この一致は230反例で自動には成り立たない。
    非terminalのfull Holds比較は未証明。
21. GeneralNominalVersionedPreparedTransport231: frame_extended。
    固定観測、Linked保存、新Holdsの実在証人の下で拡張後の現行Frameを構成。
22. GeneralDictionaryVersionedUniversal231: 230旧full Modelsを満たす任意mで、
    現行観測のbounds、projection、actualFits、関連出力Oを導出。
23. GeneralDictionaryVersionedCompletion231: nonvacuous_modelwise_completion。
    任意mが旧Modelsと新merge全式を満たせば、新total Holds/Certificate/Evidence。
    この条件を満たすmも実際に構成。Evidenceを仮定していない。
24. GeneralNominalVersionedInstallation231: replay_holds_iff/replay_private_models。
    任意plan/modelについて、新予約・atoms・所有keyの明示context拡張を行った
    replayPlanのHoldsは元新Holdsと同値。まだoperational installerではない。
25. GeneralDictionaryVersionedReconstruction231: models_iff/inhabited。
    明示再構成状態の全Modelsを旧Models+新mergesとして特徴付ける。
    元source、centers、旧plans/effectsを保持。空の子を証明。
26. GeneralDictionaryVersionedFinal231: nonvacuous_current_frame_completion。
    再構成状態のモデル非空、かつ任意の全モデルに現行frameの新Evidence。
27. GeneralNominalVersionedFiniteBindings231: bindings_included/reserved_included。
    name/endpointの有限候補とcapture長上限を明示仮定し、全該当bindingsを
    有限列挙してreservedをsourcePoolへ含める。実traceのその仮定は未証明。
28. GeneralDictionaryVersionedModelExtension231: every_model_extends。
    任意の230旧full Models mに対して、全旧journal source値を保全する
    再構成モデルnとその新Evidenceを実際に構成。結論の循環仮定なし。

## 検証

* Lean4.35.0、focused lake build Yulang.<module> --wfail を各追加moduleへ実施。
  最終まとめfocused buildのログはnotes/verification/cycle231/focused-build.txt。
* lake env lean --trust=0 Audit/Cycle231Allocation.lean: PASS、6 modules/102 constants。
* lake env lean --trust=0 Audit/Cycle231Packet.lean: PASS、13 modules/254 constants。
* lake env lean --trust=0 Audit/Cycle231Final.lean: PASS、9 modules/112 constants。
* 合計28 modules/468 constants。定義・生成補助宣言を含み、468個の新定理ではない。
  許可依存はpropext/Classical.choice/Quot.soundのみ。
* sorry/新axiom/native_decideなし。既存Lean変更なし、barrelに追記のみ。
  凍結Audit.lean/README.mdはintegrationと一致。主要定理は独立Auditへ登録。
* 全体lake build/verify-lean.shは指示に従い実行していない。
  全体gate PASSは監督側で確認が必要。
* read-only独立レビュー: Models→新merges→reconstruction→Evidenceの依存に循環なし。
* Yulang2 x-oracleのrecord/associated case制約を確認。内部aggregate版付けに
  runtime oracleはなく、実機conformanceは主張しない。

## I44受け入れ条件の状況

版付き割当と旧制約保持: 部品および230モデル再構成で達成。
230非空Evidence回復: 新evidence部品として全モデルで達成。
実際の後継boundary上のReachable/Stable/EvidenceAt: 未達。
元source/actual中心/共有維持: 列挙した一般補題と230再構成で達成。
12laws、停止性、199/202/204/206/218の後継boundary回帰: 未達。
一般EvidenceNode: 未着手。旧偽命題の証明を再試行しない。

## 次の3件

1. versioned current plan/effectを実際に記録する後継journal/transitionと非terminal
   child投入を作り、exact install_modelsを証明。
2. 一般のsource保全モデル拡張とframe/effects保存、230実traceのReachable/Stable、
   SourceBoundaryの12lawsを接続。
3. 実traceの有限endpoint/name候補・長上限または別の整礎測度を証明し停止性へ接続。
詳細: notes/design/2026-11-17-cycle231-successor-journal-gap.md。

## 公開・時間・制限

途中公開: 2d27058d（6 modules）、375d2301（追加13 modules）。
40分前後の心拍: d419a09b。最終公開・照合結果は完了時に追記。
公開先はwork/dots-mainのみ。既存公開を消さず、最終追加分も公開する。
環境中断なし。初回局所型不一致は修正して再build済み。全体gateは未実施。
使用量の枠: 不明。
