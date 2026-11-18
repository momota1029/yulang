# cycle250: snapshot refresh, same-witness metadata and stable owner execution

## 結果・復旧・時刻

開始2026-11-17T23:34:17Z（予定23:30より遅延）。親指定は実開始から約45分研究、55分以内（00:29Z）に検証・公開・報告。cycle249はcompleted、報告・remote bytes一致を確認済み。開始時にlatest integration/m1-final `11f14b58ae547f5991505e61923f8884144fa276` とstanding orders/inboxを再読。最終再取得integration `9ec236c7908e2f872be08556eb9693e294ae3741` でもstanding orders/inbox差分なし。I47(a)継続、I45変更なし、STOPなし。他writerなし。origin/workの追跡refは更新されない設定なので、明示fetchのFETCH_HEADで照合した。旧cycle247/248隔離ファイルや旧builder.lockを今回の紛失成果と誤認せず、公開対象から除外した。

34新規Lean module、明示259宣言。実際の完了時刻・最終検証結果・公開treeはverification/cycle250/publication-receipt.mdと完了heartbeatに記録する。使用量枠は不明。公開先はwork/dots-mainのみ。

## 前進した点

任意のmaterialized Journal全fieldについて同値な割当への意味的合同性を証明し、compile/substitution由来という前提を外した。実際のowner raw equationsから安全なsnapshot refreshを構成し、全予約slotを残して未使用→再使用にも備える。旧metadataは旧snapshotへ書き換え、新metadataは新witnessへ追加する有限実行器と、その同一witness存在モデル同値を証明した。

実captureのlower/upper、予約済みowner handle、固定登録表からの複数owner命令列について、coverage/coherenceと構造的実行成功を実装・証明した。actual source reachable snapshotからの初期化も接続した。ただし新source Stepの全packet生成、Permittedの供給、無条件Acc、EvidenceNode完成ではない。

## 追加モジュールと主要主張

名前は共通prefix GeneralNominal/GeneralPresenceとsuffix250を適宜省略。全宣言名、全34module名、source hashはCompleteAudit-declarations.txt / modules.txt / source-sha256.json。以下の量化は、明記した前提を満たす任意のframe・assignment・raw・command列について。

### A. snapshot equationと任意metadata

- SnapshotBlock.refresh_safe / refresh_models / rhs_snapshot: old SafeOrderとraw targets⊆oldの下で、old mappingでraw RHSをsnapshot化・dedupしたfresh blockはSafe。raw Coherentなら全変換済みraw equationを保持。rawを同時連立方程式として解いた主張ではない。
- SnapshotOwner / SnapshotMerge: concrete actual Definitions241.entriesを利用して同じframe変換・actual coherenceを供給。旧public値との分離条件を残す。
- ViewCongruence: 任意RawViewのparameters、FitsAll、descriptor、ModelsをSame（型同値・row等号）で保存。
- OriginViewCongruence: 任意origin witnessの輸送と判定保存。witnessの文字通り同一性は不要。
- ProjectionViewCongruence: anchor/test/capture/cross-captureの全fieldを保存。
- SchemaViewCongruence: Argument/Site、requirements、uses、schemaの合同性。
- ExprViewCongruence: 再帰Expr/ExprListの全constructorについて評価型同値、EquationHolds保存。
- JournalViewCongruence.models_iff: actual Packetの8field、class、effect、observed、全Journalに適用。provenance仮定なし。
- ArbitraryOwnerFrame.recovered / models_forward / public_models_iff: old blockモデルから任意Journal回復。fresh SafeとProtectedでforward、old Safeもあればbackward、old/fresh targetsがpublic names外なら存在モデル同値。

### B. 全予約slotの持続と新旧metadataの時刻

- JournalAppend: Deltaはobserved/sites/packets/effects/ordinary。attach_modelsは旧Modelsかつ**同じ割当**でDelta.Holds。rebase_attachで旧metadata追加と置換が可換。
- PersistentSnapshot.refresh_safe / target_list / raw_equations / retains_missing: 任意rawでもold Safeからfresh Safeと全旧target listの一致。rawにないslotは旧値を保持。rawの全制約を主張するには別途coverageとCoherentが必要。範囲外keyは無視され重複はfirst matchであり、その制限を隠さない。
- SnapshotRegression: old2=var0、3=var1にraw2=var3、3=var2を与える循環例。snapshotは2=var1、3=var0でSafe。実Common modelがsnapshotを満たしてもraw同時方程式を満たさない具体例。
- PersistentOwner: update、安全性、全target list、public_models_iff、covered/coherentなraw_constraints。旧Delta追加のaugmented_public_models_iffも同一witness。
- SourceDelta.compile_exact / attached_source_exact: actual source observations/sites/plans/effectsを有限Deltaへcompile。reachable mixed sourceとprepare成功から、追加old-blockモデル仮定なしでsourceModels＋consumers＋Deltaをframeへ接続。ただしeffect.Liveは指定した旧coreで評価し、live request再生成はしない。
- PostInstall.public_models_iff: 新Deltaをupdate**後**に追加する場合、旧側条件はfresh mappingで置換したDelta。forward/backward solveとabsorptionを用い、旧値への条件と取り違えない。
- PersistentSequence: 任意有限raw列のSafeと固定target list、各段publicモデル同値、後続actualowner coverage。入力列有限性はsource停止性ではない。
- FiniteInstallTrace.public_run_iff: 任意有限Command(raw,postDelta)列。final PublicModels iff 初期Modelsと、逐次computed fresh witnessで全Deltaが成り立つPermittedとpublic値一致が同じ割当に成立。PermittedはPropであり判定実装・source適格性からの自動導出ではない。

### C. 構成的予約・実owner producer・検査器

- ReserveBlock: bottomによるdedup予約、Safe、member iff、既存blockとのfresh append安全性。
- FrameReservation: poolは全Journal型read、consumers、old definition targets/RHS。pool外の新slot予約は旧metadataを保存し、明示shared list外ならpublicモデルを保存。
- StableSlots: 各inputのlo/hiをsingleton時も予約。実entriesは任意bindingsで全て予約内、2*names.lengthのslot list。Fresh/public分離/old Safeからactual snapshot equationとpublicモデル同値。
- InstallCoverage: actual owner entriesのcoherenceと予約coverageから、任意有限OwnerCommand列のCoveredを構成。computed next assignmentが全変換raw equationを満たす。
- CheckedInstall: pairwise coherenceCheckとcoverageCheckとSafeCheckの正確性。成功したstep/runは構造的に安全、covered、coherent。Noneは内部準備失敗で言語拒否ではない。
- OwnerOpening: current pool＋明示shared listのmaxを一度だけseedに選び、それより大きいstable keysを予約。seedはlegacy State.seedと同じとは主張しない。new handleは将来も保持する。
- OwnerExecution.checked_success / public_execution_iff: actual bindingsを用いる任意有限owner命令列でcoverageを供給しcheck成功。初期reserved witnessにおけるPermittedを残した正確なpublic存在モデル同値。
- SourceOwnerExecution: reachable actual mixed source＋prepared historical blockから上記有限実行器へ接続。初期source.Modelsとconsumers以外のold-blockモデル仮定を追加しない。以後の命令生成・Permittedは別義務。
- CoverageRegression: 範囲外keyと同key競合RHSのcheck=false/step=None。後者はcoverage=trueでもcoherence=false。
- PostInstallRegression: old2=exactEmptyから2=public0へupdateする例。新eq(2,public0)を後から付けるframeはモデルを持つが、先に付ける誤った時刻のframeには指定public widthモデルがない。
- TwoInstallRegression: 同じslot2をpublic0、次にpublic1へ更新。最初のmetadataは0=0に書き換わり、最後のmetadata2=1と両立。古い2=0を据え置く版は具体モデル不成立。有限checkerの実成功も証明。

### D. captureと登録表・複数owner

- StableCapture.bound_values / bounds_exact: singletonは旧endpoint式、複数は予約lo/hiを使う実Bounds。actual raw equationからlower/upper fold同値。空の場合もbottom/top値対応は証明。Fitsと全元intervalの同値は**nonempty**仮定付き。
- StableCaptureStep.generated_equations / snapshot_bounds_exact / actual_bounds_exact: Safe＋actual coverageからcomputed fresh solveがaggregate方程式を供給。旧blockモデルもあれば、旧original assignment上の全capture intervalとの一致。freshモデルを追加仮定しない。
- OwnerRegistry: (root,declaration) lookup、初回reserve、同じexact input-name listならhandle再利用、違えばNone。Registeredは各handle slotがframe target内という不変条件。有限refreshでtarget list不変なので維持。後のshared list増加でも再seedしないが、それでpublic escapeが安全になるとは主張しない。
- RegistryInvariant: Uniqueを前提として登録後Unique、登録後Safe、登録時public Models iff、trace後同handle再利用。RegisteredそのものをUniqueと混同しない。
- MultiOwnerCommands.compileMany_covered / checked_success: Registered frameに対し、lookup成功した任意request列のactual entriesからcoverage/coherenceを供給。複数ownerを交互に更新しても成立。unknown handleはNone。lookupは宣言妥当性検査ではなく、Deltaは依然入力。

## 検証とレビュー

全34新規moduleを依存順にLean4.35.0 `--trust=0 -DwarningAsError=true` でfocused再buildし、全259宣言をcollectAxiomsで検査するCompleteAuditを実行。許容依存はpropext/Classical.choice/Quot.soundのみ。完全なcommand列はfinal-build.sh、結果はfinal-build.txt。前回1473source hashは変更なし、今回import closure1425sourceをhash。新規に必要な旧Store241/Names241はstrict build済み。全体lake build / tools/verify-lean.sh / Yulang2実機テストは実行していない。全体検証は監督役担当。

独立read-onlyレビューで定理側の過大主張は見つからず、設計noteの「seedが上」を「seedは上界、slotが上」に訂正し、source受理不変という表現を明示shared listのmaterialized public Models iffへ限定。review note公開。新規Leanの禁止語、旧file凍結、import barrel追記だけ、remote全tree bytesはfinal-checks/receiptで確認する。

## 受入条件・未完了・次の候補

I47(a)の有限owner slot再利用、旧metadata意味保存、実capture式・登録表・複数ownerへのcoverage供給まで前進。I45条件は変更なし。I47のsource全体停止性、後継boundaryの12性質と回帰移植、B4/EvidenceNodeは未完了。

1. `StableCaptureStep250` を用いて新packetの全8fieldを生成するmixed-time compiler。旧raw context/projection originsはsnapshot、head/binders/schemaはfresh boundsを読む。既存PacketView243へ単一mappingを渡すだけでは代用できない。child/default/shared-center/output identitiesも必要。
2. actual source stepからpostDeltaとlive class/requestを生成し、`FiniteInstallTrace250.Permitted`を導出、source受理の健全性・完全性へ接続する。checker成功を意味受理と呼ばない。
3. sourceで発生するdistinct owner数・term growth・将来allocatorとpublic escapeを抑える不変条件を構成しAccへ。有限request listを与えたことだけでは満たさない。

199/202/204/206/218/230/239/240の言語回帰は旧証明を維持したが、新boundary上の移植検証は未実施。今回の内部負例は言語の新反例や新拒否判断ではない。新しい意味選択はせず質問noteも追加していない。
