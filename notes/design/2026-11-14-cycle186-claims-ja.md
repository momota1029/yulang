# Cycle186: 定理の量化範囲と残る橋

対象は実 `GeneralNominalCenteredHeadWFBoundary.boundary`（V6）。15新規モジュール・57公開定理。すべて一般carrier上の補助的な健全性／モデル拡張の定理であり、57本のB4フィールドを閉じたという意味ではない。全定理の名前・暗黙引数・量化子・前提は `notes/verification/cycle186/theorem-signatures.md` と `lean/Audit/Cycle186PublicTypes.lean` の実Lean出力に保存する。

## 主要成果

1. `HeadIdentityCenters186.registered_identity_centers_same`: 任意のChecked registry、WF到達可能state、そこに登録された任意の2siteについて、数値invocation identityが等しければ、すべてのfull Modelsの下で対応centerはSame。whole occurrence等式、同じcapture bounds、point/nonpoint選択一致は仮定しない。子producerを復元し、数値identityへの強帰納で示す。
2. `HeadCandidateOverlap186.candidate_overlap`: 任意の登録inputを持つ現在候補、可視declaration、その非output/nonpoint actual head-useについて、binderがfullSourcesと重なるなら、すべてのfullモデルでそのoriginとbinderはSame。歴史planの存在は実supportから導く。初期root限定を除去したが、候補input登録・current context・visibilityは残る。
3. `HeadConservativeExtension186.conservative_extension_iff`: 任意有限個のactual/nonoutput head-useについて、旧fullモデルとその全support値および選択したcapture endpointsを保存する拡張が存在し、各NominalArgument.Holdsを満たすことと、観測存在・全観測のFits・同binder観測整合性が同値。Checked、WF到達、登録input、role整合、current context、可視declaration、旧Modelsは前提。origin支持とendpoint分離を導出し、callerのlinked前提を除去。point/nonpoint混在も扱う。
4. `HeadEquationExtension186.head_equations_extension_iff`: 上記をheadの全useへ広げ、Finishedを加えると、拡張モデルで実HeadEquationsの全3項（input.Holds、全inputNameのFits、whole head SchemaHolds）を満たすこととCompatibleが同値。Compatibleはhead tests、全use観測存在、Fits、同binder整合性。Plan.Holds全体ではない。
5. `HeadFrameExtension186.frame_extension_iff`: 任意の現在の実Frameについて、そのFrameから登録・role/context整合・Finishedを導き、同じ全head拡張iffを得る。Frameや選択だけからCompatibleを自動導出したとは主張しない。
6. `HeadRevisitExtension186.revisit_extension_iff_bounds`: 任意の現在Frameと、同数値identity／同declarationの登録歴史planについて、旧fullモデルの下で同じ保守的全head拡張の存在は、現在captureの各head観測がFitsを満たすことだけと同値。tests・観測存在は歴史schemaから、非point binder衝突は同nameへ、point衝突はFitsへ還元する。歴史planの存在と現在のFitsは未解消であり、一般選択候補で自動成立とは言わない。

## モジュールごとの全公開定理

以下の各行は量化範囲を共通の前提として読む。個別定理で不要な前提は実型に存在しない。正確な全型は上記署名ファイルを参照。全項目は「補助（辞書健全性・モデル拡張に効く）」であり、M1健全性／完全性／主型性の全体完成ではない。

- `ChildSemantic186`: 任意2plan、seed/parent identity/declaration一致、同一所属clause、すべてのinputNameのbinder Sameの下で、`child_centers`は任意引数indexの子center Same、`child_centers_list`はdefault0を含む全index版。
- `HeadSchemaSemantic186`: 任意model/originで`related_symm`は観測集合一致またはSameの対称性、`related_holds`はその関係で任意ExprのHoldsを移送。`structural_related`/`nominal_related`は対応投影の観測集合一致。`schema_correspondence`/`schemas_correspondence`は任意query(列)、起点関係、所属useから名前・modeを保存した対応useを導く。`head_correspondence`は同宣言/configと意味的center一致を持つ2planのhead版。`input_use`は任意Finished planとinputNameからactual use存在。`binder_same`は同宣言/config・意味的center・両head SchemaHolds・Finishedの下で任意inputNameのbinder Same。
- `HeadIdentityInduction186`: 任意site/modelの`centers_self`、Checkedな実traceと局所binder移送則の下で`trace_identity_centers`。この局所則を次モジュールで独立に充足するので循環前提ではない。
- `HeadIdentityCenters186`: 実traceと2登録plan・同宣言・意味的親center・full Modelsから`trace_registered_binders`。Checked traceと同数値identityの2登録siteから`trace_registered_identity_centers_same`、そのWF版`registered_identity_centers_same`。同数値identity・同宣言の登録planの任意inputNameについて`registered_identity_binders_same`。
- `HeadCandidateSemantic186`: 登録input候補と登録歴史plan、数値identity／declaration一致、current context、actual use、full Modelsから`candidate_actual`。さらに非outputと両capture非pointの下で`candidate_nonpoint_overlap`。候補自身のhead SchemaHoldsは不要。
- `HeadCandidateOverlap186`: `candidate_overlap`の全前提・結論は主要成果2。
- `HeadCandidateExtension186`: `candidate_extension_iff`は主要成果3の前段。旧fullSourcesだけを固定し、endpoint/origin所属を明示前提に取る。非point限定はなくpointもFitsから処理。より強い適用範囲の後継はConservativeExtension186だが削除しない。
- `HeadCandidateSupport186`: `schemas_bounded_roots`は実query範囲に限った任意schema列のorigin支持、`normalized_length`は任意pattern列の正規化長保存、`head_roots`はrole整合planの実center列のみの支持（余分な0なし）。`current_source`は現在source→full支持、`registered_center`は登録site center→full支持、`candidate_origin`は登録／role整合候補useのorigin支持。`singleton_endpoints`はcurrent候補の単一capture occurrenceなら両endpoint支持。`current_capture_separate`はWF到達／current contextの任意packetのendpointと任意purpose≥7名の分離。`nonpoint_binder_endpoints_separate`はそこから非output/nonpoint binderと任意capture endpointの分離。
- `HeadConservativeExtension186`: 任意有限use列の`lower_mem`/`upper_mem`は追加支持への所属。`conservative_extension_iff`は主要成果3。
- `HeadSchemaNames186`: 任意query(列)・actual modeの所属useに対する`schema_actual`/`schemas_actual`、任意planの`head_actual`。実translator scopeから`head_input`。Checked declarationのoutputOnlyと正規化変数保存から`input_not_output`と`head_not_output`。Finishedは不要。
- `HeadEquationExtension186`: 任意planで有限列挙の`uses_mem`/`uses_cover`。登録・role整合planと拡張支持値の一致の下で任意testの`tests_frame`。`head_equations_extension_iff`は主要成果4。
- `HeadFrameExtension186`: 任意実Frameの`frame_finished`/`frame_aligned`。`frame_extension_iff`は主要成果5。
- `HeadTestSemantic186`: 任意Related originsの`related_head`、任意query(列)のtest対応`schema_tests`/`schemas_tests`、同宣言/config／意味的centerを持つplanの`head_tests`、登録inputと同数値identity歴史plan・同宣言/current context・full Modelsの下で全candidate testを満たす`candidate_tests`。
- `HeadBinderCollisions186`: 任意非output point captureの`point_binder`、両非output/nonpoint captureの同binderから`nonpoint_name`、point captureのFitsから値とbinderのEquivalentを得る`point_fits`。同identity歴史planを持つ現在候補と2actual/nonoutput use、full Models、両観測のFits、同binderの下で`historical_coherence`。point/nonpoint混合衝突はnamespace分離で排除。
- `HeadRevisitExtension186`: 登録input、同数値identity／同宣言歴史plan、current context、full Modelsの下で`compatible_iff_bounds`。実Frame版`revisit_extension_iff_bounds`は主要成果6。

## 13項目とB4の状態

Checked、Models、Step、Stable、Generated、RootPending、RootK2、CandidateK2、InspectionPending、Survivor、Evidence、Reorders、DictionaryEquivalentはいずれも現在WF境界で参照する一般nominal定義が存在する。V6追加のOutputConflictも定義あり。ただし言語全体の網羅性や定義項目ごとの証明完了を意味しない。

今回閉じた一般B4フィールドは0。一般EvidenceNodeはOPEN。現リポジトリにはB4SkeletonV6構造体がなく、旧V5の14フィールドの分母をV6へそのまま移さない。旧GのRemaining4本とWF/V6の未完事項を混同しない。依存到達検査は一般WF rootsと今回の局所完成rootsを別々に測る。

## 次に必要な3橋

1. 現在captureの`BoundsFit`を、実inspectionと記録済みmerge方程式から導く。単にcaller前提へ戻さず、未登録reservation endpointの変更可能性と旧support保存の範囲を分析する。
2. 初回候補（対応する登録歴史planがまだない場合）のCompatible生成。再訪iffの歴史plan存在を一般選択から導いたことにはしない。
3. 全head拡張からOutputEquations・child materialization・子証拠・親証拠へ。既存HeadWFJoinCounterexampleは現在境界のmulti-tag生成欠落を反証しており、Astra担当の境界修復を勝手に変更しない。

新しい言語意味論の選択や仕様変更はない。Yulang2はfresh auditのx-oracleの既存結果を参照したが、この新一般carrier補題を新規実機実行で検証したとは主張しない。
