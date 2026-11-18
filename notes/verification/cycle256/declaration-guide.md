# Cycle256 宣言ガイド

101個の明示的なdef/theoremを列挙する。生成・private宣言はFull監査で別途検査。
全ての定理は型に現れるデータに全称量化される。省略されたimplicit引数も含む機械出力の完全な型は [all-types.txt](all-types.txt)、主要型は [critical-types.txt](critical-types.txt)。以下の各節に共通前提を記し、さらに必要な前提は各行に記す。

## GeneralNominalInputOccurrences256

任意のregistry・roles・state・root・key・plan、またはcontext/declaration/bounds。FrameまたはFinishedと宣言のinputNamesへの所属を明示前提とする。

- `frame_finished`: 実Frameから当該packetのhead検査Finishedを得る。
- `report_nonempty`: Finishedな実reportの宣言入力名には少なくとも一つoccurrenceがある。
- `frame_nonempty`: 実Frameから同じ非空性を得る。

## GeneralNominalAggregateAtoms256

任意の非空interval列、任意のCompTerm置換、任意のpool。空列にはこれらの等式を適用しない。

- `lower_atoms`: 置換後lower集約のunion原子列は各lower端点の原子列を連結したものに等しい。
- `upper_atoms`: upper集約についてintersection原子列の同じ等式。
- `lower_supported_iff`: lower集約全体の支持と各lower端点の支持は同値。
- `upper_supported_iff`: upper集約全体の支持と各upper端点の支持は同値。

## GeneralNominalSourceAggregate256

任意registry/context/owner keys。report補題はFinishedと当該入力名所属を要求。置換はidentityに限定し、basisは当該contextのCanonicalBasis255。

- `source_variable`: context.state.sourcesの任意の名前のvarはbasisに属する。
- `report_lower`: 実reportのlower集約はbasisに支持される。
- `report_upper`: 実reportのupper集約はbasisに支持される。
- `report_prepared`: 両sideのCheckedNormal.prepareが実際に成功する。
- `frame_prepared`: Frameから上記成功を得る。後続全trace固定basisとは主張しない。

## GeneralNominalHistoricalAggregate256

任意の有限old定義列、pool、interval列。oldは実際に渡したordered mappingで解釈する。一般のsource閉包を仮定なしで主張しない。

- `EndpointSupported`: lower端点はunion、upper端点はintersection原子で支持されるという条件の定義。
- `rewrite`: old置換後の両集約を各sideで正規化する定義。
- `check`: 各実端点の支持を有限allで検査するBool。
- `prepare`: 非空かつ検査成功の場合だけBoundsを返す内部adapter。
- `check_exact`: Bool成功とEndpointSupportedは同値。
- `supported_iff`: 非空なら端点ごとの支持と置換後両集約の支持は同値。
- `prepare_exact`: prepare成功は非空・EndpointSupported・結果がrewriteであることと同値。
- `values`: 非空かつ支持の下、全assignmentで結果はsolve(old)下の元lower/upperとEquivalent。
- `fits_exact`: prepare成功の下、全assignment・全actualで結果Fitsとsolve(old)下の全occurrence Fitsが同値。
- `finite`: 支持なしでもrewriteの両値は有限candidate列に属する。この事実だけで意味保存を言わない。

## GeneralNominalFrameAggregate256

任意の実Frameと宣言入力名。identity結果のpoolは各plan.contextから取る。

- `nonempty`: 入力名の実occurrence列は非空。
- `prepare_iff`: 非空条件をFrameで供給したprepare成功の正確な条件。
- `identity_supported`: identity old=[]ではendpoint支持を実source所属から導く。
- `identity_prepared`: identity snapshotでprepare成功。
- `identity_fits`: 全assignment・actualに対しidentity結果Fitsと全実occurrence Fitsが同値。

## GeneralNominalInitialAggregate256

任意初期context・root・labels、state=(initial context root).coreの任意実Frameと入力名。labelsのground条件は不要だが、将来portsの列挙はこの結果に含まれない。

- `prepared`: 開始前に固定したSourcePublicBasis255上でprepare成功。
- `fits`: 同じ固定basisの結果について、全assignment・actualで実occurrence Fitsと同値。

## GeneralDictionaryReachableAggregate256

固定された実I45 LooseIteration240 familyの全n。任意source一般ではない。semantic結果は指定witnessだけでなく量化したassignmentに関する。

- `old_atoms`: 実ordinary履歴atoms nは次段に保持される。
- `lower_equations`: 実次段ordinaryには生成されたlower union方程式が含まれる。
- `lower_value`: atoms nを満たす任意assignmentでlower nは初期source2とEquivalent。
- `current_atoms`: 実stage Modelsからatoms nの成立を抽出。
- `source_lower`: 実stage Modelsを満たす任意assignmentで同じlower同値。
- `representative`: 固定Bounds(var2,var4)の定義。
- `pairs_exact`: 実planの入力0のoccurrencesは(lower n,4)の二重列。
- `frame`: 全nの実stageに当該planのFrameがある。
- `fits_exact`: 全stage Models・全actualで固定代表Fitsと実capture Fitsが同値。
- `reachable_all`: 全nのstageが元I45 source境界から到達可能。

## GeneralPresenceOrderedAppend256

任意Name、任意置換・有限定義列。ordered mappingの定理ではDecidableEq Nameを使用。SafeOrderやsource到達は主張しない。

- `row_comp`: row置換の合成則。
- `type_comp`: type置換の合成則。
- `row_identity`: row identity置換は元項に等しい。
- `type_identity`: type identity置換は元項に等しい。
- `mapping_row`: ordered mappingのrow成分は元名のvar。
- `mapping_append`: 列appendのtype mappingは後半展開に前半mappingを代入したもの。
- `mapping_snoc`: 末尾に加えたtargetの値はそのrhsを旧mappingで展開したもの。

## GeneralDictionaryAggregateHistory256

実I45 familyの全n。ただしhistoryは実ordinaryに含まれるlower方程式の射影であり、全snapshotとは同一視しない。

- `tree`: 初期var2を重複unionで増やした木の定義。
- `entry`: 実lower方程式に対応する1 entry。
- `history`: 過去lower entryをreplay順に連結した射影history。
- `block_in_source`: historyの方程式blockは実atoms nに包含。
- `current_expansion`: 現在lower nのordered展開はtree nそのもの。
- `targets_above`: 任意history targetは初期seed4より大きい。
- `upper_fixed`: 初期upper source4の展開はvar4のまま。
- `tree_atoms`: treeのunion原子所属はvar2であることと同値。
- `pool`: 固定2原子pool[var2,var4]。
- `tree_normal`: 全nのtree正規化はvar2。
- `endpoint_supported`: 実capture列の両endpointがこのpoolに支持される。
- `rewritten`: 実captureをhistoryで展開・正規化した結果は固定代表。
- `prepared`: 全nで内部prepareが固定代表を返す。

## GeneralDictionaryAggregateBasis256

同じ実familyの全n。固定source/public basisは初期contextから取る。

- `initial_basis`: 任意labelsについて2原子poolは初期SourcePublicBasisの部分集合。
- `pool_unique`: 2原子poolに重複なし。
- `pool_private_free`: 任意割当originの名前(seed4)はpool原子から読まれない。purpose0/1だけに限らない。
- `prepared_finite`: 固定代表は両sideの有限candidate列に属する。
- `source_history`: 任意stage Modelsは射影history方程式も満たす。
- `prepared_source_fits`: 任意stage Models・actualに対し、prepareが返す結果のFitsは元capture Fitsと同値。

## GeneralDictionaryAggregateRows256

同じ実familyの全n。rowについての最初の結果は構文metadataの観察であり、activeなrow制約や公開需要への流出ではない。

- `historical_row`: 実anchorのcompile後slot.rowはvar(lower n)のまま。
- `row_read_retained`: n+1では当該private lower名のrow読みが残る。
- `row_name_private`: その名前はpurpose0、version付きのprivateNameそのもの。
- `outside_initial_names`: その名前は初期0..4のいずれでもない。
- `eraseSlotRows`: 任意Viewのpaired slot.row metadataだけをemptyにした定義。ordinary row/descriptor rowは不変。
- `slot_rows_irrelevant`: 任意View・assignmentでmetadataのみの消去は現在View.Modelsを定義的に保存。
- `erased_row_sources`: 消去後metadataのrow読み列は空。

## GeneralDictionaryHistoricalFields256

実familyの全n、全base slot。poolは初期5変数。privateな補助snoc_otherもFull監査に含む。

- `past_expansion`: index≤nの任意過去lower indexもtree indexに展開される。
- `initial_name`: 任意name≤4はhistoryで変化しない。
- `pool`: 固定5変数pool。
- `variable_fixed`: 任意name≤4のvarはこのpoolで正規化しても不変。
- `tree_fixed`: 全tree nはvar2へ正規化される。
- `representative`: slot値<5は元名、それ以外は2という代表名の定義。
- `representative_small`: 全slotの代表名は4以下。
- `slot_fixed`: 全実base slotのcompile後typeは対応var代表へ正規化される。
- `slot_supported`: 全実base slotのtypeはunion-sideで固定poolに支持される。
- `slot_prepared`: 全実base slotのtypeのprepareが対応var代表を返す。

## GeneralNominalSlotTypeMap256

任意RawView・slotごとの新TyTerm・assignment。現在のView.Modelsのみを対象とし、将来Stepは対象外。

- `map`: slot.typeだけを差し替え、他のtype/row consumerはそのままにする定義。
- `models_exact`: 全indexの新旧slot type値がEquivalentなら、View.Modelsはiffで保存される。
- `ordinary_unchanged`: ordinary listは文字通り変わらない。
- `nominals_unchanged`: nominalsは文字通り変わらない。

## GeneralDictionarySlotView256

同じ実familyの全n。expandedはlower historyのcompile、compactはslot typeのみ5代表にする。全consumer有限化ではない。

- `expanded`: 当該historyでcurrent raw stateをcompileしたView。
- `compact`: slot typeのみ代表に差し替えたView。
- `compact_exact`: 全assignmentでcompact.Modelsとexpanded.Modelsは同値。
- `recovered`: history方程式が成立するassignmentなら、compactと元raw stateのModelsは同じassignmentで同値。
- `source_models`: 実stage Modelsならcompact.Modelsも成立。
- `slot_values_finite`: 全slot type値は固定5変数poolに属する。
- `slot_count`: それでもslots数はn+5である。
- `source_erased_rows`: 実stage Modelsならinactive slot.row消去後も現在View.Models成立。
- `compact_solved`: 前提なしでcompact.Modelsはsolve(history)下の元raw Modelsと同値。
- `solve_initial`: 任意name≤4の完全なComp成分はsolve(history)で不変。
- `public_models`: 任意boundaryについて初期0..4の完全成分を固定したraw/compactモデルの存在は同値。逆方向のprivate割当は変えてよい。

## GeneralNominalOrderedRawPublic256

任意raw state・有限ordered entries・private名集合hidden・公開boundary。置換による消去のみであり、新しいblockへの更新の正当化ではない。

- `compiled_solved`: 全assignmentでcompile.Modelsはsolve(entries)下のraw.Modelsと同値。
- `recovered`: 実block方程式成立の下、同じassignmentでcompile/raw Modelsが同値。
- `solve_public`: 全targetがhiddenにあれば、solveは全unhidden Comp成分と全row成分のPublicAgreeを保つ。
- `public_models`: blockがraw.ordinaryに実包含し全targetがhiddenなら、任意固定public assignmentの下でraw/compileモデル存在が同値。SafeOrder/Coherentは不要だが、有限表現や新block可解性は結論でない。

## 全体の未完
任意source traceのside別pool閉包、全consumerのprivate非流出、active rowの処理、strict新fact、後継Step Acc、mixed-time packet、Permitted、12則とEvidenceNodeは未完。これらを仮定した結果で完成扱いしない。M1の主型性・B4 Statementの証明ではなく、そのための補助である。
