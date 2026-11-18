from pathlib import Path
from collections import defaultdict
v=Path('notes/verification/cycle256');decls=v.joinpath('declarations.txt').read_text().splitlines();groups=defaultdict(list)
for d in decls:
 _,m,n=d.split('.');groups[m].append(n)
info={
'GeneralNominalInputOccurrences256':('任意のregistry・roles・state・root・key・plan、またはcontext/declaration/bounds。FrameまたはFinishedと宣言のinputNamesへの所属を明示前提とする。',[
'実Frameから当該packetのhead検査Finishedを得る。','Finishedな実reportの宣言入力名には少なくとも一つoccurrenceがある。','実Frameから同じ非空性を得る。']),
'GeneralNominalAggregateAtoms256':('任意の非空interval列、任意のCompTerm置換、任意のpool。空列にはこれらの等式を適用しない。',[
'置換後lower集約のunion原子列は各lower端点の原子列を連結したものに等しい。','upper集約についてintersection原子列の同じ等式。','lower集約全体の支持と各lower端点の支持は同値。','upper集約全体の支持と各upper端点の支持は同値。']),
'GeneralNominalSourceAggregate256':('任意registry/context/owner keys。report補題はFinishedと当該入力名所属を要求。置換はidentityに限定し、basisは当該contextのCanonicalBasis255。',[
'context.state.sourcesの任意の名前のvarはbasisに属する。','実reportのlower集約はbasisに支持される。','実reportのupper集約はbasisに支持される。','両sideのCheckedNormal.prepareが実際に成功する。','Frameから上記成功を得る。後続全trace固定basisとは主張しない。']),
'GeneralNominalHistoricalAggregate256':('任意の有限old定義列、pool、interval列。oldは実際に渡したordered mappingで解釈する。一般のsource閉包を仮定なしで主張しない。',[
'lower端点はunion、upper端点はintersection原子で支持されるという条件の定義。','old置換後の両集約を各sideで正規化する定義。','各実端点の支持を有限allで検査するBool。','非空かつ検査成功の場合だけBoundsを返す内部adapter。','Bool成功とEndpointSupportedは同値。','非空なら端点ごとの支持と置換後両集約の支持は同値。','prepare成功は非空・EndpointSupported・結果がrewriteであることと同値。','非空かつ支持の下、全assignmentで結果はsolve(old)下の元lower/upperとEquivalent。','prepare成功の下、全assignment・全actualで結果Fitsとsolve(old)下の全occurrence Fitsが同値。','支持なしでもrewriteの両値は有限candidate列に属する。この事実だけで意味保存を言わない。']),
'GeneralNominalFrameAggregate256':('任意の実Frameと宣言入力名。identity結果のpoolは各plan.contextから取る。',[
'入力名の実occurrence列は非空。','非空条件をFrameで供給したprepare成功の正確な条件。','identity old=[]ではendpoint支持を実source所属から導く。','identity snapshotでprepare成功。','全assignment・actualに対しidentity結果Fitsと全実occurrence Fitsが同値。']),
'GeneralNominalInitialAggregate256':('任意初期context・root・labels、state=(initial context root).coreの任意実Frameと入力名。labelsのground条件は不要だが、将来portsの列挙はこの結果に含まれない。',[
'開始前に固定したSourcePublicBasis255上でprepare成功。','同じ固定basisの結果について、全assignment・actualで実occurrence Fitsと同値。']),
'GeneralDictionaryReachableAggregate256':('固定された実I45 LooseIteration240 familyの全n。任意source一般ではない。semantic結果は指定witnessだけでなく量化したassignmentに関する。',[
'実ordinary履歴atoms nは次段に保持される。','実次段ordinaryには生成されたlower union方程式が含まれる。','atoms nを満たす任意assignmentでlower nは初期source2とEquivalent。','実stage Modelsからatoms nの成立を抽出。','実stage Modelsを満たす任意assignmentで同じlower同値。','固定Bounds(var2,var4)の定義。','実planの入力0のoccurrencesは(lower n,4)の二重列。','全nの実stageに当該planのFrameがある。','全stage Models・全actualで固定代表Fitsと実capture Fitsが同値。','全nのstageが元I45 source境界から到達可能。']),
'GeneralPresenceOrderedAppend256':('任意Name、任意置換・有限定義列。ordered mappingの定理ではDecidableEq Nameを使用。SafeOrderやsource到達は主張しない。',[
'row置換の合成則。','type置換の合成則。','row identity置換は元項に等しい。','type identity置換は元項に等しい。','ordered mappingのrow成分は元名のvar。','列appendのtype mappingは後半展開に前半mappingを代入したもの。','末尾に加えたtargetの値はそのrhsを旧mappingで展開したもの。']),
'GeneralDictionaryAggregateHistory256':('実I45 familyの全n。ただしhistoryは実ordinaryに含まれるlower方程式の射影であり、全snapshotとは同一視しない。',[
'初期var2を重複unionで増やした木の定義。','実lower方程式に対応する1 entry。','過去lower entryをreplay順に連結した射影history。','historyの方程式blockは実atoms nに包含。','現在lower nのordered展開はtree nそのもの。','任意history targetは初期seed4より大きい。','初期upper source4の展開はvar4のまま。','treeのunion原子所属はvar2であることと同値。','固定2原子pool[var2,var4]。','全nのtree正規化はvar2。','実capture列の両endpointがこのpoolに支持される。','実captureをhistoryで展開・正規化した結果は固定代表。','全nで内部prepareが固定代表を返す。']),
'GeneralDictionaryAggregateBasis256':('同じ実familyの全n。固定source/public basisは初期contextから取る。',[
'任意labelsについて2原子poolは初期SourcePublicBasisの部分集合。','2原子poolに重複なし。','任意割当originの名前(seed4)はpool原子から読まれない。purpose0/1だけに限らない。','固定代表は両sideの有限candidate列に属する。','任意stage Modelsは射影history方程式も満たす。','任意stage Models・actualに対し、prepareが返す結果のFitsは元capture Fitsと同値。']),
'GeneralDictionaryAggregateRows256':('同じ実familyの全n。rowについての最初の結果は構文metadataの観察であり、activeなrow制約や公開需要への流出ではない。',[
'実anchorのcompile後slot.rowはvar(lower n)のまま。','n+1では当該private lower名のrow読みが残る。','その名前はpurpose0、version付きのprivateNameそのもの。','その名前は初期0..4のいずれでもない。','任意Viewのpaired slot.row metadataだけをemptyにした定義。ordinary row/descriptor rowは不変。','任意View・assignmentでmetadataのみの消去は現在View.Modelsを定義的に保存。','消去後metadataのrow読み列は空。']),
'GeneralDictionaryHistoricalFields256':('実familyの全n、全base slot。poolは初期5変数。privateな補助snoc_otherもFull監査に含む。',[
'index≤nの任意過去lower indexもtree indexに展開される。','任意name≤4はhistoryで変化しない。','固定5変数pool。','任意name≤4のvarはこのpoolで正規化しても不変。','全tree nはvar2へ正規化される。','slot値<5は元名、それ以外は2という代表名の定義。','全slotの代表名は4以下。','全実base slotのcompile後typeは対応var代表へ正規化される。','全実base slotのtypeはunion-sideで固定poolに支持される。','全実base slotのtypeのprepareが対応var代表を返す。']),
'GeneralNominalSlotTypeMap256':('任意RawView・slotごとの新TyTerm・assignment。現在のView.Modelsのみを対象とし、将来Stepは対象外。',[
'slot.typeだけを差し替え、他のtype/row consumerはそのままにする定義。','全indexの新旧slot type値がEquivalentなら、View.Modelsはiffで保存される。','ordinary listは文字通り変わらない。','nominalsは文字通り変わらない。']),
'GeneralDictionarySlotView256':('同じ実familyの全n。expandedはlower historyのcompile、compactはslot typeのみ5代表にする。全consumer有限化ではない。',[
'当該historyでcurrent raw stateをcompileしたView。','slot typeのみ代表に差し替えたView。','全assignmentでcompact.Modelsとexpanded.Modelsは同値。','history方程式が成立するassignmentなら、compactと元raw stateのModelsは同じassignmentで同値。','実stage Modelsならcompact.Modelsも成立。','全slot type値は固定5変数poolに属する。','それでもslots数はn+5である。','実stage Modelsならinactive slot.row消去後も現在View.Models成立。','前提なしでcompact.Modelsはsolve(history)下の元raw Modelsと同値。','任意name≤4の完全なComp成分はsolve(history)で不変。','任意boundaryについて初期0..4の完全成分を固定したraw/compactモデルの存在は同値。逆方向のprivate割当は変えてよい。']),
'GeneralNominalOrderedRawPublic256':('任意raw state・有限ordered entries・private名集合hidden・公開boundary。置換による消去のみであり、新しいblockへの更新の正当化ではない。',[
'全assignmentでcompile.Modelsはsolve(entries)下のraw.Modelsと同値。','実block方程式成立の下、同じassignmentでcompile/raw Modelsが同値。','全targetがhiddenにあれば、solveは全unhidden Comp成分と全row成分のPublicAgreeを保つ。','blockがraw.ordinaryに実包含し全targetがhiddenなら、任意固定public assignmentの下でraw/compileモデル存在が同値。SafeOrder/Coherentは不要だが、有限表現や新block可解性は結論でない。'])}
out=['# Cycle256 宣言ガイド','',f'{len(decls)}個の明示的なdef/theoremを列挙する。生成・private宣言はFull監査で別途検査。','全ての定理は型に現れるデータに全称量化される。省略されたimplicit引数も含む機械出力の完全な型は [all-types.txt](all-types.txt)、主要型は [critical-types.txt](critical-types.txt)。以下の各節に共通前提を記し、さらに必要な前提は各行に記す。','']
for m,names in groups.items():
 common,descs=info[m];assert len(names)==len(descs),(m,len(names),len(descs));out += ['## '+m,'',common,'']
 for n,d in zip(names,descs):out.append(f'- `{n}`: {d}')
 out.append('')
out+=['## 全体の未完','任意source traceのside別pool閉包、全consumerのprivate非流出、active rowの処理、strict新fact、後継Step Acc、mixed-time packet、Permitted、12則とEvidenceNodeは未完。これらを仮定した結果で完成扱いしない。M1の主型性・B4 Statementの証明ではなく、そのための補助である。']
v.joinpath('declaration-guide.md').write_text('\n'.join(out)+'\n')
print('Guide checked',len(decls),'declarations',len(groups),'modules')
