from pathlib import Path
import re
v=Path('notes/verification/cycle263')
summaries=[
'任意Plan二つとassignmentについて、正規化後のbody変数におけるbinder意味の一致、既定式の位置別center意味の一致、Layoutの一致から、任意outputのsuppliedBody・Effects・ClassEffectsの同値を導く。生の名前集合を正規化後支持と同一視しない。条件付き健全性・完全性の補助。',
'任意互換Plan二つ、任意assignment/output/keyについて、正規化したbody factとstable classの意味を双方向移送する。Compatibleは明示前提で、自動成立を主張しない。補助。',
'任意実headの充足とFinished中心条件から、正規化body支持のbinder意味を得る。入力と出力を区別するScoped条件と既定式の位置を保つ。出力ClassEffectsそのものを仮定しない。補助。',
'任意owner番号でfactをタグ付けし、異なるownerの表の非干渉、owner一意性、結合した意味の分解と有限予算を示す。owner選択がsource由来であることは別定理。補助。',
'任意有限owner列・output pool・代表Plan族について表の意味を定義し、一ownerへの実proposalの書込みをClassEffectsへ対応させる。代表Planと実Planの一致条件はここでは前提。K*(N+N²)は重複を含むlist長上界。補助。',
'任意source/Selection列について実requestsと実Planからproposalを作り、各選択のReadyを検査する。selectorに現れないPlanのReadyやSATまでは含まない。実行可能判定の健全性・完全性。',
'任意状態依存selector、固定代表族、LayoutCompatibleとpool coverageについてproposalがbasis内に閉じる。base下の意味Compatibleから実書込みの意味を導く。補助。',
'任意有限basisと状態依存observer、任意Except検査器について、各書込みの前と終状態で検査し、remainingの長さで再帰を止める。成功時のTrace・全中間検査・終端を証明する。新有限Stepの停止性であり旧source Stepではない。補助。',
'任意上記driverについて成功または有限prefix後のvalidation/outside errorを分類する。全状態の検査成功を仮定しない。Closedがあればoutsideを除外できる。内部診断であって言語の拒否分類ではない。補助。',
'有限owner表上で選択Readyを検査しながら実行する。Listed・Layout互換性・coverage下に、成功証明書または実中間状態の診断、書込み数上界を得る。補助。',
'任意Checked source root/Initialから実mixed Stepsで到達した状態の全登録Planは、root identity×有限宣言idに由来する有限候補内にある。current/novel/Installableだけに対象を狭めない。補助。',
'任意多owner実行の各実中間snapshotとSelectionをEventとして保持する。同じ履歴で全assignmentに意味同値を証明し、Ready・終端・予算をまとめる。base下互換性は明示前提。限定健全性・完全性。',
'任意source Initialからの到達snapshot全登録Planを選択する。有限ownerと実requests poolをsourceから導く。observerへのinspector自体は外から与え、状態間のsource Step対応は未証明。補助。',
'既存の隠れたfield shadowの実例において正規化後支持を使う。生の名前の包含へ強めない。非空の実Planについてbodyと既定式の意味を比較する回帰。補助。',
'実登録Planのseed/registry/構成子/解釈/visible/Finishedの出自をsource経路から導く。同じownerの二経路でLayout一致。意味compatibleにはModelsまたは後続head-only証明が別途必要。補助。',
'実mixed source経路のsiteはroot inputまたは既存Planの出力に由来する。producer invocation identityが利用側より小さいという厳密上界を示す。古いsource反復の停止性は含まない。補助。',
'任意同一Initialからの二source経路、同一ownerの登録Plan二つ、全登録producerのheadを満たすassignmentについて、invocation identity帰納法で意味center一致とNormalizedBody.Compatibleを導く。head-only前提は全producerに及び、選択された二Planだけではない。出力ClassEffects仮定なし。補助。',
'任意有限owners/poolにPlan非依存basisを作る。各owner/outputにbody index0とoutput対を予約する。全実PlanのbodySchema長≤1から実proposalを被覆。予約が未使用で残ってもよい。補助。',
'Plan非依存basis上の実行器。Listedと実requests coverageだけで閉包と成功または実選択診断を示す。外部代表Plan、Layout、Models、全状態Readyを要求しない。新Stepの有限性の補助。',
'任意source Initialで有限owners/poolを導き、任意個別にsource到達するinspectorへ適用。外部代表Plan/Layoutなしの実行結果と予算を証明する。inspectorの連続snapshotがsource Stepで結ばれるとは主張しない。補助。',
'実AllocationMergeの二つの異なるownerを常に非空で選択する例。実requestsを二回書き、終端・Ready・全assignmentで二つの実ClassEffectsとの正確な同値を示す。補助。',
'Plan非依存basisの各factを固定代表Planで解釈する。任意base下でCompatibleがあれば一回の実書込みのModels iff旧Modelsと実ClassEffects。全basisのLayout被覆は不要。未使用予約はpresentにない限り意味義務を生じない。限定健全性・完全性。',
'任意成功checked runについて、実選択の一つの履歴を全assignmentに共通して返し、全書込み前Ready・終状態Ready・終端・予算・実ClassEffects同値を証明。意味互換性はbase下の明示条件。限定健全性・完全性。',
'実二ownerを非空選択し、poolには未使用Outputも加える。二書込みで終端・Readyになるが予約body keyはremainingに残る。終端は全予約消費とは違うことを実例で示す。補助。',
'任意Checked/Initialから到達する登録Plan族が非空なら、sourceに実在する代表Planをownerごとに非計算的に選ぶ。同owner出自、Layout、全到達heads充足下の互換性を証明。将来Planを実行時に列挙するアルゴリズムではない。補助。',
'実CompoundStep238のsource installationにより、将来登録Plan族が非空になる例を示す。任意Planを仮置きしただけの例ではない。全到達head充足を自動導出する例ではない。補助。',
'任意Checked source/Initialについてowners,pool,holdsをbaseとinspectorより先に選ぶ。個別source到達inspectorの任意成功runには、base∧全到達head充足をContextとして、全assignmentに共通の履歴・Ready・終端・予算・実ClassEffectsとの同値がある。未来全体に登録Planがない場合も空選択で処理する。Contextの存在・SAT・自動成立は未証明。限定健全性・完全性。'
]
summaries += ['任意非空のsource登録族で、選んだ代表Planそのものを含む実snapshotをownerごとに選ぶ。有限ownersのうち出現するownerの代表snapshot全登録headと、実observed snapshot全登録headだけで互換性を導く。全alternate source futuresのhead充足は不要。どちらのsnapshotでもproducer全体のheadsは明示前提。補助。', '任意Checked/Initialと非空のsource登録族に対し、finite owners/pool/holdsをbase・inspectorより先に固定する。各snapshotがsource到達するinspectorの成功runで、base∧有限代表snapshotのheads∧inspector像のheadsをContextにすれば、Ready・終端・予算と実ClassEffects同値が得られる。Contextはinspectorに依存するがrunの帰結を前提に含まない。全futureHeadsより弱い。空登録族は既存SourceMeaningで別処理。限定健全性・完全性。']
summaries += ['任意有限basisについて全Stateをskip/keepで明示列挙し、全状態の包含とリスト長2^basis.lengthを証明する。重複basisでは列挙結果も重複し、distinct状態数の等号ではない。任意inspector像上の全Heads条件を有限list上の量化へ同値変形できる。指数的列挙は効率的実行や意味Heads判定可能性の主張ではない。補助。']
summaries += ['任意source Reachableと実current Local selectedから、登録済Plan所属を仮定せず実Plan Frameと順序付きchildrenを得る。そのPlanの実requests checkerを場合分けし、内部診断または正確なregistry/snapshot/Plan/root/key/childrenを持つEffectを返す。成功を全候補に仮定しない。候補発見の実行可能性・novelty・Installable・共同InstallationModelsは未証明。source対応の補助。']
mods=(v/'modules.txt').read_text().splitlines();assert len(mods)==len(summaries)
out=['# cycle263 宣言の日本語案内\n','全量化型は `types-final.txt`、明示宣言は `complete-final.txt`、生成/private定数を含む公理依存は `full-final.txt`。以下は補助と条件付き健全性・完全性で、M1主型性・全言語受理・source Step全体対応は未完。\n']
for i,(m,s) in enumerate(zip(mods,summaries),1):
 names=re.findall(r'^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+(\w+)',Path('lean/Yulang/'+m+'.lean').read_text(),re.M)
 out += [f'## {i}. {m}\n',s+'\n',', '.join('`'+n+'`' for n in names)+'\n']
(v/'declaration-guide.md').write_text('\n'.join(out))
