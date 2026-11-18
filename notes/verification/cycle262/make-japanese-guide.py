from pathlib import Path
import re
v=Path('notes/verification/cycle262');mods=v.joinpath('modules.txt').read_text().splitlines()
scopes={
'GeneralFiniteAliasClosure262':'任意の実state・root/query自然数について、有限edgeの全cut判定 iff 既存Alias。root/queryと全edge端点を含めるため外部の孤立点も含む。列挙数は頂点list長nに対し2^n。指数的な正しさ基準であり、本番のrequest抽出には使わない。健全性・完全性の補助。',
'GeneralFiniteAliasSearch262':'任意の実state/root/queryについて、remaining全edge端点をfrontierで厳減させるsearchのcomponent所属 iff 既存Alias。追加coverage仮定なし。rootが全edgeの外でも成立。重複vertexは許し、query順序やsourceの全Step停止性は主張しない。referenceとのBool同一も証明。',
'GeneralRebaseExecutableRequests262':'任意snapshotとrootについて、computed componentで元sitesをfilterしたrequestsは既存requestsとlist全体で等しい。順序・重複も保存。同alias classのmembership一致とsnapshot候補包含を移す。sourceは任意だがこれだけでpacket validityは出ない。',
'GeneralRebaseExecutableSnapshot262':'source/Plan/ownerを固定し、任意finiteState依存root選択を許す。実行可能requestsからcoverageを導出し、settle成功・新Step停止・write数上限・実ClassEffectsを証明。historyは全assignmentで共通。roots関数を非計算的に与えた場合まで実行可能とは主張しない。',
'GeneralRebaseRootTrace262':'固定snapshot/Plan上の各中間状態で選ばれたrootを保持するTraceと実Runsを双方向対応。任意base/全assignmentについて終点Models iff始点Modelsと全history ClassEffects。certificateは停止と予算も含むがSAT/Frame/Readyは含まない。',
'GeneralRebaseAliasRegression262':'cut/searchの鎖・逆向き・孤立・非接続・非site中継と、実AllocMerge stageの任意atomsにおける二つのrequestsのlist同一。一般Alias同値定理の使用例であり一般compiler受理の証明ではない。',
'GeneralRebaseChildRequestPool262':'任意実packet/clause/childで、新しいoutput targetが実allocationのpurpose2又はpurpose5 public portに入る。visible declaration下のoutput名も有限menuに入る。名前×targetの積のmembershipを厳密化。Coveredは全raw site outputの包含であり、desired semantic conclusionではない。',
'GeneralRebaseSourceRequestPool262':'任意の実mixed-source Initialについて、一つの有限Output poolが存在し、その同じsourceからの全到達snapshot・任意query rootのrequestsを覆う。source formation、Paterson lineage、既存finite public portsから導出。Absorbedなし。旧Stepの停止性やsnapshot間のsimulatorは証明していない。',
'GeneralRebaseDynamicSource262':'任意fixed Plan/owner/poolとfiniteState依存snapshot/rootを扱う。各snapshotのraw outputsがpoolに入るcoverage前提でnew observer完了と、そのstepで実際に選んだsnapshotのClassEffectsを証明。Planの意味はここでは固定。',
'GeneralRebaseSourceObserver262':'実source Initialからpoolを先に存在構成し、その後に任意Plan/owner/observerを量化。inspectが同じstartから到達可能なsnapshotを返す前提でDynamicSourceのcoverageを解消。各snapshot間の旧Step接続、Generated rootやFrameの認証まではない。',
'GeneralRebaseDynamicTrace262':'各中間状態の実snapshot/rootをeventに保持。coverage下で一つのhistoryが全assignmentの厳密な履歴連言を表す。source_certificateはInitial由来poolを使う。Plan固定、observer生成とsource simulationは依然別義務。',
'GeneralRebasePlanTransport262':'任意二Planの宣言/catalogue/interpretation・actual binder名・default center列一致という構造Sameからschema/key/facts同一と全assignmentでのfact/body/ClassEffects同値を導く。desired effect同値を仮定しない。既存MatPlanData.Sameからも導出。',
'GeneralRebasePlanTransportExamples262':'実candidate atoms familyの任意二ordinary journalについて空bindingsから構造Sameを導出しtable/意味を輸送。Good・model存在なしでも成り立つが、任意atomsのsource到達性やpacket Evidenceは主張しない。',
'GeneralRebaseBinderShape262':'同seed/owner identity/declarationで、各non-output入力が同じpoint又は両方nonpointなら実allocatorからbinder名一致を導く。catalogue/interpretation/center一致もあればPlanTransport.Same。nonpoint→pointを自動で覆う定理ではない。',
'GeneralRebaseObservedPlan262':'実plans state rootでproposalを作る。選択rootに限った構造Compatibleによりfixed observerと関数同一、coverage時の停止と実Plan ClassEffectsを証明。valid FrameやsourceからPlanを選ぶcompilerを定義したわけではない。',
'GeneralRebasePlannedTrace262':'各実中間stateのsnapshot/root/selected Planを同じevent historyに保存。構造Compatible・coverage下の全assignmentモデル等式、source Initial由来poolのcertificate。runtimeの履歴再生を導入せず証明証人として持つ。',
'GeneralRebasePlanSemantic262':'Layoutは宣言/catalogue/interpretationだけの一致でschema/key/facts同一を保証。Compatibleは一つのassignmentでactual binder値とdefault center位置値がEquivalentである条件。その条件からbody/fact/ClassEffectsを同値輸送。全assignment無条件の同値ではない。',
'GeneralRebasePlanSemanticExamples262':'入力centerの名前を変え構造Sameを偽にしても、constant assignmentではsemantic CompatibleとBodyHolds輸送が成り立つ。入力indexの存在を明示する厳密な弱化例。実source遷移であるとは主張しない。',
'GeneralRebaseSemanticObserver262':'LayoutCompatibleで実observed tableを固定tableへ同一視。BaseCompatibleはbaseを満たすassignmentでbinder/center意味が同じという前提。Modelsが両辺でbaseを含むことを使い、全assignmentのwrite/step iffへ持ち上げる。baseからこの条件を実sourceについて導く義務は別。',
'GeneralRebaseSemanticTrace262':'semantic observerの条件を同じactual planned history全体へ帰納。selected-check run成功から訪問eventとfinalのReadyを得て、全assignment同時のモデル等式を証明。source_certificateでpoolだけはInitialから導出。source compiler/Frame/SATは未完成。',
'GeneralRebaseSelectedCheck262':'snapshot/root list/各Planについて選択root全体の実requestsだけを検査。check成功 iff全selected Ready。errorはその実selected rootと正確なClassCheck failureを持つ。pool全体・未選択rootは検査しない。',
'GeneralRebaseSelectedSettle262':'各roundで選択root全体をReady検査した後、既存nextで一つ進行。remaining長が厳減して再帰終了。成功から各prewrite stateとfinalのReady、実Runs、予算、quiescenceを得る。全state Readyを仮定せず、errorも返し得る。',
'GeneralRebaseSelectedMeaning262':'同じchecked中間state列から正確なplanned event列を取り出す。成功・構造Compatible・coverageからevent Readyと全assignmentモデル履歴を導出。source_certificateはsource Initial由来の共通poolを使う。成功自体やmodel存在を無条件には結論しない。',
'GeneralRebaseSelectedRegression262':'前cycleのunused unknown候補は旧全pool checkerで失敗するが空選択の新checkerでは成功。wrong parent Planをleafに対応させた明示的内部不整合はselected error。正しい実mergeのchecked実行は成功しても保持履歴Modelsは不充足。言語拒否の例ではない。',
'GeneralRebaseSelectedUnused262':'非空の実[focus]を選び正しいPlanを使う場合もunused unknown候補を無視できる。任意stateから0又は1writeで実六factを書いた状態へ成功。初期expanded poolからunused self-pairがremainingに残ることも証明。',
'GeneralRebaseSelectedFailure262':'run全体のerrorについて実finite rebase Runsで診断stateへ至るprefixを構成。selected errorならsteps上限、診断stateで選択されたroot、そのPlan/requestsの正確なfailureを証明。旧source Stepのpathやlanguage rejectionではない。',
'GeneralRebaseQuadraticBudget262':'任意Plan/owner/Output list長Nについてbody facts≤N、同名pair facts≤N²、合計≤N+N²。任意valid有限stateから任意observerの非自明write数はこの上限以下。list重複含む。observer実行時間・言語compiler全体の計算量ではない。',
'GeneralRebaseSelectedSafety262':'Layoutとsnapshot pool coverageがあればoutside-pool errorは起きない。全runは成功又は実到達finite stateでのselected translation errorのどちらかで、そのprefix長はN+N²以下。Ready/SAT/source受理を先に仮定しない。'
}
s='# cycle262 宣言の日本語案内\n\n全量化型は types-final.txt、全明示宣言の公理依存は complete-final.txt。帰納型・structure・private/生成宣言は Full 監査対象。以下は定義・補助・健全性/完全性の部分結果で、M1の主型性・全言語受理は未完。\n'
for i,m in enumerate(mods,1):
 assert m in scopes,m
 names=re.findall(r'^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+(\w+)',Path('lean/Yulang/'+m+'.lean').read_text(),re.M)
 s+=f'\n## {i}. {m}\n\n{scopes[m]}\n\n'+', '.join('`'+n+'`' for n in names)+'\n'
v.joinpath('declaration-guide.md').write_text(s)
print('GUIDE-PASS',len(mods))
