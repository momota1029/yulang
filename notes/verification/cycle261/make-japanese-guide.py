from pathlib import Path
import re
v=Path('notes/verification/cycle261');mods=v.joinpath('modules.txt').read_text().splitlines()
scopes={
'SourceSnapshot':'任意固定source snapshotの全site outputsを実行可能な有限candidate列にする。任意rootの実alias requestsを仮定なしで包含し、その固定snapshot上の動的root選択でClosed/完了/実ClassEffects書込みを示す。sourceやPlanは固定、一般trace共通pool・Frame生成・言語停止性ではない。',
'CandidateValidation':'固定有限candidate全体のmissing/unknown検査とcovered schedulerを接続。成功なら全traceのReadyと正確なModels連言。未使用candidateのunknownも内部errorになり得るため言語拒否ではない。',
'StableMergeFinish':'具体fixtureでは任意観測・任意finiteStateから唯一終端doneへsettle/finishが成功する。ただし履歴保持doneは不充足。翻訳/制約生成成功と充足性/プログラム受理を区別する閉じた回帰。',
'BodyTable':'任意固定Planの実lookup/bodySchemaを保持する要求表。missingは空schemaかつunknown。全key成立 iff全要求のBodyHolds。name/target別住所と位置非依存bodyの意味を区別する。',
'ClassTable':'固定要求列についてbody義務と全同名pairのEqualOutputsを合成。全facts iff ClassEffects、終点は任意baseとの連言。初期kind2 equality住所は固定schema内indexであり、可変表の安定住所ではない。',
'ClassCheck':'固定要求列のmissing bodyとunknown翻訳を別errorで検査する。check成功 iff Ready。意味的充足性やプログラム受理は判定しない。',
'ClassRun':'固定要求表のrunはReady時にchecked writeへ一致。初回進行にはfacts非空が必要。固定表のsettle/AccはReadyなしでも成立し、モデル存在を意味しない。',
'MergeRequests':'AllocMerge実alias classの全requests membershipが2要求列と一致、両targetは異なる。実lookup/bodySchema/Ready/ClassEffectsまで接続するが、旧V7と現行versionedのtrace到達は別。',
'MergeMeaning':'実二要求のClassEffectsは両target Int。既存parent履歴はa=Int,b=Variant Intを要求する。履歴とEqualOutputsまたは両bodyは不整合。raw-only uniformは新Effectsを満たす。',
'MergeRun':'具体6factの初回成功・以後停止。履歴保持終点は不充足、Good下raw-only終点は充足。旧V7実到達終点・rejectedへの接続は現行versioned到達証明ではない。',
'MergeFrame':'GoodとSupportedの具体atoms-stageから現行versioned Frameを構成。capture/report空、ordinary、fresh等を実fixtureで解消する。任意sourceのFrame生成ではない。',
'MergePacket':'具体stageのraw Modelsと実Effectsから現行packet Holds、Good＋Supportedからleaf Evidence。raw-only uniformのEvidenceは履歴モデルを意味しない。実children/head空・emitted Intを使用する。',
'MergeHistory':'当該stage familyの既存履歴を初期snapshot Models＋固定2出力制約へ全assignmentで同値圧縮。任意の増大journal有限化ではない。新全subsetのModels同値と終点不充足を保持。',
'PairKeys':'ownerと二つの(name,target)をkind3に注入符号化し位置非依存のEqualOutputs住所を作る。全key iff同名pair型同値、subset包含・並べ替えに対するmembership不変。旧kind2と混ぜない。',
'StableBody':'固定Planについて全requestを量化したkey意味。住所一意性により観測subsetのbody義務と厳密一致。subset変更に意味は依存しないが、Plan変更は別の橋が必要。',
'StableClass':'安定body＋pair表。全facts iff観測要求列のEffects。有限candidateに要求が含まれる前提で、書込み後Models iff書込み前Models＋実ClassEffects。',
'CandidateDriver':'任意state依存request選択について全要求が固定候補列に入るCoveredを明示。Closed・settle完了・成功Step上限とモデル変化を証明。Ready・充足性・source候補producerを仮定から自動生成しない。',
'CandidateTrace':'成功Stepで実際に選んだrequest列を記録するTraceとRunsを長さ保存で対応。同じ記録が全assignmentに対し終点Models iff開始Models＋全履歴Effectsを満たす。監査証人でruntime履歴storageではない。',
'StableMerge':'新kind3でも6factの終点意味は旧表の履歴保持終点と同一assignmentで同値。任意atoms-stageの実requests coverageを実証。固定Plan解釈であり動的Planとの橋は次節。',
'MergeObservation':'この具体familyのbodyは全atoms-stageでIntなので、固定Plan表のEffectsと実観測stageの実Plan ClassEffectsが一致。Good/Supported/raw Modelsを明示して実packetとleaf Evidenceへ接続。一般Plan変更の不変性ではない。',
'StableMergeDriver':'任意state→atoms観測でも実requestsのmembershipが同じため、実proposalのwriteは固定6facts書込みへ一致。noncomputable実観測runと実行可能固定表runが関数等号。初回一歩・以後停止・Runs≤1は具体family限定。'
}
s='# cycle261 宣言の日本語案内\n\n正確な引数・全量化型は alltypes-final.txt、公理依存は complete-final.txt。全source停止性・有限候補producer・SAT判定は未証明。\n';count=0
for i,m in enumerate(mods,1):
 key=m.removeprefix('GeneralRebase').removesuffix('261');assert key in scopes
 names=re.findall(r'^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+(\w+)',Path('lean/Yulang/'+m+'.lean').read_text(),re.M);count+=len(names)
 s+=f'\n## {i}. {m}\n\n{scopes[key]}\n\n'+', '.join('`'+n+'`' for n in names)+'\n'
 if key=='CandidateTrace':s+='\n`Trace` 帰納型とその生成宣言も Full 監査対象。\n'
s+='\n## CandidateBoundaryProbe\n\n実fixture Planに実requestsに属さない未定義name1を内部candidateとして加える。空observerならschedulerは即完了するがlayout検査はmissing errorを返す。未使用candidate全体検査の保守性を示し、source到達反例や言語拒否とは主張しない。\n\n`unused_missing`, `empty_selection_covered`, `empty_settles`, `unused_layout_error`\n'
v.joinpath('declaration-guide.md').write_text(s)
print('GUIDE-PASS',len(mods),count)
