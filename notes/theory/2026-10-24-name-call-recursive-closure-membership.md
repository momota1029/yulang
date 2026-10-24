# Name Call を持つ一つの再帰 root と生成される内側閉包の同時導入

独立査読後の注記: NF/NG、NR1/NR2 の同時構成を、記載した monomorphic instance と元の独立 kernel/full background/formation 前提の下で受理。査読対象 `f0a3efe6995a1d4070a36ef5aedea173752051f6ec5a831dd9568bdbfc9b2ef3`。PF1/PF2 は native local formation 部分を元の independent license inputs の下で供給する。全 source/publication/native 対応は未完。この注記だけを primary が査読後に追加した。以下の独立査読前・待ち表記は producer freeze の履歴。[outcome](../../tasks/agent-loop/sprints/name-recursion-profile-20261024-outcome.md)を参照。

NAME-RECURSION-PROFILE-20261024/r1。Author `/root/astra_scoped_join`。Claim class: selected original constructor interpretation における独立 kernel/formation 前提付き構成的証明。独立査読前。実装権限なし。

Contract SHA-256 `bfb886777e4ef069af70a1f809e6b11baac175eb136285f2e211efbfc2e34c5e`。Baseline `18222ed99cc1ec963e12198d03a7d6e05257a30b`。唯一のwrite leaseは本稿。

## 1. 対象と独立入力

対象は元のsourceである。

```text
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first=h x, next=f {a=y}}
  in f
in top
```

A=Record(a:Int)、y:Int の一つのmonomorphic instanceを構成する。hは実際の外側entry Returnが供給した同じcallable/rootで、genuine complete H* certificateを持つ。H*のwhole inletは元instanceのComp(empty,A)、complete resultの元projectionを保持する。hの結果endpointをBと書くが、Bはhの既存complete result projectionであり、都合のよいpure envelopeではない。h Callのpending/response/futureは全てH*のものを使う。

以下の前提は、選択済み同時immutable introduction §§2–3、Strict definition §§2–3、WR1–WR3と同一の独立入力である。

* 元raw Lambda/Name/Delay/Record/Return/Bind/receipt/rebind/return transitionとroot allocator。原capture/scope/incidence/authorityのimmediate guardsと合法restriction/transition laws。
* 全independently admitted context/history、whole carrier、response/raw Resume/FutureUseのdomain。tested membership、candidate S、Qから定義しない。
* 全background proof fieldsは選択済みpositive V/W/T/Car operatorのdeclared-value解釈である。別foreign証明の無条件embeddingは仮定しない。
* I_A、I_Intは元Value-entry whole-carrier interfacesでdesignated Return endpointsがA、Int。許されるeffect/pending/divergence/futureをそのまま保つ。元pure Record(a:y) carrierのI_Aへのwhole checking、pure Name x carrierのH* inletへのcheckingは同じcomplete pure interfaceの元inert/Return introductionで行う。このidentity-compatible monomorphic instanceを選ぶ。異なる固定inlet/追加boundへは別のcheckingが必要。
* 各実local introductionの元profile/permission formation証拠、primitive/independent arm laws。原guardをtrueと再定義しない。native形成の別laneはこの前提のsupplierであり、moving稿を本証明の依存にはしない。実在するW/Zの独立lawを除去しない。

これらは「fがsafe」「gがsafe」「全composite C0」の前提を含まない。特にf ordinary membershipとcompleted own-worldは結論である。guardが偽のassignmentがこの定理を満たすとは主張しない。元A/B、全source、F1/FK1、全raw利用、主型性、停止性の量化は本局所instanceへ置換しない。

## 2. 実root registryとcomplete descriptor graph

実let-rec登録で一つのroot r_fを確保し、元resolved recursive referenceをそのrootへ結ぶ。

```text
v_f = Closure(ValueEntry(I_A,x),
              Return(Lambda_y(body)), env[h↦r_h,f↦r_f])
body = Bind(Call(Name h,Delay(Name x)), u,
         Bind(Call(Name f,Delay(Record(a:Name y))), v,
           Return(Record(first:u,next:v))))
```

これはsourceのordered Record field evaluationの展開である。Recordのfield結果がlatentであっても再Forceしない。上のBindのu,vは元field-result slotsの表記であり、新しいsource binderやexecution boundaryではない。

各f entryの**実際の**Return/rebind event κで得たx=(a,r_a)に対し、内側Lambda実行が新root r_gκを作る。

```text
v_gκ = Closure(ValueEntry(I_Int,y), body,
               env[h↦r_h,f↦r_f,x↦(a,r_a)])
```

κはsource formal xのdynamic event parameterであり、xの古いbindingの変更ではない。fresh allocatorの元一意性だけを使う。r_gκ≠r_f、別allocationは別root。gを返してもf referenceは元r_fのまま。各gのxはそのcreation時の実xであり、後続f invocationのxに書き換えない。

形成前に元source-owned portsで有限な相互参照descriptorを作る。

```text
R_h = ReadInvoke(H*,D_h,IF_h)
R_fcall = ReadInvoke(F,D_f,IF_fcall)
Q = Record(first:B,next:G)
R_body = ordered Bind(R_h,u,
             Bind(R_fcall,v,PureReturn(Record(first:u,next:v):Q)))
G = Strict(I_Int,y:Int,R_body,IF_g)
F = Strict(I_A,x:A,PureReturn(G),IF_f)
```

BへのprojectionはH*のactual full result portの元もの。R_hをPureReturn(B)に置換しない。R_fcallのcomplete resultはGだが、entry effectsはF/ReadInvokeに残る。F bodyのclosure creationだけがpureであり、F invocation全体はpureとはいえない。G descriptorは任意の合法x:A捕捉を許し、特定gのsuccessful traceだけをその意味にしない。source reference cyclesは既存nodesを共有し、runtime rootsを静的nodeと同一視しない。

## 3. candidateと穴の正確な範囲

Phiはselected simultaneous immutable-root interpretationの同じpositive operator。Strict、ReadInvoke、Recordとordered Bindのselected clausesを用いる。D、ActualAdm、raw transitions、immediate guardsは固定し、Sはそれらに現れない。

Hを次のvalue tuplesだけのfamilyとする。

1. (F,v_f,r_f,e) と元registration/capture incidence。
2. 各実Lambda_y allocationの (G,v_gκ,r_gκ,e)、その同じh/f/x projection、元scope/witness、合法future restriction。

各allocationを指定するindexはraw constructor eventと、その時のx:Aの独立ground/Record field evidenceを含む。AのfieldはIntなので、その証拠は新しいF/G membershipを使わない。world validityはHの条件に入れず、元registry/alias/immediate guardsとbackgroundのworld fieldsから後で組み立てる。future rootsを現在のregistryへ先置きしない。Hは全合法allocation/eventをindexとする証明familyであり、各eventのworldにはそこで実際に存在するrootsだけを入れる。

Hにworld/carrier/observation/continuation/guard/authorityを入れない。hのmembershipはHの穴ではなく独立importである。hをf/gへ置換せず、H*のdomainも変更しない。

B_H=νY.(Phi(Y) with only value summand H)。SはB_Hの全V/W/T/Carと、上記実f/g tuples、その実worlds、source invocation/Call/Record/Delayの全有限phase tuplesと元suspended suffix familiesの和。追加したRecord valuesは同じactual field-result tuplesから組み立てる。typed carrier Returnをまだ得ていないphaseへ値を入れない。

これはmembership定義をsource imageへ変更する操作ではない。membershipは独立Phiのνのまま、Sはpostfixednessの証人である。Sの全finite developmentsは一つのphase-recursive proof functionで扱い、各prefixごとに互換性のない証明を選ばない。Hは無限familyでもよい。静的descriptorは有限共有graphであり、全未来allocationの数を有限と主張しない。

## 4. Fの直接一段realization NF

任意の元independent d∈D_F、任意のretained actual provider decompositionを固定する。v_fのconstructor inversionによりactual entryはValueEntry(I_A)。dの同じcarrier/receipt/context evidenceをこの等式で読むとActualAdmを得る。candidate f membershipからadmissionを引き出さない。

各actual finite developmentを次で証明する。

| phase | P_F[S]の証拠 |
|---|---|
| zero/receipt前 | actual f registry/capture、S内の同じh/f bindings、元immediate guards、未実行entry/body/return interfaces |
| receipt/Force | 元transitionと同じcarrier。I_Aの全Car/Force evidenceをB_HからSへ運ぶ |
| Force Request/admin/divergence prefix | current world、raw handle、response interface、未完了 `rebind x; create g; return` のみを残す |
| Force Return | 同じreturned a/root/current world。W/ValueBindによりfresh x@κ。ground A evidenceは同じReturn projection |
| body Lambda/Return | 実Lambda constructorでv_gκ/rootを作る。capturesは同じa,h,f。G tupleはH⊆S.V。よってPureReturn(G)のvalue/world clausesを満たす |
| invocation Return/future | 元return edgeと同じg provider、future eventのS.V(G,v_gκ,r_gκ,e')。その時点のguardを使う |

raw source derivationはLambda/Return/Bindの元構成子であり、desired typingから作らない。pending suffixの証拠は任意のadmitted response後に上表を再適用する関数である。ここにνPhiのf eliminatorは一度もない。Gのfuture obligationはS.Vというpositive edgeに残し、その一段証明を次節で同時に行う。これでNF: 全actual f observations→P_F[S]を得る。

## 5. Gの一段realization NGと再帰Name Call

任意のgκと全d∈D_Gを固定する。admission/entry/pending casesはNFと同じStrict constructor proofをI_Intに適用する。Returnの時だけfresh y@λ:Intを作る。captured x@κは保持し、そのcertificateを新eventへrestrictする。

### 5.1 first field: actual h x

Name hは同じr_hを読む。Delay(Name x)は同じcaptured x/rootを保持する。W/D、identity inlet checking、R/Eを**genuine imported h certificate**に適用する。GC1–GC3のphase mapsでR_hの全prefix/pending/consumer/result/future証拠を得る。B_H内のh証拠を扱う場合、非穴Function caseをunfoldしてP_H*[B_H]を得てmonotonicityでP_H*[S]へ運ぶ。ordinary f membershipをその中に輸入しない。

hがpendingなら残るsuffixは `bind first; Call f {a=y}; build Record; return`。hが発散すればこのsuffixを実行せず全finite prefixを保持する。hがReturnした場合だけ、その実u/provider/rootをfirst slotへ結ぶ。uのlatent interfaceは保存するが実行しない。

### 5.2 next field: actual f {a=y}

h Return後のactual current worldでName fは元r_fを読む。whole argumentはDelay(Record(a:Name y))。inert formationは元Delay/reify law、全designated ForceはName y→Record→Returnの元有限pure constructorsで証明する。fieldはそのactual y:Int。元I_Aとのidentity-compatible checkingでsame carrierのadmissionを得る。これを純粋なName argumentに偽装しない。

calleeがNameであるためReadInvokeのselected clauseを使用できる。ただしGC3のcompleted-f operand premiseを使って循環させない。代わりに:

* pre-callee prefixのbinding obligationはS.V(F,v_f,r_f,e)として保持する。
* callee Returnは実Name inversion、Delay/challengeは上記実constructor。
* actual receipt/admissionとreceiver全phaseは**NFの直接関数**をこの同じchallengeに適用してP_F[S]を得る。
* ReadInvoke-Descのstaged introductionにそれらを入れ、R_fcallのS.T証拠を得る。

NFはg∈S.Vだけを戻すので、ここでNGやrecursive fのordinary certificateを再帰呼出ししていない。actual f entryがRecord(a:y)をForceしReturnした時、fresh x@κ'はそのrecordであり、そこで作られるv_gκ'のcapture xはそれ。r_fは不変。Callが返すのは新r_gκ'でありr_fではない。

### 5.3 Recordと全suffix

next CallのReturn後、同じcurrent worldでu:Bとv_gκ':Gを元field clausesに渡し、actual Record(first:u,next:v_gκ'):Qを得る。背景uのfuture certificateとgのS.Vを同じtupleに保持する。二つのfieldに別world/別witnessを選ばない。元Record/ReturnでR_bodyを満たし、Strictのinvocation returnへ運ぶ。

両Callの全requestでは元Bind equationで未完了suffixだけを付加する。完了したh Callをfのresumeで再実行しない。どのphaseもcurrent worldと元raw handleを使う。各finite derivation長による構造帰納がzero/admin/何回でもresponse/resumeを扱い、future g invocationは同じNG proof familyへpositive edgeとして戻る。これでNGを得る。

## 6. 四成分のpostfixednessと結論

**NR1。** 上記独立入力の下でS⊆Phi(S)。

証明。H value casesはNF/NG。全capturesは同じrootのS.V/Carと独立guard。追加Record valuesは§5.3、ground A/Intは元constructorでPhiVを満たす。追加worldは実registry/scope/alias guard、全installed bindingのS.V/CarでPhiWを満たす。entry/formal/result bindingsはactual typed Return後だけであり、own-worldを先取りしない。追加observationはNF/NGとReadInvoke/Bindの各phaseでPhiTを満たす。追加pure carriersは§5.2とNameDelayでPhiCarを満たす。外部carrierはB_H全成分を保持する。B_Hのnon-holeケースはunfoldとmonotonicity、HケースはNF/NGで置換するselected relative-coinduction lemma。全independent armはその元lawを同じarm injectionで適用し、source branchに偽装しない。これが全四成分を尽くす。□

**NR2（actual original membership）。** NR1とν最大性からS⊆νPhi。従って同じactual f/rootのValueMem_F、全実gκ/rootのValueMem_G、actual immutable worlds、全pending/complete/future observationsを同時に得る。全independent carrier/challenge domainは元のまま。ここで初めてordinary fのR/E eliminationを使ってよい。

これはselected positive interpretationでのmonomorphic recursive constructor theoremである。原two-closure proofの固定二rootを、独立allocation grammarで指定したg familyへ拡張したrelative-coinduction applicationであり、PhiやDを変えない。有限個のgしか存在しないという仮定もない。

## 7. HC-REC/HISTORYへの実適用

元sourceの任意の合法f invocationで、typed I_A carrierがReturnすればNR2がそのactual Return/current worldを供給する。VB1を同じeventに適用してfresh x@κを構成でき、作られるgκはそのxを保持する。そのg invocationでh xを評価する時、HC1/GC3へ渡すA certificateはこのactual captured xのものである。native lower boundや候補S.Vをcompleted certificateへ読み替える旧gapは、このconstructor instanceでは解消した。

さらにbodyのrecursive `f {a=y}`について、NR2/§5.2が実Record argumentのtyped Force Return、actual f entry/rebind、実fresh g Returnを与える。これが次世代gの同じHC/VB1 supplierになる。hがReturnしないbranchではnext Callを発明しない。発散は全prefixとして残る。

元topは通常のValue-entryでhを受け取り、local let-rec f登録とName f Returnを行う。genuine H*のactual Returnがあった後のこのlocal suffixにNR2を適用できる。topの全外部complete descriptorとのcomparison、Generalize/publication、全source/native対応をこのlocal suffixから自動で宣言しない。

残余は元kernel/primitive/guardとlocal native formationの実supplier、independent armsの各law、foreign embedding、publication/intrusion/native receiving対応、全source coverage/principality/termination。今回は一般raw sourceの受理や旧computed-Lambda calleeへReadInvokeを拡張していない。

## 8. Handoff / checks / stop

Contractと20 pinned inputsのactual SHA-256を照合し全一致。manifestは上記contractのFrozen direct inputs。直接使用したGC1–GC4のauthorは`/root/astra_corrected_machine`、WR1–WR3とselected definitionsのauthorはprimary、旧VB1は本worker（現在はprimaryがreviewed statusを統合したfrozen入力）。本稿は単著、coauthor/descendantsなし。moving native-profile稿は読まず依存にしない。

Reuse: selected positive Phi/declared-hole lift、Strict、ReadInvoke、GC/WR、W/D/R/E、元source Record/Return/Bind。Reject: candidate fへのcompleted elimination、old x/world substitution、body purityからinvocation purity、r_fとreturned gの同一視。

Mutual TODO NR-PROFILE: primaryのnative-local-profile ownerが元local Lambda/Name/Call/Record/Returnのformation証拠を供給する。local lawのf recursive caseはGC3 completed operandを仮定せず§5.2のNF関数を使う。falsifierはlicense schemaをlicense evidenceとすること、imported H* policyをlocal reseedすること。

NR-ARM/HOST: original independent arm/foreign kernel ownerが固定law/embeddingを供給する。falsifierはsource executionのないZをsource branchで証明すること。NR-LIFECYCLE: original publication/native ownerがこの実memberから元Generalize/use/replayへ対応を構成する。falsifierはfresh g rootをf rootへ潰すこと。

Three stages: actual registry/descriptors、NF/NG、postfixedness/application。190秒上限、full reserved charge、requested Astra/medium、observed model/effort/elapsed UNKNOWN。static reads/hash/文書検査のみ。tests/build/probes/compiler/implementation/network/Git/scratch/descendantsゼロ。本稿のみ新規write。独立査読とprimary intake待ち、parent whole goal OPEN。

r1 frozen。全write終了、STOPPED。hashはfinal handoffに返す。
