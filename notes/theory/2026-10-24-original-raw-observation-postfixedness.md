# raw observation の単一族、返却相関と original postfixedness

Assignment **ORIGINAL-RAW-POSTFIXED-20261024/r1**。著者 `/root/astra_corrected_machine`、子なし。要求 Astra/medium、観測 model/effort/duration UNKNOWN。契約 SHA-256 `26480f08270d3a98d05014870f6fd1690965272b2c1a88ccdfaf0ff08478a425`、基準は primary 指定 `e698efa92f35a71a3c3cc6e6880aedc8ffa745d0`。

本稿は raw derivation による部分構成である。結論は raw source の返却相関、全 prefix を持つ一つの証明族、candidate-relative carrier/world の構成、そして full original postfixedness の未導出 case の特定である。完全 J_rec/J_pub、元の required-coverage 反例、production authority は結論しない。

独立査読後の注記: RP1–RP5、RP6a、明記した guard/world 前提の下の RP6b は限定範囲で受理された。r1 の「q_fy の RP-FULL だけで全四 sort が閉じる」という十分性には MAJOR 指摘があった。primary が producer の停止後に §6・§7 を修正し、全 closure/world/carrier/field の既存条件を残した。新たな全体閉包は主張しない。凍結版・修正範囲は [sprint outcome](../../tasks/agent-loop/sprints/original-raw-postfixed-20261024-outcome.md) に記録する。

## 1. 固定した source と二つの意味

```
let rec f = lambda x.
  let g = lambda y. (lambda z.y)(f y)
  in {a=succ(g 0), b=g true}
in f
```

U=Int∨Bool、V={a:Int,b:Bool}。f は同じ r_f、ある f invocation h で生成された g は同じ r_g(h)。wrapper はその g invocation k で実際に束縛された y を捕捉する r_w(h,k)。元の registry R1 がこの参照と raw plan を与える。

今回 g の actual Parameter endpoint と stored inlet は **固定 U** とする。二 use で Parameter の assignment を Int/Bool に取り替えない。checked narrow views を後で構成する場合には、同じ actual g の原 U carrier inletへ CA1 によって入る。generalized A と WalkActive を先取りしない。

二つの集合を厳密に分ける。

- `RawSrc` は actual source constructor の finite raw derivation、原 administrative/pending/response/future rules と同じ raw handlesを含む。
- `Obs_orig` は original complete operation が量化する全 observation。independently declared alternative があれば、その全 original witness を含む。

raw source derivation を持つことは前者への所属である。前者を後者の定義としない。以下の raw 相関定理はこの区別を維持する。

## 2. 型安全性を前提にしない raw result 帰納

raw evaluation を、有限の constructor/transition 導出木 π として記録する。各 Call の記録は actual callee/root、carrier、receipt、designated Force、actual Return/rebind、body、result consumer、invocation returnを順に持つ。未完了 prefixには未完了 code/suffixをそのまま残す。response/raw Resumeは元の continuationへ実 response/current worldを入れる。

長さ `|π|` は primitive/raw transition と接続規則の有限個数である。completed child derivationは親の真の部分木なので、長さが厳密に小さい。saved continuationの再利用を許し、各再利用の **その回の** 有限導出を数える。history の総経過時間や仮想 stepを induction indexにしない。

### 補題 RP1: wrapper の結果

actual wrapper `lambda z.y` の raw invocationが正常終了したとする。その結果は捕捉時の actual y と同じ raw value/rootであり、result transportの元の incidenceだけを付ける。carrierを無視したことにはならない。

証明。Value-entry inversionにより、carrierのdesignated Forceがactual値 zを返した後にだけbodyへ入る。bodyは保存済み参照 y のName/Returnであり、そのraw lookupは同じrootを返す。invocation-returnは値を置換しない。Forceが未完了ならbody Returnを導く規則はない。request時には z-rebind/Name-y/returnのsuffixがraw continuationに残る。どのresponse/resumeを経ても、正常終了導出の最後のbody節について同じinversionが成立する。□

### 補題 RP2: g の結果相関

actual gのcarrierがactual yを返し、そのg invocationが正常終了する任意の finite RawSrc derivation πについて、結果はその同じ y/rootである。途中の `f y` の実行と全phaseはπの中に残る。

証明。πのCall/Bind節を反転すると、g entryでyを束縛し、その後にwrapperを作り、wrapperのwhole argumentとして `f y` を渡す。wrapperのcompleted invocationはπの真の部分導出。RP1を適用すると結果はそのactual yである。fのcompleted subderivationがある場合は、そのactual resultをzに束縛してから結果を捨てる。fが途中ならgもその段階で未完了であり、正常終了の結論はない。receipt/Forceを消去するraw ruleは使っていない。これはfのValueMemを使わない純粋なconstructor反転である。□

RP2から、yの同じtupleにoriginal hereditary ValueMem_Aが与えられた場合、その結果をAとして扱うのに別のparameter assignmentは不要である。ただしfull descriptorの相関は§7の別問題である。

### 補題 RP3: f の record fields

fのraw bodyがrecordを返す場合、field aは元の `succ(g 0)` occurrence、field bは元の `g true` occurrenceの結果またはその元のretained field planに由来する。strictなfield valueの完了導出があるなら、aの値はInt、bの値はBoolである。retained/latent fieldはその計画と将来使用契約を保持する。

証明。record constructorのactual field tupleを反転する。各strict fieldのchild derivationは有限親導出より小さい。g 0のcompleted childへRP2を適用すると同じ0、g trueには同じtrueを得る。authentic succのoriginal Int→Int primitive lawからa:Int、literal lawからb:Bool。両fieldは同じactual current worldと元のfield incidenceを持つ。retained fieldの場合、record formationはそのbodyを実行しない。したがってこの場合は型付きretained plan/将来demandに同じ帰納を適用し、その瞬間の値型成立をrecord formationだけから主張しない。□

ここで「fは絶対にReturnしない」という補題は採用しない。strict recordの特定実現ならg0内のより小さいf完了への無限降下を導けるが、original Recordはlatent fieldをforceしない。actual field-consumptionの同定なしにその降下を全original sourceへ拡張できない。RP1–RP3はどちらのfield phaseも残す。

### 補題 RP4: prefix と response の保存

元の raw prefix の中断点には、次に行うsource instructionと未完了suffixが一意に残る。entry pendingではparameterは未束縛、`f y` pendingではfの未完了suffixの外にwrapperのz-rebind/Return-yとg-returnが残る。完了したreceiptをResumeで追加しない。

証明。有限raw導出長への同時帰納。Name/Delay/Lambdaのstepはそのconstructor equation、Callのentryはreceiptの後にForceを置く。BindのRequest規則は同じraw handleの後へ未完了suffixをappendし、Returnだけがactual current worldでsuffixを開始する。Response/Resumeは保存bodyのholeにそのresponseを代入する。各caseで既完了phaseは接頭部として保持されるが再実行codeには入らない。FutureUseはその時点のactual value/immutable referencesから新しいuse derivationを開始し、古いworld snapshotを復元しない。□

## 3. 全深さを一つにした証明族

有限深さごとに別のf/worldを選ばない。元のallocation/reference規則を一つ固定し、source occurrenceとactual invocation履歴で全closureを索引する。同じ履歴へのrestrictionはその同じrootを保持する。

まず declared value holes Hを、次の**raw constructor tuples**で定める。

1. actual r_fとfixed F_U descriptorのtuple。
2. actual f bodyが生成する各r_g(h)とfixed actual U-entry descriptorのtuple。
3. actual g entryが束縛したground-U値yをcaptureするr_w(h,k)とwrapper descriptorのtuple。

Hのwrapper行にはその同じyのordinary ground-U constructor evidenceを付ける。UはInt∨Boolなので、このground証拠はFunction membershipやB_Hを参照しない。Hにworld、carrier、continuation、authority、guardの穴はない。tupleのevent範囲は元のindependently compatible eventsであり、検証に成功したeventだけへ狭めない。actual source allocation以外の恣意的なclosureをHに入れない。

Hをfだけでなく生成されたg/wrapperにも広げるのは、実contextにlocal gが入るとき、そのbindingを完成済みmembershipと偽らずに扱うためである。これは元のPhiを変更する操作ではない。証明中の仮定を最後に**全件**置換するrelative constructionである。

`Phi_H(Y).V=Phi(Y).V∪H`、他の三成分はPhi(Y)のままとし、`B_H=νY.Phi_H(Y)`を置く。既存のrelative-lift証明はHの要素数を使わない。Hが履歴により無限でも、unfoldした各value行がholeかnon-holeかで場合分けできる。

**補題 RP5: 任意のexact Hに対するrelative lift。** `B_H⊆S` と `H⊆Phi(S).V` があれば `B_H⊆Phi(S)`。

証明。B_Hを一回unfoldする。non-hole VとW/T/CarはPhi(B_H)の同じfull tuple証拠を持つので、positivityによりPhi(S)へ運ぶ。hole Vだけは指定されたH replacementを使う。worldやcarrierをholeとする場合分けは存在しない。scope・raw handle・provider・current worldはすべて恒等に運ぶ。□

### S の定義

一つのraw索引族Sを次のように取る。

- **S.V**: B_H.V、H、RP1–RP3で現れるactual source literal/result/field値を、それぞれの実result descriptorとrootに置いたtuple。
- **S.W**: B_H.W、およびraw sourceのregistration、capture restriction、receipt/control action、actual Return/rebind、record/result bindingで得られる全current worlds。旧bindingsと新bindingsの証拠は個々の元tupleを保持する。
- **S.Car**: B_H.Car、actual NameDelayと`f y` whole carrier、retained fieldがある場合はそのactual field carrier。元のinert source licenseとactual lexical tupleを付ける。
- **S.T**: B_H.T、上記source planの全finite raw observationsと、それぞれの未完了suffix・typed response/current world・result incidenceを付けたtuple。safeと判明したobservationだけを選ばず、元の各admitted demandからの全raw observationsを入れる。

新しいT行は `RawSrc(π,o)` とphase/descriptor indexで導入する。`DescMem(o)`をS.Tへの入場条件にしていない。完成したSを見てchallenge domainを作り直さない。外部carrierが発散するprefix、sourceを呼び戻すresponse/context、同じraw continuationの複数使用もB_Hの全fieldとraw familyに含む。

## 4. candidate-relative carrier action を導く

前CA1の通常の意味論に対する証明を、任意のcandidate Zへ無条件に移せるとは言わない。次の二つを分ける。

**RP6a: refinement射影。** 同じraw tuple上の `I_A[Z]=I_U[Z]∧Ret_A[Z]` からI_U[Z]への射影は任意のZで成立する。理由は既存conjunctionの第1成分射影だけであり、Z.Vの未証明なsubtyping closureを使わない。全pending/future familyにもpointwiseに同じ射影を行う。

**RP6b: actual NameDelayのone-step構成。** actual yのground-U証拠とS.Wのcurrent worldを持つ場面では、NameDelayのinert guardは元のDelay constructor、captured lexical bindingは同じS.V y、Force observationはRP1と同じName/ReturnのS.T行を使ってPhi(S).Carに入る。Return節ではS.V UとS.Wをpositive premisesに使い、zero/admin節では結果を捏造しない。すべてのindependent demandをS.Tの全raw索引が含む。

I_Uを前packetで明示構成した`Comp(empty,U)`の同じfull native policyとすると、q_fyのNameDelay U-result viewはこのI_Uと一致する。checked narrow input I_Int/I_Boolの値は同じground-U値なので、actual stored inletを変更せずRP6aで入場できる。一般のAに対するsame-value actionをcandidateの全要素へ仮定せず、今回のfixed Uとground Int/Boolに必要な具体constructorで証明した。

arbitrary external I_U carrierはNameDelayに置き換えない。B_H.Carをunfoldすると、inert証拠、各Force observationのB_H.T、全current B_H.W、Return時のB_H.V U、全typed response/raw continuationが得られる。これは完成済みown W*を入力にしていない。ground U resultはground clauseからその元のconstructor証拠を取り出せる。

## 5. 四成分の一段caseを実際に埋める

### 5.1 W: own-worldを前提にしない構成

source allocationはR1の同じregistryを拡張し、原scope/alias/incidenceをその実constructor mapで運ぶ。f/g/wrapperをbindingへ入れるときのvalue premiseはH⊆S.V。parameterの新bindingはcarrierのactual Return後だけに置き、B_H.Vまたはsource resultのS.Vを使う。旧bindingは元のrestrictionを使う。これらをPhiWの全binding conjunctへ一度ずつ差し込む。

current authorityは静的originの存在から導かない。entryに必要なpreconditionは独立challengeのfield、actual receiptは元のsource transitionのconclusion、Resume/FutureUseで読むauthorityはその独立history actionのfieldである。unknown State updateをimmutable compatible extensionとして扱わない。

この構成でsource世界の**binding部**とregistry/alias輸送のPhi(S).W証拠を作る。original guardがsource transitionに明記されていれば、その同じpremise/conclusionを使う。raw resultの相関からguardの真偽を推論する段階はない。

### 5.2 Car: 全source carrierと背景

NameDelayはRP6b。wrapperのargument `Delay(f y)` はsource Callの実codeを保持し、各Force prefixは対応するS.T行を使用する。source executionの完成済みDescMemを仮定しない。latent field carrierも元のfield planのT行を用いる。inert licenseは各actual Delay/field constructorの原証拠、world/bindingsはS.W/S.Vである。B_H.CarはRP5のnon-hole unfoldingで最後に同時に運ぶ。

### 5.3 T: source phaseの構成

- zero/admin: actual phaseとcurrent world、未実行suffixのS.T obligationを使う。before-receiptにactive receiptを置かない。
- external Force: B_H.Carのunfolded観測を使う。pendingではそのresponse/raw handleと現在world、RP4のordered suffixを組にする。source parameter結果を先に置かない。
- recursive q_fy: RP6bのsame-carrier admissionとactual stored `CarrierContract(U_f)=I_U`のconstructor equalityでActualAdmを作る。fのS.Vを完成済みνPhiとしてeliminateしない。実invocationのprefix/complete observationはその同じraw πで索引されたS.Tに置き、元のpositive continuation/phase clauseの子として使う。
- Return: wrapper/gはRP1/RP2で同じyのS.Vへ戻る。fのstrict field completionはRP3の小さい導出、retained fieldはそのcarrier/future premiseを保持する。current worldはそのactual return時のS.W。
- result transport/invocation return: 元のprovider/root/typed pathを保持し、current owner completionの実lawで世界を移す。外側のborrowed ownerを終了しない。

このcase splitは、必要なsource structural子observationをS.Tへ置く正当なcoinductive使い方である。ただし `P_F[S]` が **そのsource phase constructorだけで尽くされるか**は別問題であり、次節で曖昧にしない。

### 5.4 V: source constructorと全challenge

raw closure inversionはR1のactual role/entry/body/captureを与える。f captureには同じr_fとsucc、gは同じr_f、wrapperは同じground-U yを使う。capturesのsemantic premisesはS.Vにある。actual receipt/context admissionは各independent challengeのfieldとstored inlet equalityから構成する。

任意のcomplete challengeを取り、そのarbitrary carrierをB_Hでunfoldし、§5.1–5.3を各raw observationに適用する。source-defined observationについてはwhole input/current world/response/futureがすべて同じtupleのまま残る。後のcompatible eventもSの同じraw-indexed familyに既に含まれ、別のf/world/witnessを選び直さない。

これがH replacementの**source constructor部分**である。すべての元guardとfull observation conjunctがこれらから導出できればRP5が背景全体もPhi(S)へ運び、νPhiへ入る。次節はその最後の適用を実際の凍結定義に照らして検査する。

## 6. full original Phiで最後に失敗する箇所

今回の raw 帰納は、NameDelay の条件付き一段構成、return correlation、source pending suffix、背景の relative lift、local g を含む world binding 部分を与える。しかしこれらから無条件に `S⊆Phi(S)` と書くことは、次の凍結原文に反する。

`simultaneous-immutable-root-introduction` §3のPhiVは、original formation/role/profile/scope/incidence guardsと **full P_F[Z] hard envelope**を要求する。同節は明記している: Return/prefix/Bindの表示caseはそのpositive occurrencesを識別するのであって、full envelopeを置き換えない。`captured-call-closure-introduction` §2は、actual source/raw lawsと独立のprimitive/alternative full contractを別の入力とする。native signatureのOp constructorも `typing_q` と `original_license_fields` を実入力に持つ。

ここでの未導出caseを正確に書く。

```
RP-FULL:
 for the fixed original source invocation tuple o of q_fy,
 derive every independent conjunct of P_F*[S](d,o)
 from the actual source constructor and its primitive/phase law,
 without replacing P_F* by its displayed Return/prefix projection.
```

§5はsource phaseのvalue/world/continuation **positive部分**を構成した。だが現在のf/g/wrapperのfull original typed phase-law recordには、各表示caseからP_F*の残るindependent conjunctへの実mapが提示されていない。Rのregistryとnative full-protection/no-removalは静的構成とpolicyを供給するが、native signature自身が区別する `typing_q` のwhole semantic lawを同義にしない。これは外国の恣意的guardを新設した障害ではなく、**実際に選択済みPhiVのfull-envelope conjunctへの証拠**の欠落である。

したがって、§5.3の「実recursive observationをS.Tに置く」から、直ちにそのobservationのfull P_F*[S]を取り出すことはできない。前者はcandidateの定義、後者は検証すべき一段conclusionである。この差を消すと、旧完成済みmembership eliminationと同じ循環をT側へ移しただけになる。

RP-FULL は q_fy の一つの必要 case であり、それだけで全四 sort は閉じない。全 postfixedness へ適用するには、少なくとも次の **元の owner ごとの残る判断すべて**を、同じ tuple と strategy で導く必要がある。

| owner / 対象 | 既に構成した部分 | 未導出の complete case |
| --- | --- | --- |
| 各 f/g/wrapper の H value | raw Act、actual capture references、candidate S.V の捕捉値 | その closure の全 original formation/profile/scope/incidence guards、全 checked challenge の full P readout と future restriction。q_fy 以外の H replacement も含む |
| 各 source-added world | 全 binding の S.V/S.Car 部分、registry/alias の raw map | その current world の全 joint guard と、実 receipt/rebind/return/resume transition の原作用 |
| 各 source-added carrier | inert code/capture、raw Force の S.T 子、RP6a の射影 | その actual inert license/view/incidence guards と、全 demand の完全な PhiCar/observation case |
| 各 source-added T 行 | source phase、raw result 相関、元の未完了 suffix | その descriptor の full hard envelope、typed path/request/response/authority と remaining continuation の全 clause。RP-FULL(q_fy) はこの一行の一部分 |
| 各 record/result/retained field | RP3 の原 field provenance と完了結果の条件付き性質 | actual field consumption、元の field view、retained carrier/future と result membership の全 constructor case |

この全 family を導き、追加した S の各行を対応する Phi case に入れた後にだけ、RP5 が背景の全 non-hole/hole case を結合し coinduction を適用できる。特に §5.1 の binding 部分を full world guard と同一視しない。今は full Φ を表示 case だけの小さい演算子へ変更していないため、その結論を保留する。source/domain を狭めて残る条件を消す方法も採らない。

### production alternativeと混同しない

`RawSrc`に属さないactual declared W/Z等については、別のoriginal arm-local証拠をそのまま保持する。これらのcomplete production C0は上のraw source correlationの前提ではないし、未知のW/Zを障害のために発明しない。

RP-FULL は **source invocation tuple にも要求される** full observation conjunct の map であり、production の全 alternative census と区別する。exact native source P_F* を既存 positive clauses の ordered image として構成しても、元の full guard を各 constructor から導く義務は残る。上表の他の owner の case も別々に必要である。既存の別 descriptor や固定 conjunct を黙って削除してはならない。

## 7. fixed U、二つのnarrow viewと親への適用

raw sourceでは、stored U-entryを持つ同じgが正常Returnすると同じyを返す。従ってInt入力のsource ReturnはInt、Bool入力のsource ReturnはBoolであり、Parameterを二つのassignmentにする必要はない。

full checked view `G_Int`/`G_Bool`を得るには、このraw equalityを **独立に定義したfull descriptor観測**へ上げる必要がある。例として `RetSame(y)` を全source phaseのordered relationとして構成するなら、そのReturn節はsame actual y、pending節は元のf-y suffixとall futureを保持しなければならない。さらにfull original alternativesがある場合、その各original fieldも残す。raw traceだけの相関を追加constraintとして断言すればよい、という規則ではない。

その full relation と §6 の全 owner case の導出後なら、I_Int/I_Bool から同じ I_U への RP6a、同じ result tuple への ground result checking を使い、同じ g の二つの complete realization を得る。既存 same-value intersection introduction はその二証拠を **同一 value/root/world** で結合する。任意の per-port witness 選択や新しい g/f を必要としない。現時点では全 family が未完なので、その intersection membership を先取りしない。

R4へ戻す成果は以下である。

- arbitrary external carrier/world/responseを落とさない単一のB_H/Sと、generalized Hのrelative lift。
- f/g/wrapperの同じraw allocation family、全finite prefixとfuture restriction。
- completed-result相関の有限raw帰納。特にgのresult=Aというsource部分をfの最終membershipなしに構成。
- candidate-relative admission/NameDelayと、own-worldを仮定しない全binding側の構成。
- q_fy の具体的な未埋め case を RP-FULL として特定。ただし full hereditary conclusion には §6 の全 owner-indexed residual family が残り、RP-FULL 一件に限定されない。元の J_rec は未導出。

元のcoverage/native failureへ適用するにはoriginal J_recとlawful usesが必要である。今のraw theoremだけでREFUTEDとはしない。元の全intrusion/extrusion、A/B、主型性・停止性、F1/FK1、shared Cの量化を維持し、親はOPEN。

## 8. Producer r1 の handoff（履歴）

以下は査読前の producer handoff を保存する。現在の残項は §6 の全 family、査読・修正状況は冒頭と outcome に従う。以下の「未査読」「次は査読」は producer が停止した時点の記録である。

| ID / owner | 最小の次の証拠・反証条件 |
|---|---|
| RP-FULL / original descriptor・source phase owner | chosen native F_U/G_U/wrapperのfull P/guard telescopeとactual source phaseから各conjunctへのmapを示す。S.T membershipだけをPの証拠とするstepが反証。 |
| RP-RETSAME / full-result owner | same-yをraw source imageだけでなく同じoriginal full result relationのlawとして構成。actual alternativeの異なるresultを消すことが反証。 |
| RP-RECORD / source Record owner | actual fieldがstrict resultかretained carrierかの原consumptionを提示。latent fieldをformationでforceしたと仮定することが反証。 |
| RP-ACTIVE / primary | fixed U actual Parameterと同じr_fのActiveCapture field graphを使う。今回A binderは導入しない。fixed intersection採用はfull view導出後。 |

契約の25依存と契約hashを静的照合して全件一致。直接の主依存はR=`f90b88e3e7759a457991f6186782bbd5c1c0236600ca03694527767e4ca49ba8`、CA=`c3aff32c3f966526019abd49d389b140b27614be120cc3280b4728545c65c2ee`、simultaneous immutable=`a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6`、captured Call=`0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f`、source Generalize=`e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`。全manifestは契約の凍結表。Rは `/root/astra_scoped_join`、CAは本worker、candidate-coreとactive graph入力はprimary、旧原稿はその帰属を保つ。新RP1–RP6と今回のsource族は本worker単著、独立査読未実施。

三段階: raw帰納、四sort構成、full original適用の検査。上限190秒/三段階。requested Astra/medium、observed UNKNOWN、予算返却なし。hash/原文/紙上case inspectionのみ。tests/build/probe/compiler/Git/network/子なし。新規・scratch pathは本稿一つのみ。

r1を最終hashで凍結、全書込み停止、STOPPED、descendantsゼロ。次はprimary intakeとfresh independent review。workerの停止を全体目標の完了としない。
