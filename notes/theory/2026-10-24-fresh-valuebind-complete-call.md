# actual Return からの fresh ValueBind と original h Call の実現

独立査読後の注記: VB1/HC1–HC2、および元の対応 fields を伴う advertised complete invocation Comp port がある場合の §5.1 の CIncl 構成を、明記した範囲で受理。査読対象は `91e30ce18e92f219d89ce34cb0257b6b1463b8a1f4ee301bfe58d487881bc90a`。抽象 P_H* の表示、全 generated fields、再帰 history は未導出。後述の未査読/次は査読という記述は producer freeze 時点の履歴として保持する。この注記だけを停止後に primary が追加した。[outcome](../../tasks/agent-loop/sprints/call-realization-history-20261024-outcome.md)を参照。

CALL-REALIZATION-HISTORY-20261024/r1。Author `/root/astra_scoped_join`、descendants なし。
Status: original binding/admission/receiver の構成的導出、complete source-result の exact 残余。全 TypedCallCert/CIncl と recursive/source-global theorem は OPEN。
Contract `tasks/agent-loop/sprints/call-realization-history-20261024.md` SHA-256 `17cb330a3184cf267784141239bbfd42e9e91b1950bd7e1b9ce5a1806a9d9339`。
Baseline `ef2b33d76045802cfb61c9ed82d7115a4b9ca9f8`。Requested Astra/medium、observed model/effort/duration UNKNOWN。

## 1. 固定する actual judgment

source-indexed 稿の原 source は

```
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first=h x, next=f {a=y}}
  in f
in top
```

である。争点の非再帰 Call q_h は同じ original Name h と Name x を使う。I=Int、A=Record(a:I)。h の **既存** complete descriptor H* の actual inlet は、この固定入力 instance で selected `Comp(empty,A)` と一致する。H* の result、profile、hard envelope、actual provider、challenge domain は新しく選び直さない。

元の q_h result は `R_h=Comp(E_h,A_h)`、元の emitted Function checking variable は F_h、元の scope/assignment は ξ,η。今回の identity checking instance は F_h=H* とする。R_h の source occurrence は保持するが、unannotated endpoint E_h,A_h は既存の complete-call synthesis 制約を満たすように解いてよい。固定annotation/profileを変更することとは異なる。source 発行originは証拠を置く場所であり、そのsemantic truthではない。

以下 W/D/R/E は選択済み `call-semantic-input-realization` §§4–7 の補題/定理。現在扱う h は独立 formal のactual hereditary certificateを持つ。再帰 f を S.V に置いたことを完成済み ValueMem として使わない。元の全 source/history/future/F1/FK1、Simple-sub A/B、主型性、停止性は変更しない。

## 2. 古い x を変更せず fresh binding を構成する

### 2.1 actual Return を入力とする original constructor

actual compatible event e0 の immutable environment E0 に、h の元の hereditary certificate

`b_h : ValueMem_H*(v_h,r_h,e0)`

を保持する。元の independent history/entry rule による一つの compatible extension e0→e1 を固定する。その actual argument Force/RHS は

`Ret_a=Return(v_a,r_a,C1,w1)`

を返し、元の typed Return clause の証拠を持つ。この input は単なる raw Return の存在ではなく

`JointWF(C1,w1) ∧ ValueMem_A(v_a,r_a,e1) ∧ original result/root/provider/world incidences`

である。この証拠の供給元を、未証明の recursive f membership に置かない。ordinary independently typed external Value-entry carrier の completed Return、または既に証明された source RHS の original Return が供給する場合の constructor theoremである。元 source の recursive entry がこれを満たすという別の到達性/typing theoremは後で必要となる。

d_x は元の static formal declaration、κ は今回の actual activation/rebind occurrence とする。dynamic binding key b_x=(d_x,κ) は今回の frame で fresh。過去の同名 x がある場合、その key/root/value をそのまま残し、lexical lookup は今回の frame の b_x を指す。old world の fieldを上書きしない。

元の typed entry/rebind evidence に沿って

`E1 = ValueBind(E0 restricted to e1, d_x@κ, r_a, A, actual rebind origin)`

を構成する。これは適合性のない heap extension を独断で作る操作ではない。current world C1,w1 と原 rebind transition が持つ正当な binding projectionを、source telescopeに加える。

**定理 VB1（fresh actual binding）。** E1 の b_x projection は exactly (v_a,r_a)、h projection は exactly (v_h,r_h)。全旧 binding の immutable values/roots、元 history、receiptとdependent evidenceは変更されず、E1 は全 independently compatible future events に hereditary。

証明。Return clauseから同じ C1,w1 の ValueMem_A を射影する。旧 entries は independent e0→e1 の restriction actionで同じ eventに移す。Lemma W の ValueBind caseはこのactual returned certificateをappendし、old projectionを変更しない。joint aliases/dependenciesは同じ旧証拠、new bindingはactual rebind evidenceを使う。後の各compatible extensionでold/new certificatesを各自身のhereditary actionでrestrictする。Wのtelescope inductionで結論。□

これにより SC4 の無効な「既存x/rootをRecord(y)に置換し同じworldを保持する」操作は不要となる。例えばold x={a:0}, y=1ならold xはそのまま、actual Return {a:1} があればnew x@κ={a:1}。e1,C1,w1はその実Return後のものを使う。

### 2.2 Record Return の具体的 source case

別の actual source RHS が同じcurrent worldで y:I を持ち、元の Record constructor を実行する場合、actual field y/rootとそのValueMem_Iを使ってRecord(a:y):Aを形成できる。Record規則はlatent fieldsをForceせず、同じworldのfield証拠を共有する。元Return規則により実record/rootのReturnMem_Aを得る。その実Returnと合法rebind eventにVB1を適用できる。

これは元sourceの`f {a=y}`のargument payloadの形を構成するが、fのactual admission/entryとこの新しいframeへ至る全typed historyは証明しない。したがってVB1を使うためfの再帰membershipを暗にReturn premiseへ入れない。この限界は「古いbindingを書き換えてよい」こととは別であり、修復済みVB1の結論を弱めない。

## 3. 同じ actual H*/x から R/E を適用する

E1でq_hのresolved Name/capture derivationをそのまま使う。callee Name h は同じv_h/r_hを返し、actual CalRet branchは元のU_h decompositionと現在C2,w2を持つ。これはH*の印刷型からproviderを選び直したものではない。

1. VB1/Wをe2へrestrictし、callee Name/Return inversionにより `ValueMem_H*(v_h,r_h,e2)` を得る。`VIncl(H*,H*)` はsame decorated tuple上のidentity。
2. 同じE1のName xを元reify originでDelayする。Lemma Dによりactual `t_x=Delay(Name x)` は全inert/license/capture fieldsと全designated demandのzero/admin/Return/futureを持つ `Comp(empty,A)` carrier。
3. H* inletがそのexact interfaceであるため、元WholeArgCompatibleは同一carrier/同一interfaceのidentity checkingで得る。異なるI_Uへpure viewを押し込まない。
4. 元のindependently admitted punctured ambient context、valid other values、同じactual h/t_x references、checked admissionでchecked challenge dを組み立てる。ActualAdmやoutput safetyはassemblyの入力ではない。
5. Theorem Rをこのsame tupleへ適用し、`Acc(CarrierContract(U_h);t_x,C2,w2,η,ξ)` とU_hのactual receipt/path/context preconditionsを得る。
6. Theorem Eは、同じU_h/dの全zero/admin/pending/complete observationと全admitted response/resume/futureを `P_H*(d)` に入れる。

**定理 HC1（実 h Call の入力と receiver）。** 上のactual Return/rebindと元formal H*の証拠から、q_hの同一callee、同一argument carrier、同一current worldでwhole admissionとcomplete receiver observation typingを構成できる。

証明は1–6。全量化は元H*の独立domainのままで、今回のNameDelayだけがH*に入場できるという制限を加えない。複数actual provider decompositionsがあればretained CalRetのそれぞれに同じmembership eliminationを使う。旧grantをnew eventでliveと仮定しない。□

HC1はSC4撤回後のinput caseを、**actual fresh Return/rebindを含むjudgment**へ進めた成果である。単なる「new x:Aを仮定した環境」から始め直していない。

## 4. complete source Call のphase assembly

q_hのsource imageはcallee評価、argument inert formation、actual receipt、U_h-owned entry、body、designated consumer、invocation returnの順である。以下のphase証拠をHC1と元constructorから組み立てる。

| phase | 実際の証拠とsuffix |
|---|---|
| callee前/Name lookup/CalRet | Wとoriginal pure Name/Return。C2,w2の同じhを返す。まだreceiptやargument Forceを実行しない。 |
| inert t_x形成 | Dのinert clause。元reify/license/reference。runtime receiptを形成したことにしない。 |
| actual receipt/entry | RのActualAdmから元Invoke transitionのpreconditions。実transitionがreceiptを一度形成し、Eがtyped phaseを与える。 |
| Value Force Return | actual entry carrierのReturnでWを適用。result bindingはその時点だけ。hの実entryがRetainedなら同じcarrierをRetainBindし、Forceを追加しない。 |
| entry Request/divergence | 元request/raw handle/current worldと未完了rebind/body/consumer/return suffix。response後はそのsuffixだけを継続、receiptを再実行しない。 |
| body/consumer pending | Eの元full P_H*。完了したshellを再実行しない。operation-providerのnative Returnとdeclared result consumer完了を混同しない。 |
| final Return/future | 元のactual result/provider/rootとそのdependent future family。後のeventのcurrent worldで証明をrestrictする。 |

**補題 HC2（source-image分解と全phase typing）。** q_hの任意のactual finite source observationは、上表のpre-receiver prefixまたはHC1のreceiver/consumer developmentへ元のordered constructor equationで分解される。各phaseに上表のfull typed witnessを与えられる。

証明。source Callのactual transition/finite-prefix導出を反転する。Name calleeはpure lookup/Returnのcasesだけ。Delayはinert。receiver開始後は同じU_h operationの残りでありEを適用する。Request/Bind equationは `k_arg(response,C') >>= remaining_suffix` なので元順序とcurrent-state fieldsを維持する。有限development長への帰納で繰返しRequest/Resumeも含む。非Return prefixも場合に含むため発散をvacuityにしない。□

HC2の型付け先は各phaseの元Name/Delay clausesとP_H*であり、まだ独立に名付けられたR_hではない。以下でその違いを隠さず実Applicationの最後のfieldを検査する。

## 5. original R_hへのCIncl:埋まった部分と最初の残余

求める元のconjunctは

`CIncl(ExecuteCallableImage(J_h,Delay(J_x),H*,e;ξ), R_h;ξ,e_result)`。

HC2はその左辺のfull semantic witnessesを構成した。各witnessを同じtupleのR_h membershipへ入れるには、R_hの原defining clausesを反転し、次のlocal result-port actionを実際に与える必要がある。

```
ResultPort_h:
  (q_hの元callee/inert prefixes, または同じdのP_H* receiver/consumer witness)
  → R_hの同じphase/actual result/provider/world/future witness,
  元e_result/return-port correspondenceに沿う。
```

これが与えられた場合、HC2のphase inversion後にその対応caseを適用する写像がCInclの実証拠となる。Call consumer以後のresultだけを写して前半のcallee/entry/pendingを捨てる写像は不可。given source imageの各元を同じwhole tupleのまま写すため、全source-image CInclを得る。

### 5.1 unannotated synthesisによる構成を実際に試す

元q_hはresult annotationを持たない。したがって「任意に固定されたR_hへの包含が入力だけから従わない」は存在構成の障害ではない。この稿の初期凍結時のBool/Int任意assignment diagnosticはこの理由で撤回する。元source変数の同一性を保持して解くことは合法である。

追加で読んだselected source-result-synthesis-choice §§1,4–5はknown interface forwardingを選択する。typed-core §6 application rowは `Computation(E_call,A_call)` を生成し、これらのendpointを既存complete invocation relationで制約する。§9のJ_callはactual ExecuteCallableのcomplete relational imageであり、closure bodyのJ_bodyとは異なる。この二規則を使う候補assignmentは、同じq_hの `R_h := J_call(H*,t_x)` の**既存source Comp表示**である。H*のbody resultをその代わりに代入しない。

構成を二段階に分ける。

1. H*が既に広告しているcomplete invocation portが `O_h=Comp(E_out,A_out)` として、その元profile/typed-path/response/future対応を伴って存在する場合、元fresh E_h,A_hにE_out,A_outを代入する。q_hのsource result occurrenceは維持し、対応は元source application/return-port introductionで付ける。既存O_hの各complete memberへTheorem Eを適用する。Name callee prefixは同じcallableを返すpure Return、Delay形成はinertで、元Call constructorのprefix casesへW/Dの証拠を付ける。receiver以後はEの同じtupleをそのまま使う。Request時はHC2の同じpending suffix、response/futureは同じcurrent-event restriction。これが `ResultPort_h` の具体的case関数であり、HC2との合成でCInclを構成する。新しいH*保証は要求せず、元advertised **complete invocation** guaranteeを使う。body-only portや外向きrowだけではこの手順の入力にならない。
2. 今回固定されたH*のデータが単に `D_H*,P_H*` という独立関係とwhole-carrier inletを持つ場合、上の `O_h` 表示と元application-result pathへの対応がそのデータから射影できるかを検査する。semantic-input §2はwhole observation interfaceを独立入力とするが、任意P_H*がsource `Comp(E,A)` grammarのどのdescriptorかを定義していない。contextual-definition §1は選択が「exhaustive descriptor/model interpretation」を採用しないと明記する。typed-core §6はcomplete-call endpointをrelationで制約し、§9末尾はcomplete ExecuteCallable imageのfinite symbolic presentationを未構成とする。source-result-synthesis-choice §4のResult規則は**既にknown**なComputation(E,A)を保持する規則であり、任意の関係P_H*からその表示を作る規則ではない。

従って実際の未供給fieldは、自由なR_hへの任意checkingではなく、**この継承H*のadvertised complete invocation observation relationのsource Comp表示とその元result-port projection**である。これは同じP_H*を後付けで強化することなく、その保証を既存descriptor構文に読むfieldである。もし「advertised complete invocation-result port」という言葉に既にこのfull fieldが含まれているなら、上記1がそのまま必要な実CIncl証拠を与え、HC-RESULTは閉じる。今回の固定データにはこのfieldの定義/値が提示されていないため、普遍的に存在すると宣言しない。

特に `R_h := successful observations` とする新しい意味論は採用しない。J_callという意味的imageは既存§9により存在しHC2で全phaseを型付けできるが、それが元source endpoint grammarで表せることとgenerated decorated result occurrenceに沿うことは別の導出である。この残余はnative inferenceの有限性全体を要求するものではない。この一つのH*についてのfull advertised result port/projection一個で足りる。

### 5.2 正確な親適用

このpacketはactual fresh bindingとsame-carrier receiverを構成し、さらに**advertised complete portがあるH*のinstance**に対してunannotated result assignmentとcomplete source CInclを上記case関数で構成した。任意target assignmentを満たすという不要な量化を置かない。full portが不明な元H*の全instanceについては、そのsource表示/projectionが残る。独立whole-Call W/Zのtypingはこのsource-image witnessに含めない。

## 6. TypedCallCertのfield-by-field組立て

source-generation §5のTypedCallCert_Decは「supplied decorated receipt, profile, operation, observation, correspondence premises」を保持すると規定する。固定入力にはexhaustive dependent record declarationがないため、次表を全宇宙の新定義にはしない。実際に指定された各categoryへの供給を明示する。

| 元field/category | このpacketの証拠 | 判定 |
|---|---|---|
| resolved source/Check_c/operand origins | 元SC1とsource Name/Delay形成。同じq_h,ξ,e_value,e_arg | 構成済み。originからtruthは導かない |
| callee/formal/provider | VB1でrestrictしたH*、W/Name/CalRet、元Actの同一U_h | 構成済み |
| whole argument/inlet | Dとexact inlet identity、R | 構成済み |
| actual receipt/path/context | Rのpreconditionsと実Invoke transition。未来のreceiptを事前に存在させない | actual phaseごとに構成済み |
| entry/body/result consumer/operation | 元U_h operationとE、HC2のfull ordered suffix | 構成済み |
| observation/current world/response/future | Eとindependent compatible-history restriction、HC2 | P_H*およびprephase clausesで構成済み |
| original source result correspondence | 上記ResultPort_h at e_result | advertised complete Comp portがある場合は§5.1で構成。今回の抽象H*ではその表示/projectionが残る |
| source-generated profile/typed-path coverage beyond supplied H*/origins | 実source profile formation/packet mapsを保持し、H*自身のprofile証拠はEから取得 | H*の既存証拠は供給。q_hの別generated profileとの対応は未供給なら残る |
| independent complete operation alternatives | 元のactual arm declaration/evidence | source-image証明から新規に作らない |

source profileのunannotated policyを勝手に変更したり、全latent positionsへ blanket保護を導入しない。既存formation証明が別途ある場合そのactual mapを使えるが、今回のcallee実現だけで全generated profileと一致したことにはしない。

この表はprefix/entry/consumer/worldを曖昧なTypedCallCert仮定へ戻さず、証拠のtermを具体化したもの。完全recordの残るfieldを削除してTypedCallCertを宣言しない。

## 7. source imageとindependent W/Z、受領境界への適用

HC1/Eはactual U_h interfaceに含まれるreceiver-local alternativesをその本来のfull契約の範囲で含む。他方、独立whole-Call ZはName/receiver実行のimageとは限らず、Wは元のchanged-coordinate/provider/future actionを持つ。CInclの左辺がsource ExecuteCallableImageであることと、complete operation C0が全independent armsを量化することを区別する。全C0/OwnedCall contributionを使う段階では各actual armの独立typing証拠を残す。新しいW/Zを発明して障害にせず、存在するarmも除去しない。

争点のB≤C receiving boundaryに戻すと、**actual fresh x:Aがそのままhへ渡る**場合のwhole carrier admissionとreceiver observationはHC1で実証拠になった。SC3のsource-map compositionへこのinput mapを渡せる。hのactual receiving callableは同じH/root、actual entry/worldは元のものなので、semantic source boundaryのこの局所部分は型名やoriginだけの推測ではない。

しかしRecord(Y)≤Bがnative propagationで現れたことから、その実historyにVB1のactual typed Returnが存在するとは推論しない。recursive q_rにはfのcomplete member/worldとそのentry transitionの別証明が必要。さらにsource image→R_hのResultPort_h、native replayのMatchMiddle/occurrence transportが残る。従ってT/Y copyのsource interpretationやRG-OWNERをこの非再帰Call結果だけで閉じない。

### mutual TODOと次の一手

* **HC-RESULT** — original q_h source-result/checking owner: frozen H*のadvertised complete invocation portのsource Comp表示と元result projectionを具体化する。§5.1のassignment/case関数を適用すればCInclが得られる。callee/entry effects、pending/future、元result/providerのどれかを落とすことがfalsifier。
* **HC-DECORATION** — original source profile/certificate owner: 元TypedCallCertの実recordとq_hのsource-generated profile mapsを供給する。source incidenceやH*のprofileだけから別profileのtruthを得ることがfalsifier。
* **HC-REC/HISTORY** — original recursive-member/history owner: 元q_rのactual typed argument Returnとcompatible entry/rebindを独立に導出してVB1へ渡す。candidate S.Vやnative lower boundをその証拠とする循環がfalsifier。
* **HC-TRANSPORT** — source/native owner: この実現したsame-carrier mapとnativeB≤C、replayのsame-middle/receiving-occurrenceを結ぶ。scalar row equalityでwhole source tupleを同一視することがfalsifier。

今回完了したのはVB1とHC1/HC2のoriginal constructor judgments。SC4の旧主張は復活しない。完全source CIncl/TypedCallCert、recursive/history bridge、全言語親はOPEN。

## 8. 凍結・依存・資源

契約と20 frozen inputsのSHA-256をactual bytesで照合し全一致。全manifestは冒頭のfrozen contractにある。主要直接依存:

| input | SHA-256 |
|---|---|
| contextual Function definition | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| semantic input realization W/D/R/E | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| source Call generation | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| Call input construction | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| source-indexed derivation with SC4 withdrawal | `f11968c9e30d64a96e0a0f7bfebd75d31ff53a36e0af884d1d0cc3fe32491698` |
| prior admission construction | `c3aff32c3f966526019abd49d389b140b27614be120cc3280b4728545c65c2ee` |
| typed computation core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |

SC稿/CA稿のproducerは`/root/astra_corrected_machine`、SC4撤回はprimary。旧W/D/R/Eと他入力は各frozen artifactの帰属/選択範囲を維持。本稿は本worker単著、独立査読未実施。whole-substitution構文定理をactual world変更の証拠として再利用しない。primaryのmoving copy-genealogy稿は読まず依存にしない。

三stages: actual ValueBind、同一carrier R/E、fullphase/certificate/親適用。190秒上限・全予約charge、observed duration UNKNOWN。static読み取り/hash/数学/fence・whitespace検査のみ。tests/build/probes/compiler/implementation/Git/network/scratch/descendantsゼロ。唯一の新規pathは本稿、final messageがhandoff。

追加依存（primaryがreadを許可）: `notes/design/2026-10-02-source-result-synthesis-choice.md` SHA-256 `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992`。Authorは同文書のprimary、selected source authorityの範囲だけ使用。

r1 revised freeze、全書込み終了、STOPPED。次はLuna intakeとfresh independent review。親はOPEN。
