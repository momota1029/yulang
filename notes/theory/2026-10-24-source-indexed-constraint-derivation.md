# Application の実発行義務と source-indexed native 導出

SOURCE-INDEXED-DERIVATION-20261024/r1。著者 `/root/astra_corrected_machine`。
Baseline `25f5e05ddf7c0d3e4c407036fd52d98641adfa31`。
独立査読は SC1–SC3 を記載範囲で受理した。SC4 の semantic substitution に MAJOR 指摘があり、primary がその主張を撤回した。元の NameDelay 入場結果は保持する。査読対象 hash と修正は sprint outcome に記録する。
契約 SHA256 `38e1ee6cdd017659bcf9a1b07c85ad47ec69539646273fe1bd1d5a24cc690331`。

## 1. 原 Application から始める

G = `notes/progress/2026-10-06-source-call-generation-construction.md`、S = `notes/theory/2026-10-07-call-input-construction-proof.md`、IF = `notes/theory/2026-10-08-call-source-interface-construction.md`、SG = `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` とする。

実 resolved Call c と子 q_f,q_a を固定する。source root/scope/telescope ξ、actual Name/capture/reify origins と complete Function 変数 F_c を同じ Application node に登録する。G.§5 が発行する意味のある formula は次である。

```
exists_sigma(F_c,e).
 WF_Dec(F_c;ξ)
 ∧ VIncl(A_f,F_c;ξ,e_value)
 ∧ WholeArgCompatible(J_a,CarrierContract(F_c);ξ,e_arg)
 ∧ CIncl(ExecuteCallableImage(J_f,Delay(J_a),F_c,e;ξ),
         Comp(E_c,A_c);ξ,e_result)
 ∧ TypedCallCert_Dec(c,F_c,e;ξ)
 ∧ Role_0 ∧ canonical Gen-Call-0 records.
```

ここで J_a は actual source code image、Comp(E_a,A_a) はその printed interface。両者を同一視しない。全 carrier、actual returned callee/current world、receipt、Force、dependent rebind、body、consumer、request/pending/response/raw resume、future-provider、全元 alternative は ExecuteCallableImage と certificate の元の引数として残る。

**SC1（operand origins の構成）。** G.§5 の実 emission の各 conjunct に source-address `(c, conjunct-position, ξ)` を付け、VIncl conjunct の address を o_V、WholeArgCompatible conjunct の address を o_A とする。この address と元 formula を一緒に保持すれば、S.§3.4 の二 operand origin を構成できる。

証明。Application の発行 object は上式であり、二 conjunct はその literal subobjects。subobject injection と元の child code/reify origins が o_V,o_A の formation derivation を与える。任意の legal whole substitution θ は式全体と ξ と address に同時作用し、投影と可換。truth を読む操作はない。Gen-Call-0 だけの inventory には二 subobjects がないので、この手続はその場合には適用できない。□

これは G の明記した decorated-rule envelope における construction である。任意の parser/frontend が G を発行済みという定理ではない。実 Application emission inventory がある source では、従来 Check_c の未構成 operand-origin 欄を SC1 で埋められる。G の receipt/profile/observation の semantic premises を新たに真としない。

次に S の Name/Result/Reify/Entry/Bind constructors を source順に適用し、SC1 の二 origins を束ねて Check_c を作る。IF.§5 の Call はこの Check_c の子 frames と actual operator schema から FrameCall を構成する。元の raw providerと source field を残したまま、root-use placement の有限データが得られる。unknown Functionを導入するために成功済み checking を要求する循環はない。

## 2. obligation と realization の二つの sort

`Obl(Δ,I,J,q)` は、元 telescope Δ における interfaces I,J と実 source/checking occurrence q を持つ義務。これは syntax/schema。`Real(o)` はその義務の元 whole semantic relation を満たす proof-relevant evidence。sourceから発行されたことは Real の introduction rule ではない。

元の checking grammar SG.§3.2 の identity、logical composition、Record/Union/Intersection、same-value checking、complete Function checking を **realization constructors** とする。Function realization は checked-domain→source-domain と、同じ challenge における source-observation→checked-observation の両方を実際に証明する。scalar Function inequality をこの proof の代わりに使わない。

source frame の単なる inclusion/placement も Real(VIncl) と区別する。IF の slot insertion は actual declaration の位置を作るが、独立 operator predicate の membership を作らない。この区別は今後の全 constructorに保たれる。

## 3. 有限 native history に沿う同時生成

H_n を元 reference constrain/extrude/freshen の **既に固定された有限 constructor history** とする。finite source graphと SC1 seeds を入力に、native eventと次の source-indexed obligation recordsを同時に構成する。実装変更ではなく proof representation である。native scalar portと complete source portを同一視せず、対応欄がまだ義務なら明示的に残す。

record は `(id,native-step,source-frame,whole-telescope,parents,rule,goals)`。source-frame は source derivationまたは実登録 reference、parents は actual dependency IDs。goals は独立な complete semantic obligations の有限式/参照。erasure |-| は native-step と元 native endpointsを返す。source-frame を読むことで desired receiverを定義する規則は追加しない。

### 3.1 constructor cases

- **Seed。** 実 Application emission から SC1 の o_V,o_A と全残り conjunctを保持。native App demand `(callee-row ≤ Function(argument,result))` と pairingする。これは原 reference App のsyntax projectionであり、whole F_c を二port scalar Functionと等しいとする semantic theoremではない。extra fieldsは recordに残る。
- **Registered Name。** rootを先に登録し、Nameはresolved handleと元 binding substitutionを参照。recursive Nameは同じ monomorphic root、後の fresh useは別 instance map。referenceへの erasureは元 lookupであり、参照の存在は recursive membershipではない。
- **FunctionPort。** native `(a→b)≤(c→d)` から argument `c≤a` と result `b≤d`。source側には元 complete Function checking の domain/observation obligationとactual port indexを付ける。argumentの順序を必ず反転する。whole carrier/receipt/returnを Value fieldと混同しない。complete comparisonを実現済みなら SG Function checking のactual domain/observation evidenceをこの対応に使用できる。そうでなければ child goalを残す。
- **RecordPort。** 元 field indexとprovider tupleを保持し、native同名field比較へ消去。source realizationは同じ field/value/worldへのstructural checkingによる。field formationをForce実行に変えない。
- **Bound insertion。** actual owning row、polarity、payload、processing obligationを保持する。upperは hole入力→upper endpoint、lowerは lower payload→hole入力の schema。native erasureは元 list insertion。middle interfaceは同じ registered objectと実 substitutionで同定し、同じscalar row番号だけでは同定しない。
- **Ordered replay。** 実 lower record d:L→M とupper record b:M→Uから、endpoint消去 L≤U と source義務 `Compose(d,b)` を同時に作る。middle source objectが未認証なら `MatchMiddle(d,b)` を残す。realizationがあるときだけ合成 `real(b)∘real(d)` を作る。polarityを反転したresidualでは元 RD1/RD2 の `d∘b` の順になる。
- **Extrusion fresh。** target k、実 parent a、polarity ε、空memoの実miss、copy cを保持。nativeの一方向linkとselected-bound recursionを同時記録し、source側にはその変換の元 whole-interface checking obligationを残す。native scalar approximationだけから complete source linkのRealを返さない。各structural childはvariance、元source operand、全dependent fieldsを引き継ぐ。
- **Memo hit。** exact invocation/key `(a,ε,k)` の既登録copyをRefする。新しいsource originやcopyを作らない。memoには bounds recursion前に登録する。selected boundのcycleも有限参照になる。
- **Retained-output reuse。** original pair group、実 output、new processing derivation、new occurrenceを別記録。original創造recordを書き換えない。source realizationには新しいwhole substitution/transport goalを持たせる。fresheningは元 one-memo instance mapとbound transportを記録し、extrusion occurrenceを作らない。

**SC2（有限構成と exact native erasure）。** SC1 の実 seed inventoryと有限 H_n に対し、上の全recordsを有限graphとして構成できる。各 stepのerasureは元 H_n の同じ constructor/順序/endpoints/bounds/memo結果であり、全 native step が残る。

証明。native event数への帰納。step0は登録rootとseed。新stepは既存parent IDを参照し、finite constructor fieldsをappendするだけ。source graphのrecursive Nameは事前登録rootを参照するので展開しない。extrusion memo missはcopy IDを先に登録し、hitはそのIDを返す。freshenも同じ順序。従ってfinite H_nから無限 obligation graphは生じない。各caseのerasureは元のstepを保持する定義から従い、source annotationが native分岐を変更しない。Function argumentの反転も nativeと一致する。□

SC2は停止性定理ではない。無限 propagationをfiniteと仮定して隠さない。また cyclic obligation graphの存在はRealの存在でも、coinductive guardの証明でもない。S Theorem Sのacyclic証明をそのまま循環意味へ適用していない。

**SC3（実現済み部分の合成）。** source objectsのmatching証拠と各local whole checking evidenceが実際に与えられた有限acyclic部分では、identity/port/bound/replayのRealをoriginal checking constructorsで組み立てられ、same whole tupleと合法なrestriction/substitutionを保つ。

証明。evidence treeに帰納する。identityは恒等、Recordは元same field、Functionはdomain逆向き/observation順向きの元証拠、replayは同じmiddleの依存合成。provider/world/receipt/responseは一つのwhole tupleのfieldとしてtransportし、各portごとに選び直さない。registered cyclic referenceが残る場合はそのcomponentの独立joint realizationを要求し、単なるgraphの閉路からRealを返さない。□

したがってSC2はRD4の**同時生成syntax**を供給し、SC3は独立なlocal実現から合成できる部分を閉じる。semantic source/native対応全体をsource indexの追加だけで証明したわけではない。

## 4. h 境界と record replay への実適用

sourceは前稿の argument反例:

```
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first=h x, next=f {a=y}}
  in f
in top
```

前稿のempty-start native historyをそのまま使う。h Callは e_h=(F,H_v)、recursive Callは e_r=(F,F)。native B,Y:2、C,T:1。初回h demandが B≤Cを作り、後のFunction argumentが Record(Y)≤Bを作ってRecord(Y)≤Cへreplayする。

SC1により q_h は actual child Name h、Name x、Delay originと、VIncl(H,F_h)/WholeArgCompatible(J_x,I_h) の発行originsを持つ。q_rも同じ形式のactual operand originsを持つ。SC2の記録は

```
seed_h → ExtrusionLink(B,C) = b
seed_r + recursive completion → ArgumentPort(Record(Y),B) = d
Replay(lower=d,upper=b) → Record(Y)≤C → positive copy T/Y
```

を残す。d,bのnative middleはBだが、complete source middleの一致は別欄である。これは勝手に消さない。

### 4.1 実現した入力と、撤回した rebind の主張

I=Int、A=Record(a:I) とし、h の既存 complete Function descriptor H* の
actual inlet が選択済み `Comp(empty,A)` である入力 instance を考える。
元の joint hereditary world と binding `h:H*, x:A, y:I` が与えられている。
この正式な入力の下で、次の二つは元の規則から得られる。

1. h の Name は同じ actual h/provider を読み、`VIncl(H*,H*)` は identity。
2. x の Name/Return/Delay は CA2 の元の構成により完全 `Comp(empty,A)` を
   満たす。h の inlet との checking は同じ interface 上の identity。

これは既に与えられた **同じ x、同じ world** に対する証拠である。
既存の h への入場を、source の Name carrier だけに制限する規則ではない。

r1 の SC4 は、これに続いて actual y から Record(a:y) を作り、x の既存の
value/root をその record に置換しても、元の receipt/history/continuation
indices を保持できるとした。この後半を **撤回する**。引用した S の
whole-substitution は構文定理であり、任意の semantic substitution には
別の lawful action を明示的に要求していた。

例えば同じ world に x={a:0}、y=1 がある場合、既存 x の actual binding event
を変えずに x={a:1} へ置換できるとは限らない。静的な型 A が一致することは
この動的 action を与えない。IF の source incidence を保つことも、その world
の全依存条件を保つ証明ではない。

必要な修復は、actual Return/rebind の意味規則から **その時点の**新しい
ValueBind と resulting world を構成し、既存 h 等の証拠をその正当な event
へ restriction すること、または今回の θ の全 lawful action を証明すること。
その constructor には actual returned-value certificate と独立の history/
rebind evidence が要る。新しい binding を仮定して元の既解釈 history を
書き換えたことにする修復は行わない。

従って本稿の受理済み結果には Record(Y)≤B≤C の **source map の実現**を
含めない。SC1–SC2 はその義務と元 native path を構成し、SC3 は実現が
与えられた場合の合成を与える。上の NameDelay 入場の二項だけは元の正しい
入力条件で残る。元の RG-OWNER を閉じる意味の SC4 は未証明である。

### 4.2 最初の未実現 judgment

既存 x を変えない上記 NameDelay instance では VIncl と WholeArgCompatible を導ける。その入力から次に必要な実 Application conjunct は、元 complete invocation に関する

`CIncl(ExecuteCallableImage(J_h,Delay(J_x),F_h,e;ξ),Comp(E_h,A_h);ξ,e_result)`

および `TypedCallCert_Dec(q_h,F_h,e;ξ)` の独立なreceipt/profile/observation fieldsである。H*の元complete membershipと対応するsemantic Call ruleから導くべきものであり、発行originを証拠として使わない。さらに本例のq_rでは、source-created fのactual complete recursive-member judgmentを同時導入する必要がある。登録済みProofRefやS.Vへのcandidate inclusionはそれを供給しない。

未specializeの一般historyではこれより前に、actual fixed inletへのWholeArgCompatibleと、Function argumentのcomplete domain/observation mapのRealが残り得る。上の入口恒等 case を任意の I_U へ一般化しない。original C0、W/Z、foreign continuation、F1/FK1の量化を落としてこの差を埋めない。

## 5. 親への適用と停止

実際に除いた前提は、G の実 Application inventory から二 operand origins と Check_c を構成する部分、finite registered/memo history への source-indexed obligation 記録と native erasure である。SC3 の合成は元の実現前提を保つ。SC4 の record-rebind map は撤回した。native delayed occurrence と source map の全域対応、complete Call/recursive world の実現、全 source coverage/principality/termination は OPEN。

Mutual TODO SC-REBIND: actual immutable ValueBind/history owner が新しい binding と全 dependent evidence を実 constructor から構成する。SC-FULL-CALL: original Call semantic-input ownerが上記CIncl/TypedCallCertを同じactual H*/wholetupleから導く。SC-REC: actual simultaneous recursive membership ownerがq_rのcompleteguard/domain/observationを閉じる。SC-GENERAL: source/native ownerが一般boundのMatchMiddleとrealizationを、semantic inputとscalar履歴の双方へ対応させる。primaryの未凍結publication noteは読んでおらず、独立laneの結果を仮定しない。新semanticsや入力制限の提案はしていない。

contractと23 frozen inputsのhashは全一致。requested inherited Astra/medium、observed model/effort/duration UNKNOWN。190秒/3 stages、延長なし。静的読取り/hash/数学と唯一のleased note作成。implementation/tests/build/probes/compiler/Git/network/scratch/descendantsはゼロ。唯一の新規pathは本稿。著者による独立認証なし、reviewはprimaryが任命。最終SHAはhandoff。

**STOP: writes stopped; no descendants.**

## 凍結 direct inputs


| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/theory/2026-10-24-residual-demand-source-association.md` | `c96289283cd427d949160f6973c925d1faec6a4fa43ce8fae3e7ae47dc65936e` |
| `notes/theory/2026-10-24-birth-level-extrusion-redundancy.md` | `3d447e6982069023d2be69cee3e4cfc208e3f231f92407f34c0d1d8942a44211` |
| `notes/theory/2026-10-24-replay-extrusion-commutation.md` | `645c073ff0aff6ca7f972837bc8c36e652b50665fd751a4feb5fb6cc600a7a6b` |
| `notes/theory/2026-10-24-replay-receiving-occurrence-proof.md` | `1acaa0bd6ec055eb66ce0922b164d154e83280344ba414f6afd8841ccbee45ce` |
| `notes/theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| `notes/theory/2026-10-08-source-signature-incidence-construction.md` | `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-24-original-call-admission-construction.md` | `c3aff32c3f966526019abd49d389b140b27614be120cc3280b4728545c65c2ee` |
| `notes/theory/2026-10-24-original-recursive-formation-construction.md` | `f90b88e3e7759a457991f6186782bbd5c1c0236600ca03694527767e4ca49ba8` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |

査読後、producer STOP を確認して primary が lease を引き取り、上記 SC4 の撤回と適用範囲を修正した。新しい修復証明の認証ではない。
