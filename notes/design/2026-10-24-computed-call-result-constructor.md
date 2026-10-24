# Computed Call の complete result constructor

Date: 2026-10-24
Status: Authoritative missing-constructor definition under existing legitimate-definition authorization; independently reviewed at the scope below
Scope: pre-execution generated result descriptor for the original callee-first Call operation
Authority: the ongoing request to complete semantics/proofs; the explicit missing-definition authorization retained in the complete-Call and pure-read constructor decisions
Supersedes: none; no existing descriptor or foreign interpretation is changed
Production implementation / cutover authority: none
Author: primary

## 1. 新たに定義するもの

[complete Call](2026-10-07-complete-call-contribution-definition.md) は元の callee Bind → actual receiver という operation を固定し、[pure-read result](2026-10-08-pure-read-call-result-constructor.md) は Name route の R_c=ReadInvoke だけを選択した。本稿は computed/effectful callee に対する **未定義だった generated-result constructor** を明示的に追加する。既存の relation/interface graph から descriptor formation が既に証明できていた、と主張するものではない。

[CB 初稿](../theory/2026-10-24-computed-call-bind-result.md)への独立査読は、その違いを MAJOR と指摘した。以下では新 descriptor の sort、formation、解釈、introduction を直接与える。元 Call の evaluation order、whole carrier、Request/resume、world、provider、permission と independent alternatives は変更しない。

古い complete descriptors と independently fixed R_target の意味は保持する。新 constructor と別の R_target の包含は別の genuine checking proof を必要とする。new constructor の存在は production compiler が生成・受理するという命題ではない。

## 2. 静的パラメーターと descriptor formation

元 Call の独立 joint index Δ;ξ、original source occurrence e、full IF_e、binder tree を固定する。次の **型付き静的情報**を用いる。

* C_f : CompleteComputationDescriptor(Δ;ξ)。callee の complete contract とその Return interface A_f、actual callable/decomposition/provider/current-world projections。
* F : CompleteFunctionDescriptor(Δ;ξ)。checked view と、独立 complete challenge telescope D_F、whole-carrier interface I_F、actual receiver の complete P_F。これらの意味は既存のまま。
* A_e : ArgumentFormationSchema(Δ,b;ξ)。元の inert argument code/captures/origin、original reify license の slot、I_F に対する whole designated-execution checking obligation、all independent arm fields。b は以下の actual CalRet telescope 内の binder。
* IF_e の source/return/argument/receiver/result/future incidence maps と、全 original hard/scope/authority/dependency guards。actual raw operation は元の complete Call であり、新しい operator ではない。
* C_f の Return から **同じ actual provider** の F certificate へ至る checking obligation の型付き slot。実際の証明は introduction の前提であり、formation 自体がその真理を供給しない。

b は

```text
CalRet(value v, actual decomposition U, provider r,
       actual current world C,w, original result fields)
```

であり、元 Call/ResultBind の位置で束縛される。c（inert carrier）、d（independent challenge）、receipt、response、future fields はそれぞれ元のさらに内側の event telescope に置く。guard と負/universal domains は元の独立意味を保持し、作ろうとしている descriptor の membership を guard に入れない。

**新 formation rule EI-Form** を次と定義する。

```text
Δ;ξ ⊢ C_f,F,D_F,I_F,A_e,IF_e well-formed at their original scopes
all returned/argument/response/future variables bound at the above telescopes
----------------------------------------------------------------------------
Δ;ξ ⊢ EvalInvoke(C_f,F,D_F,A_e,IF_e) : CompleteComputationDescriptor
```

well-formed は既存 sort、scope、dependency、registration、license **schema** の形成を指す。genuine carrier membership、license evidence、callee success、Q、Call の安全性は formation の結論ではない。未証明の obligation を true とする規則ではなく、その obligation を持つ descriptor を形成する規則である。

EvalInvoke は complete **computation** descriptor であり、Function、Value、inlet/carrier descriptor とは別の sort。ordinary value row をこの sort に変更しない。パラメーターは execution 前に形成した有限 graph と typed Ref で与え、動的 b/c/d は内側に束縛する。全未来の event の有限列挙は不要である。

同時に、元の actual CalRet telescope b の下で **新 open formation case EI-Tail-Form** を定義する。

```text
Δ,b:CalRet(F);ξ ⊢ F,D_F,I_F,A_e,IF_e well-formed
---------------------------------------------------------
Δ,b;ξ ⊢ InvokeTail(F,D_F,A_e,IF_e;b) : CompleteComputationDescriptor
```

InvokeTail の解釈は §3.2 の「actual CalRet 直後、まだ Delay 前」から §3.4 までの同じ clauses とする。b は既に与えられた open telescope の変数であり、ここで callee の Return を作るわけではない。単独の閉じた source term へ T_e という原子を付ける規則ではない。EvalInvoke は、この open tail を元 CalRet position で束縛した composite constructor として §3 全体で解釈する。これらの new cases に対し、genuine phase evidence を各 clause へ入れる introduction rule を定義する。任意の別 descriptor に対する一般 Bind-Desc rule は追加しない。

## 3. EvalInvoke の独立な staged interpretation

この新 descriptor の DescMem を、元の phase-tagged whole observation tuple に対する以下の全 clauses で定義する。単なる返却型や外向き effect support ではなく、未実行部分、provider、witness、guard、latent/future も含む。

### 3.1 Callee phase

actual CalRet より前の initial/zero/admin/Request/resume prefixes は、同じ実 callee tuple について C_f の既存 DescMem を持つ。全 IF_e fields と hard guards を保持する。未実行 suffix は

`form original argument; assemble independent challenge; invoke actual returned provider; consumer/return/future`

であり、元の ResultBind telescope 上の dependent obligation として保持する。まだ存在しない b、c、d、receipt、result は作らない。

C_f の Request では actual raw handle と typed response/current resumed-world を保持する。callee continuation が後に actual CalRet を返す場合にだけ §3.2 へ進む。callee が返らない場合も全 finite prefixes を含む。suffix の独立 domain は固定されており、desired result や actual provider acceptance を用いて狭めない。

### 3.2 Actual CalRet と argument formation

callee の actual Return の時に、**同じ** v/U/r/current world と original Return fields を b に束縛する。C_f Return interface の証拠と、同じ callable の checked F certificate を保持する。ここで initial callee の実行履歴を捨てない。

その後に A_e の元 Delay/reify が作った inert carrier c とその license/capture/whole checking evidence を保持する。まだ指定 Force は実行されない。independent context/other-environment/carrier constructors が作る d∈D_F を同じ event/world/witness に置く。carrier validity だけを complete context と同一視せず、actual U acceptance は d の形成条件にしない。

### 3.3 Actual receiver と全 developments

actual receipt と元 entry が実際に起きた後、同じ U/r/c/d に対する元 complete P_F(d) を、IF_e の同じ full maps で埋め込む。Value/Retained/Operation の actual role、指定 consumer と native invocation return は元通りである。

* Value entry は receipt → designated one-layer Force → actual typed Return/rebind → body → consumer/return の順。未使用 formal でも Force を省かない。
* Retained entry は同じ whole carrier を bind し、元の明示 consumer だけを実行する。
* Operation provider の native Return(MakeRequestThunk)、delimiter、declaration-derived consumer は元の順で残す。
* receiver Request は、その時点の raw handle、response/current-world telescope と **まだ実行していない** suffix だけを保持する。callee/receipt/完了済み consumer を再実行しない。
* Return の場合だけ実 result/provider/current world を original result slot に置く。future interface はその同じ returned provider と後の live event に依存する。現在の Force の純粋性を latent future invocation の純粋性へ変換しない。

provider 固有の admission/observation clause は元 F membership のもの。新 descriptor は arbitrary callable implementations の正しさを追加の公理で保証しない。

### 3.4 Prefix closure、dependency と非 source-tightness

全 observations は元 operation の phase tags、original binder tree と同じ tuple を持つ。zero/incomplete prefix では到達済み stage の evidence と、残りの typed dependent obligation を保持する。admitted response/future の各合法 restriction は元 C_f、F、A_e、IF_e の lawful action を全 tuple に同時に適用する。

この定義は「特定の E_f/E_a の成功した source executions の集合」ではない。C_f に適合する元 callee observations と、F の independently compatible challenges/complete P_F を使う。non-source carrier、発散、原 conservative receiver alternatives も元の契約のまま残る。source-base M_E の成立を DescMem の定義には入れない。実 code に対する M_E とこの descriptor judgment を結ぶのは §5 の introduction theorem である。

## 4. 全 independent alternatives と生成 result slot

callee-local alternatives は C_f、argument-local alternatives は A_e/I_F、receiver-local alternatives は P_F の full original fields を保つ。whole-Call の独立 arm α は元の arm descriptor R_α と actual whole-operation fields を持ち、structural callee/receiver path を実行する必要はない。

全 arms を持つ場合の **新 formation case EI-All-Form** も定義する。各 R_α が元の complete computation sort を持ち、その同じ original arm slot と scoped family が well-formed である時、complete generated result を

```text
R_e^gen = Union(source-slot:EvalInvoke(C_f,F,D_F,A_e,IF_e),
                original whole-Call arm slots: R_α)
```

という CompleteComputationDescriptor として形成する。この表示の Union は、元の alternative tags を保持する今回の full-result case の表記である。その DescMem は、source tag で §3、arm tag α で元 DescMem(R_α) と元の全 arm guards/fields を要求するものと明示的に定義する。独立に既存の arbitrary computation Union rule があったと仮定していない。independent arm の genuine full typing、license、provider/future、admission と hard guard は owner の独立入力のままである。存在する arm を削除しない。新たな arm は追加しない。parameterized arm family は元 Ref/binder をそのまま保持する。

**新 generated-result identity case EI-Result。** 元の生成された complete computation result slot が、この constructor の sort/scope を持ち、その生成 case が選ばれた時だけ、R_e:=EvalInvoke または全 arms を含む R_e:=R_e^gen とする。これが今回定義する missing constructor case である。未選択の independently fixed R_target の意味を変更しない。

## 5. Descriptor introduction theorem

**EI-Intro。** §2 の genuine callee source proof、same-return/provider F checking、元の whole argument formation/checking、独立 challenge/guards と full IF maps があるとする。元 source-base structural Call の任意の observation O に、同じ w/ξ/operation witness を保つ

`DescMem(EvalInvoke(C_f,F,D_F,A_e,IF_e),O,w;ξ)`

を構成できる。全 genuine whole-Call arm laws もあれば、全 original alternatives に対する DescMem(R_e^gen,O,w;ξ) を構成できる。

証明。元 raw Call の phase derivation と finite request/resume development に帰納する。

1. actual CalRet 前は genuine d_f の同じ C_f evidence を §3.1 に入れる。未実行 suffix を dependent proof function として保持し、未来の b/receipt を作らない。Request では元 `Request(q,C,k) >>= S = Request(q,C,(a,C′).k(a,C′) >>= S)` を使い、原 response/current C′ の下で同じ帰納関数を適用する。
2. actual CalRet でだけ genuine result projection/checking から同じ v/U/r の F certificate を得る。元 A_e の proof function で inert c、whole checking、独立 d∈D_F を順に構成し §3.2 に入れる。carrier checking は returned endpoint inclusion の代用ではない。
3. completed F membership の admission clause と全 observation clauseを、この同じ independent d と actual U/r/c に適用する。receiver theorem E と [CB1](../theory/2026-10-24-computed-call-bind-result.md#3-post-calret-receiver-suffix-の構成) の clause-wise proof が §3.3 の全 Value/Retained/Operation/pending/future fields を供給する。
4. 同じ original tuple を用いるため、既に済んだ callee/receipt を resume で繰り返さない。restriction の合成は元各 proof action と IF whole-map の自然性の合成である。
5. whole-Call independent arm は、その実 tag と genuine R_α typing を新 EI-All の同じ arm clause へ入れる。source proof で arm の truth を代用しない。

以上は **新たに定義した** DescMem の clauses を満たす構成である。relation graph の存在だけから導いた定理ではない。M_E の source derivation は最初から別の元入力であり、`M_E∧DescMem` から DescMem を取り出す循環はない。□

## 6. Name specialization と旧意味の保存

C_Read(F,n) を、元の resolved immutable Name n の **checked view F における** complete pure read contract とする。initial/lookup prefix は同じ hereditary binding/provider certificate、actual Return は同じ value/U/r/current world、future は元 restriction のもの。この意味は既存の Name/Return constructor が与え、単に返却型を F と書いた opaque computation ではない。

**EI-Name。** 元の Name route の同じ argument schema、D_F、IF_e、guards、independent arms を固定すると、任意の元 complete/pending/zero/future tuple について

```text
DescMem(EvalInvoke(C_Read(F,n),F,D_F,A_e,IF_e),O,w;ξ)
  iff
DescMem(ReadInvoke(F,D_F,IF_e),O,w;ξ).
```

両方向は同じ phase/source/provider/world/witness fields を保持する。

証明。全 stage tags で場合分けする。CalRet 前は C_Read の定義が ReadInvoke §3 の initial/lookup、same-root F binding、complete Bind/pending suffix obligation と同じである。ここで C_Read を checked F に取ったので、単なる A_f Return から early F certificate を逆算する必要はない。

actual CalRet/Delay 前後は、両定義とも同じ returned provider/current world、元 inert c と independent d を同じ形成時点で要求する。receipt 以降は、どちらも同じ U/r/c/d の全 P_F と同じ IF_e maps を要求する。Request/resume は同じ current configuration と未実行 suffix、Return/future は同じ actual result/provider と後の guards を要求する。従って各 tag の evidence を fieldwise にそのまま他方の同じ clause へ入れられ、逆方向も同一である。whole-Call arms を添える場合も同じ tags/R_α のままなので両方向を同じ tagged alternative clauses に沿って延長できる。□

この同値は Name-only constructor を silently generalize した仮定ではなく、新定義について証明した specialization である。C_f が任意の「F を返す計算」の時に ReadInvoke と等しいという命題ではない。effectful callee は §3.1 の元 effects/pending を持つ。

既存の閉じた descriptor と独立 kernel/challenge/primitive interpretations の clauses は書き換えない。新 constructor の追加は、旧閉じた式に対する元の structural interpretation を変えない。この限定された保存と EI-Name を主張し、unknown foreign grammar の embedding、resolver completeness、source の全 result-slot correspondence を保守拡張という語で隠さない。

## 7. 生成 source への適用範囲

[CA](../theory/2026-10-24-computed-argument-carrier-checking.md) の actual h₀/f/g family では、genuine callee proof と same-provider TU certificate が得られる。actual carrier に CA3、必要な target-specific independent arms に CA4 を用いる範囲で、EI-Intro を適用し **選択した generated result case** の descriptor judgment を得る。computed first/next の source phase だけで止まっていた箇所へ、この新 result constructor を具体的に供給できる。

未知 succ の complete law、独立 arm の target-specific inclusion、固定 foreign R_target、全 native result sites の sort/scope/definition correspondence、全 Generalize/solver/principality/termination は残る。元 whole goal の量化をこの局所 family に置換しない。

## 8. Review seam

契約 [COMPUTED-RESULT-DEFINITION](../../tasks/agent-loop/sprints/computed-result-definition-20261024.md)、SHA-256 `db4aaa97df00ba5349b662ac62cd027698da3f713835f650c780dbbc2ccdb834`。実装変更・tests・build・probes・compiler run なし。

新 formation/interpretation/identity case であること、genuine inputs による EI-Intro、EI-Name の両方向、independent domains/arms、全 prefix/receipt/current-world fields が独立査読の対象。査読前の本稿を既存 authority や全体閉鎖として扱わない。


## 9. 独立査読と選択

査読対象 SHA-256 `13ec9f006294673ed41acc0876bedc688bb41a2ba89ee21e4fbabb1b1c61603f`。`/root/astra_semantics_review` は、EI-Form/EI-Tail-Form、staged interpretation と EI-Intro、EI-All、checked C_Read(F,n) に限る EI-Name の両方向を受理した。旧 relation/interface から descriptor を導く MAJOR は、この **明示的な新定義を選択した case** について解消。新たな BLOCKING/MAJOR はなかった。

primary は、元 complete-Call/pure-read の legitimate missing-definition authorization と現在の全意味論執筆の依頼に基づき、この査読済み constructor case をそのまま選択する。元 raw Call、既存 Name descriptor、independent domains/arms/guards、foreign targets は変更しない。§8 までの数学本文は査読時と同じであり、査読前表記は freeze の履歴。変更は status とこの receipt のみ。

[統合記録](../../tasks/agent-loop/sprints/computed-result-definition-20261024-outcome.md) に、旧 CB2/CB3 の撤回、再査読、exact native Let 結果と全未完了親義務を記録する。actual generated result slots の sort/scope/source-native correspondence、原 inference/主型性/停止性、全言語閉鎖は宣言しない。production authority はない。
