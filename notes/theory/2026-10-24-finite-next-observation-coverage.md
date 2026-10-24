# 有限 next 観測 DAG の全出力契約を保つ公開輸送

FINITE-NEXT-COVERAGE-20261024/r1。Author `/root/astra_scoped_join`。FN1–FN3 は定義した有限 client grammar で独立査読受理。全 parent は OPEN。Contract SHA-256 `518bc12e5f09ad83e5ec1e2af6d96c512959ec056726e7766188fd3c33a29feb`。Baseline `54c9797c77ee75549ffb4ad81d15daf42b5f57e4`。sole write: 本稿。

## 1. 最初に固定する観測文法

元P3のprepublication全store、boundary1のf scheme、同じ低anchors H,C,D,Tを固定する。A(z)=Record(a:z)、K_i=Fun(Y_i,Record(first:J_i,next:R_i))。全original lower/upper boundsを保持する。以下は有限、型sort付き、非循環client derivation graph。辺は先に構成したnodeを参照する。source runtimeのbranch選択を追加するものではなく、fan-out/複数観測をbranchingと呼ぶ。

| sort / node | constructor |
|---|---|
| F | published root occurrence f_i（各occurrence一回のfreshenAbove） |
| G | App(F,Record(a:p))、またはSel(Q,next) |
| Q | App(G,p) |
| O | integer literal、true/false、Sel(Q,first)、App(succ,O) |
| aggregate | finite unique-label Record of any preceding nodes/aggregates |
| p | O node（ground、first結果、succ結果、これらのmonomorphic alias） |
| alias | 同じnodeの既存result rowを読むmonomorphic reference。元rowを共有 |

任意finite個のroots、任意depthのnext/App alternation、任意fan-out、同じQをfirst/nextへ何度でも使うことを許す。G/F/Qをaggregateのfieldとしてexportしてよい。外部result契約は任意finite個の `value(node)≤E`。Eは固定されたclosed regular structural descriptorまたは保持するlow coordinatesからなるdescriptorで、nodeとは独立に供給される。Record/functionを含むEの**全shape**を検査する。これは独立output checkingの入力であり、unknown source consumerがこのEを自動生成するとは主張しない。

このgrammarを後で狭めない。general client closure、ref/cell、任意関数を引数にするconsumer、client-resultのequality、nodeの改変後の値を読む可変外部contractはここで量化していない。元全client親からそれらを削除することもない。

Graph aliasはnative `Let` のpolymorphic instantiateと同一ではない。実native構文でmonomorphic sharingを表したい場合、次の明示constructorを許す。

```text
MonoBind(a,v,b) := App(Lam(a,b),v)
```

Lamはcaller level1のfresh formal row U_aを生成し、bodyのName aはその同じmonotypeを読む。外側Appのfresh row Z_bとseed `Fun(U_a,type(b))≤Fun(type(v),Z_b)` を追加する。従ってtype(v)≤U_a、type(b)≤Z_bが実分解で得られる。aliasはvのsortを継承する。bodyのfinite graphには新f occurrencesも許す。このconstructorはraw native Lambda applicationそのものであり、source ANF equivalenceやName-only ReadInvokeの拡張ではない。別source語義はprimaryの担当。

## 2. 正確な生成rows、clone、選択上界

各fresh f_iはbeforeでo_i,B_i,Y_i,J_i,R_iを独立cloneし、全boundsを同時に写す。C,D,Tは一つずつ共有、Hと未使用builtin if rowも元storeに保持する。q(Y)=q(T)=t:level1のNL5とreachable class saturationはP3と同じなので、NL6は任意finite root数mに適用できる。afterではo_i,B_i,J_i,R_iをclone、全Y_iは共通tとなる。

| client constructor | fresh actual rows / emitted seed |
|---|---|
| root App | M, `type(F)≤Fun(A(type(p)),M)`（direct rootならtype(F)=o_i） |
| G App | N, `type(G)≤Fun(type(p),N)` |
| first Sel | S, `type(Q)≤Record(first:S)` |
| next Sel | L, `type(Q)≤Record(next:L)` |
| succ App | Z, `Fun(Int,Int)≤Fun(type(O),Z)` |
| MonoBind | U_a,Z_b、上記Function seed |
| literal/Name/Record | fresh resなし（元Typerのlazy res）。Recordは子の型を構造に保つ |

同じnodeの二aliasは追加cloneも追加result rowも作らない。別Sel occurrenceはそれぞれ新rowを持つ。選択されたnext Lに後でAppを加えれば `L≤Fun(type(p),N)` という実upperが生まれる。Recordの同じresultへのfirst/next upperを両方残す。これらをP3の「R_i.upperは空」という以前の補題で扱わない。

MonoBindの生成はLam bodyを先に推論する元Typer順序を保つ。以下のmodel構成は全finite constraintsの同時解を与えるので、rhs/bodyを都合よくsolver順序変更する必要がない。全client variablesとclonesはlevel1、Primitiveは0。新extrusionを要しない。ただし一般的な実worklist停止性をfinite closureから結論しない。

## 3. モデルとguarded refinement補題

P1のregular-tree preorderを使う。Primitiveは実object identityを保つ。Topへの比較、Function反変domain/共変result、Record幅/field比較、その他のhead mismatch禁止。反射・推移・Function/Record反転とclosure/noBadは受理済みP1/P2。Topをnative syntaxへ追加しない。

beforeの**全original、全clones、全client rows、全output contracts**を満たす任意modelρを固定する。τ=ρ(T)、δ=ρ(D)、c=ρ(C)。元low clauseからA(τ)≤c。全iでY_i≤τ、δ≤J_i、K_i≤R_i、B_i≤cが成立する。

次のguarded graphを構成する。

```text
G* = μg.Fun(τ,Record(first:δ,next:g))
Q* = Record(first:δ,next:G*)
F* = Fun(c,G*)
```

τ,δ,cの元finite regular graphsに有限nodesを加えるだけなので存在する。

**FN1。** 全iでG*≤ρ(K_i)、G*≤ρ(R_i)、F*≤ρ(o_i)。base o,B,Y,J,Rについても同様。

証明を無限再帰への循環的推論にしないため、depth-n structural comparison ≤_nを用いる。≤_0は全pairs、≤_(n+1)はP1のroot clausesをchildrenの≤_nで検査する。各≤_nは反射・推移的（nへの帰納、Function domainは逆順で合成）。真の≤は全nの交わりである。root clausesは有限個の固定childrenを持つため、その交わりは同じ最大simulationを与える。

G*≤_0ρ(R_i)は自明。G*≤_nρ(R_i)から、ρ(Y_i)≤τとδ≤ρ(J_i)を使い、unfoldしたG*≤_(n+1)ρ(K_i)を得る。ρ(K_i)≤ρ(R_i)と≤_(n+1)の推移性によりG*≤_(n+1)ρ(R_i)。全nで成立し、K_iにも結論が従う。ρ(B_i)≤cとFunction反変性からF*≤Fun(ρ(B_i),ρ(K_i))≤ρ(o_i)。baseも同じ。□

この補題はR_iが既にG*と等しいと仮定しない。R_iがTop、より広いFunction、異なるregular treeでも、その元lower boundだけを用いる。任意のpositive upper outputへ後で推移できる。

## 4. 一つのwhole-graph repair

afterの元high base rowsと全publication clonesを一様に

```text
q(Y)=t : τ
B,B_i : c                 J,J_i : δ
R,R_i : G*                o,o_i : F*
```

へ割り当てる。低H,C,D,T、全Primitive、未使用builtin if rowの値はρのまま。P3のB=A(τ)を今回はB=cへ広げる。この変更はroot inputだけの要求を失わないため必要である。例えばroot argument p0と後続y input p1が異なるとき、p0≤τは一般には導けず、実際に得られるのはA(p0)≤cである。

新client valuesを文法で定義する。

| sort/node | repaired value |
|---|---|
| F | F* |
| G（root App/next Sel） | G* |
| Q（G App） | Q* |
| first Sel | δ |
| literal/true/false | 同じPrimitive object |
| succ App | Int |
| Record aggregate/argument | 同じlabels、repaired child values |
| alias formal U_a | repaired value(v) |
| MonoBind result Z_b | repaired value(b) |

同じnodeは全incoming referencesで同じ値を使う。alias利用ごとにG*や証拠を選び直さない。

**FN2（finite client induction）。** このrepairは全client seedsを満たし、各node nで `repair(n)≤ρ(type(n))`。全fixed output constraintsも保つ。

証明。ordinary graph nodesにはdependency順、MonoBindには元typed derivationの構造で帰納する。alias environmentの帰納不変条件は、aliasに与えたrepaired value≤ρ(U_a)。

* F rootはFN1。
* root App。Fの帰納仮定F*≤ρ(type(F))と元App seedを合成・反転するとA(ρ(p))≤c、G*≤ρ(M)。pの帰納仮定とRecord covarianceでA(repair(p))≤c。よってF*≤Fun(A(repair(p)),G*)。direct rootではA(ρ(p))≤ρ(B_i)≤cも導けるが、aliasの場合は前者の合成を使う。rootのpについて偽のp≤τを要求しない。
* G App。帰納仮定G*≤ρ(type(G))と元seed `type(G)≤Fun(type(p),N)`を合成・反転して、ρ(p)≤τとQ*≤ρ(N)を得る。repair(p)≤ρ(p)≤τなので新seedも成立する。この段階が任意depthにおける実input≤τの供給元である。
* first Sel。Q*≤ρ(type(Q))≤Record(first:ρ(S))の反転でδ≤ρ(S)。新seedはQ*のfirst field。別consumerがS≤Eを要求すればδ≤E。要求をIntに限定しない。
* next Sel。同じ合成をRecord(next:ρ(L))へ行うとG*≤ρ(L)。新seedはQ*のnext field。後続Appは上のG App caseへ進む。R_i/Lの実upper要求を捨てていない。
* succ。元Function seedからρ(O)≤Int、Int≤ρ(Z)。帰納仮定よりrepair(O)≤Int。new result Intでseedとresult refinementが成立する。Oがfirstに由来すればδ≤Intが実際に導かれる。succがないbranchでδ≤Intを要求しない。
* literal/Record。Primitive identityまたはcomponentwise comparison。一意labelsと同じshapeを保持する。
* MonoBind。元seedの反転でρ(type(v))≤ρ(U_a)、ρ(type(b))≤ρ(Z_b)。vのrepairを先に数学的に構成しalias environment invariantを得る。bodyの帰納仮定をそのenvironmentで適用する。U_a=repair(v)、Z_b=repair(b)ならnew Function seedは反射。body結果のrefinementをZ_bまで推移する。これはconstraintモデルの構成順であり、native typeTerm/runtimeの評価順変更ではない。

最後に各output `type(n)≤E`について、repair(n)≤ρ(type(n))≤ρ(E)。Eは保持座標だけからなり値が変わらないので、元と**同じfull output contract**が成立する。nested Record aggregateやexportされたG/Qもこの議論に含まれる。□

## 5. 全storeとclosure、reverse coverage

**FN3。** 任意finite grammar derivationについて、before modelからafter modelを構成できる。全低anchorsと元output contractsを保持し、client値は元の値のsubtypeとなる。

元high/base/clone boundsを直接検査する。B.lowerのA(t)≤BはA(τ)≤c、B≤Cはc≤c。D≤Jはδ≤δ。oのlower Fun(B,K)≤oはF*≤F*。o.upperのo≤Fun(A(t),R)はA(τ)≤cとG*≤G*。K≤RはG*≤G*。低C.lower=A(t)とH.upper=Fun(C,D)は元ρで成立。q(t)のself clauseは反射。これで全旧storeを尽くす。全clientとoutput seedsはFN2。P2のSeed/VarId/CutVar/Fun/Record帰納で全finite comparison closureを満たすのでBadはない。選択nextのupperもこのclosureに入る。

逆向きはNL6/NL7の有限m publication pullbackである。client App/Sel/MonoBind/aggregate constraintsはq_mと構造代入が可換し、Eのlow coordinatesは固定。従ってこのgrammar・このstructural modelでbefore/after可解性は同値である。追加したupper outputsも変えない。

有限depthとbranch数の一様上限は置かない。帰納は任意の有限derivationに作用する同じ関数であり、depthごとに新 theoremを仮定しない。native boundsが再帰でもFN1のguarded比較で扱う。client graphは有限DAG、source自体の再帰は元descriptor/storeへ残る。全native inferenceのterminationをこの数学的finite closureから結論しない。

**存在instance。** τ=Top、c=A(Top)、δ=Int、H=Fun(c,Int)、元/cloneを上のrepair値で置けば、Int/Bool literals、first/succとその任意finite next観測は全て型付けできる。output契約はその値以上のものに限り満たす。任意の矛盾したexternal Eがinhabitedであるとは宣言しない。存在instanceだけでなくFN3は任意のbefore解から全同じEを保つ。

## 6. 親への適用、sourceとの境界

P3の明示的「nextをconsumeしない」という制限を、この固定grammarについて除いた。next結果を何度もapplyし、同じQ/Gをfan-outし、そのwhole Function/Record結果を固定upper contractへexportしても、追加のupper要求を落とさずreverse repairできる。新しい等式inputを発明しない。高いrowsの値は変わり得るが、低anchorsとoutput要求は保たれ、全nodeの意味値はrefinementとなる。

source側には、computed next calleeの実Return/provider/current world、callee prefix、全entry/pending/consumer suffixを保つ別証明が必要である。ここで実native Lambda MonoBindをName-only ReadInvokeへ書き換えない。source U=Int∨Boolとnative Topモデルの同一性も主張しない。T/Y receiving資格、全raw clients、full effect/State/foreign continuations、一般principality/publication、A/Bとcombined terminationは元の未完了親に残る。

## 7. 凍結handoff

Contractと13 pinned input hashesをactual bytesで照合し全一致。P1–P3（本worker著、primary査読統合）、NL（primary）、元Typerの生成を再利用。今回新しい点はFN1の全recursive output refinementとFN2のfull finite graph/alias/output契約帰納。primaryのmoving source bridge稿は読まず依存にしない。著者は本workerのみ、coauthor/descendantsなし、fresh independent review前。

Mutual TODO FN-SOURCE: primaryが同じgrammarの元source phase interpretationを供給する。falsifierはcomputed calleeを無証明でName化すること、next後のcallee prefixを消すこと。FN-ALLCLIENT: native coverage ownerは本grammar外の真正client/interactionについて元全量化を証明する。falsifierはFN3を任意NL7 converseとして使うこと。別worldやforeign contractのprojectionは未供給のまま。

三stages: grammar/actual rows、guarded refinement、全graph repair/親適用。190秒上限、予約全charge。Requested Astra/medium、observed model/effort/elapsed UNKNOWN。static reads/hash/文書検査のみ。tests/build/probes/compiler/implementation/network/Git/scratch/descendantsゼロ。新writeは本稿のみ。

r1 frozen、全writes STOPPED。final handoffにSHA-256を返す。

査読対象 SHA-256 `7af7bcfce83fa5e645cf2395ac487709582b511ed963cd7b86ffeb65654842b2`。査読後の変更はこの status/receipt のみ。[outcome](../../tasks/agent-loop/sprints/finite-next-coverage-20261024-outcome.md) に受理範囲を固定する。
