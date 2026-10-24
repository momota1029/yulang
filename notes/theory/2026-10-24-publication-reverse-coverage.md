# 二つの実 App chain に対する公開後の逆向きモデル輸送

PUBLICATION-TWO-USE-20261024/r1。Author `/root/astra_scoped_join`。P1–P3 と実 client 導出は記載した範囲で独立査読受理。全 parent は OPEN。Contract SHA-256 `bbe1f0a66acc592b67bb5050fd5d1e1977a83b99140f26b14c2c4274fbe75aed`。Baseline `b4b684a1426ba6bc99a4f7f4946aba7c57fae0fe`。

## 1. 原store、公開、同じanchors

NM/BRDの正確なsourceと空初期boundsからの公開直前storeを使う。

```text
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first=h x, next=f {a=y}}
  in f
in top
```

A(t)=Record(a:t)、K=Fun(Y,Record(first:J,next:R))。Kは追加rowではない。

| row | level | lower | upper |
|---|---:|---|---|
| H | 1 | empty | Fun(C,D) |
| o | 2 | Fun(B,K) | Fun(A(Y),R) |
| B | 2 | A(Y) | C |
| Y | 2 | empty | T |
| J | 2 | D | empty |
| R | 2 | K | empty |
| C | 1 | A(T) | empty |
| D | 1 | empty | empty |
| T | 1 | empty | empty |

この全storeを残し、boundary1でroot oを二回使う。caller levelは1。各use iの実freshenは高いo,B,Y,J,Rをo_i,B_i,Y_i,J_i,R_iへ写す。低いC,D,Tを同じ物理rowsのまま共有する。Hはroot oからreachableでないが、元storeとそのboundを保持する。builtin ifの未使用rowは空のままである。

qはYとTだけをt:level1へ等置する。元Yの唯一のbound Y≤Tはt≤tになり、元Tのboundsは空。他のboundのleaf levelは下がるだけ。よってNL5の全leaf条件を満たす。oからY,Tはともにreachableなのでclass飽和性も成立する。NL6によりquotient側のuseはo_i,B_i,J_i,R_iをcloneし、Y_iは作らず共通tを使う。q_2(Y)=q_2(T)=q_2(Y_1)=q_2(Y_2)=t。他はbase qまたは対応する独立cloneへ写る。C,D,Hは固定される。

after側も全旧boundsをqで写して保持する。T/Y以外のcopy pair C/B、D/Jを等置しない。これは資格を証明したintrusion実行ではなく、争点の等置を行った場合のconstraint比較である。

## 2. actual clientsと全新規result rows

元native TyperのLam/App/Sel/Rcd/Var規則をそのまま使う。二つのchainをsame expected first Intで実際にconsumeするため、source native fragmentを

```text
{ left  = succ ((((f {a=0}) 0).first)),
  right = succ ((((f {a=true}) true).first)) }
```

とする。元let-recの`in f`をこのclient bodyにした局所native検査であり、外側topの二回instantiateや別hの作成ではない。原schemeを二回読む。source-semantic Name-only bridgeはprimaryの別証明であり、本native App grammarから推測しない。

p_1=I=同じTyper.IntType object、p_2=L=同じTyper.BoolType object。印刷名の等しさでPrimitive identityを潰さない。iごとに新rowは正確に次の四個。

| row | actual constructor | seed |
|---|---|---|
| M_i | inner App `f {a=literal_i}` | o_i≤Fun(A(p_i),M_i) |
| N_i | outer App `(inner literal_i)` | M_i≤Fun(p_i,N_i) |
| S_i | Sel `.first` | N_i≤Record(first:S_i) |
| Z_i | App `succ selection` | Fun(I,I)≤Fun(S_i,Z_i) |

全rowはlevel1。literal/true、Record、Name/succ lookup、outer Recordはresをallocateしない（Typerのresはlazy）。従って公開clone以外に計8rows。client全体のresultはRecord(left:Z_1,right:Z_2)。各chainの未選択next fieldもN_iのlower Record内のR_iとして保持され、消去されない。

既存clone boundsは上表の高いrowsを同時に添字iへ写した全lower/upper listsである。low rowsのboundをuseごとに複製しない。以下はそのboundsと4seedからの実structural/CutVar consequencesである。

```text
A(p_i) ≤ B_i                 K_i ≤ M_i
p_i ≤ Y_i                    Record(first:J_i,next:R_i) ≤ N_i
J_i ≤ S_i                    S_i ≤ I, I ≤ Z_i
p_i ≤ T                      D ≤ I
```

最初の行はo_i.lowerと第一App seedのFunction分解。第二行はK_i≤M_iと第二App seedの分解。第三行はSelとsucc。最後はY_i≤T、D≤J_iとCutVar/推移。必要なのはp_i≤Y_iであり、Y_1=I、Y_2=Lという等式ではない。第一argumentからもA(p_i)≤Cを得るが、これをA(p_i)=B_iと読み替えない。

## 3. 使用するstructural modelと証明するlaws

NMのequality-only modelでは二つのPrimitiveを一つのYに入れられない。ここでは証明用のより広いモデルを明示する。native実装にTop constructorを追加しない。

DはPrimitive object identity、Top、Funの二children、一意labelsの有限Recordからなるguarded regular treesのbisimilarity classes。順序≤は次の最大simulationで定義する。

* a≤Topは全aで成立。
* Primitive(p)≤Primitive(q)はpとqが同じobjectの時だけ。
* Fun(a,b)≤Fun(c,d)はc≤aかつb≤d。
* Record(fs)≤Record(gs)はgsの各labelがfsにあり、その対応fieldで≤。
* それ以外のroot pairは不成立。

Top≤b（b≠Top）は認めない。各意味値は閉じたregular treeであり、nativeの未解決変数ではない。native構造項の解釈は構造を保持し、variable leavesだけに値を代入する。

**P1（preorderと反転）。** 反射性は恒等relationがsimulationであることから従う。推移性は≤の合成relationを調べる。右端がTopなら成立。右端non-Topなら中間はTopになれず、同じroot kindを持つ。Primitiveはidentity推移、Recordはfield包含の推移と対応childrenの合成、Funは逆向きdomainの二比較を逆順で合成しresultを順に合成する。従って合成relationもsimulation、最大性から推移性。definitionの一段反転によりnative Fun/Record比較の全child conclusionsが成立する。これは一般preorderのmonotonicityからの不正な反転ではない。

**P2（closure/noBad）。** 全seedsとstore clausesを満たすvaluationならGEのC(Γ)全体も満たす。Seed/VarIdは仮定/反射、CutVarは推移、Fun/RecordはP1の反転で帰納する。本fragmentのRecord labelsは一意で、native first-matchと同じchildである。構造headsの解釈はnative headsを保つので、異種heads・別Primitive object・missing fieldというBadは成立しない。Topはvariableの像としてのみ現れ、nativeの異種構造headをTopへ変えない。従ってC(Γ)にBadはない。

P1/P2はこのmodelの性質であり、sourceのfull effect/receipt/world subtype意味論を変更する提案ではない。

## 4. before/after双方の具体的な一モデル

同じ低anchor valuationを先に固定する。

```text
T=Top,  C=A(Top),  D=I,  H=Fun(A(Top),I)
G = μg.Fun(Top,Record(first:I,next:g))
Q = Record(first:I,next:G)
```

Gは有限二constructor nodesのguarded graphで存在する。元high rowsと各cloneの値を一様に

```text
Y=Y_i=Top, B=B_i=A(Top), J=J_i=I,
R=R_i=G, o=o_i=Fun(A(Top),G), K=K_i=G
M_i=G, N_i=Q, S_i=I, Z_i=I
```

と置く。元全storeのboundsは等式または反射性で成立する。first AppはA(p_i)≤A(Top)とG≤G。second Appはp_i≤TopとQ≤Q。SelはRecord width rule、succはI同士。outer resultはRecord(left:I,right:I)。IとLは異なるobjectsのままでありI≤L/L≤Iを導かない。

この同じvaluationはq_2の全fiberで一定なのでafterの全base/clone/client rowsへそのまま降りる。P2で双方の全有限closureがnoBad。全client rowsと旧boundsを含むため、seedだけが成立する例示ではない。

actual client execution of constrainにもnew extrusionはない。公開後の全reachable variableと新rowはlevel1、Primitiveは0、構造項もlevel≤1なので全variable guardsを満たす。低anchorsに追加されるのはp_i≤T、A(p_i)≤C、D≤Iなど。C/Tは構造upperを持たず、DのupperはIのみ。唯一の再帰構造R_i.lower=K_iは、clientがnextをconsumeしないためR_i.upperを生成しない。M_i/N_i/S_iからのreplayは上記有限field/domain鎖を辿って終わる。q後のt≤tはidentity/cacheで止まる。従って本二chainには実際にも有限な追加comparison derivationがある。一般solver停止性は主張しない。

## 5. 低anchorsを保持する具体的reverse transport

一モデルの存在だけでなく、この**exact client family**について次の輸送を構成できる。

**P3。** P1のmodelで、beforeの全store/二client constraintsを満たす任意のρがあるとする。H,C,D,TとPrimitive objectsの値を全て固定したまま、afterの全constraintsを満たすρ'を構成できる。公開root/client結果を同じ意味値に保つとは要求しない。

証明。τ=ρ(T)、δ=ρ(D)と置く。§2の実導出とP1からI≤τ、L≤τ、δ≤I。元C.lowerからA(τ)≤ρ(C)、H.upperからρ(H)≤Fun(ρ(C),δ)も保持する。τ,δの既存有限graphsに二constructor nodesを加えて

```text
Gτδ = μg.Fun(τ,Record(first:δ,next:g))
Qτδ = Record(first:δ,next:Gτδ)
```

を作る。afterの全high base rowsと各use clonesを次でassignする。

```text
q(Y)=t : τ
B,B_i : A(τ)             J,J_i : δ
R,R_i : Gτδ              o,o_i : Fun(A(τ),Gτδ)
M_i : Gτδ                N_i : Qτδ
S_i : δ                  Z_i : I
```

全low H,C,D,Tはρと同じであり、上のtは既存Tの値τ。未使用 builtin if の空行を全 allocated store に含める場合、その値もρのまま保持する。元low bound A(t)≤C、H≤Fun(C,D)はそのまま。B≤CはA(τ)≤ρ(C)。D≤Jはδ≤δ。他の元high/cloned clausesはguarded equationの同じ両辺。各clientのfirst/second Appにはp_i≤τ、SelにはRecord width、succにはδ≤IおよびI≤Iを使う。よって全after clauses成立、P2で全closure成立。□

このrepairは元high値やclient中間値を保持するvaluation factorizationではない。ρ自体がq_2-fiber constantでなくても、明示した関数で新ρ'を作る。低anchorsの解を変更して二useを独立化する逃げ道は使わない。実expected first型はIntというupper constraintなのでδ≤Intで十分、δ=Intを別途clientに強制しない。

逆方向はNL7のpullback。従ってこの二chainと全original boundsについて、P1 modelでbefore/afterの可解性が同値であり、元low anchor valuesごとにafterの解を構成できる。同じ証明は任意有限個のp_i≤τと共通first upper Iという同形client familyへ及ぶ。別のupper requirement、nextの追加consumer、別のshared mutable/effect interfaceにはこのtransportを適用しない。

## 6. 元coverage義務への適用と残項

この実client familyは争点のT=Yの反例にならない。Int/Boolが入力に現れるだけでは、共有Tのもとで矛盾しない。`Y_i=p_i`を外から加えたequality-client反例と、元Appが生成したp_i≤Y_iは区別される。Topはこのnative modelで両下界の上界を与える。source側のcommon U=Int∨Boolの実member証明とは別であり、native Topモデルからその意味論を導出しない。

P3はNL7の任意client converseではない。一般のreverse publication/principalityには全original client constraintsとcomplete source witnessesを量化する必要がある。さらにqを実際に許すsource receiving/owner/SCC資格とfull native-source correspondenceは未解決のまま。この結果は資格に関係なく、その仮のquotientで本client familyが失われないという限定判断を供給する。

次のnative攻撃点は、P3が変更するhigh result/next coordinatesに元sourceが実際に追加upper demandを課すclientを構成し、その全App/Sel rowsで再比較すること。単に任意等式を置く方法はsource witnessにならない。source laneには共通hのInt resultを持つ二actual input/useとそのName alias/entry/world evidenceを要求し、このmodelとの対応を別途確認する。

## 7. Frozen handoff

Contractと15 pinned input hashesをactual bytesで照合し全一致。NM/GE/NLはprimary著、BRDは`/root/astra_corrected_machine`著、その他の帰属は各frozen入力のまま。本稿単著、独立査読未実施。Typer.scalaのtypeTerm、constrain、freshenAboveを直接読み、App/Selのlazy resとPrimitive object identityを照合した。primaryのmoving source-use稿は読まず依存にしない。

Outcome: P1/P2 model laws、全actual rowsを含む具体的二use model、low anchorsを保つP3 reverse repair。Parent remains OPEN。Mutual TODO PUB-SOURCE: primaryが同じcommon h/fのactual semantic usesを供給する。PUB-GENERAL: native coverage ownerが追加の真正source demandを構成してP3の限界を調べる。falsifierは未列挙row/旧boundの欠落、Primitive collapse、Y_iの入力上界を下界から捏造すること。

Three stages: exact clone/client generation、model/closure、reverse transport/application。190秒上限・予約全charge。Requested Astra/medium、observed model/effort/elapsed UNKNOWN。静的read/hash/文書検査のみ。tests/build/probes/compiler/implementation/network/Git/scratch/descendantsゼロ。唯一の新pathは本稿。

r1 frozen。全write STOPPED。final messageにhashを返す。

独立査読入力 SHA-256 `30a06bbb84b4185794235e88ee3aff941044f74806c97594866f46e0b8985b99`。査読後はこの status/receipt だけを primary が更新した。[outcome](../../tasks/agent-loop/sprints/publication-two-use-20261024-outcome.md) に範囲を固定する。
