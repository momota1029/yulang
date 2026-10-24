# let-free 高階 client の構造的 downward model transport

LET-FREE-CARRIER-20261024/r1。Author `/root/astra_scoped_join`。独立査読前のnative構成的証明。Contract SHA-256 `8c1c7f1d4141984b6bb4799cd8aaca6a6cf365b530f3c18cd4fc5d17de65c4d7`。Baseline `d613a7a34cfd6f98aea09f07682f4a6cef519aa9`。本稿のみwrite。

## 1. 正確な親とclient domain

P3/FNの同じsource由来の公開直前store、f root o、boundary1、q(Y)=q(T)=t:level1を固定する。原H,C,D,T anchors、全base high rows、全lower/upper boundsを保持する。対象clientは次の任意有限termであり、next/Appのshape restrictionはない。

```text
 e ::= Var(x) | Lit(n) | Lam(x,e) | App(e,e)
     | Rcd([(label,e),...]) | Sel(e,label)
```

各ordinary binderはmonomorphic。local Let/LetRecはこのgrammarにない。lambdaのbodyも任意の同じgrammarであり、lambdaを引数/結果/Record fieldに入れてよい。free fは既存のpublished schemeの名前。各resolved free f occurrenceは独立の実freshenであり、shadowされた同名formalをfreshenしない。任意のmonomorphic aliasは元のresolved bindingを読む。同じformalの複数回使用、capture、branch状の複数useを同じrowで扱う。`App(Lam(x,b),a)`はraw native構文そのものとして含み、ANF/Let equivalenceを使わない。

**モデルdomain。** 受理済みP1のguarded regular-tree structural preorderをそのまま使う。Recordはnode内でlabelsが一意のもの。これはP1の固定されたmodel domainであり、本稿の全client定理はそのdomain内の全let-free derivationsに対するもの。pinned Typer.scalaはRcdのlistをそのままmapし、重複labelを明示rejectしていない。したがって「全raw ASTの重複label recordも覆った」とは主張しない。既存wellformed-sourceからこのdomainへのembedding、またはduplicate-aware別モデルは独立残余である。この境界はprimaryに報告して明示保持した。nativeのfirst-matchを別record意味論へ変更しない。

contextには、固定monomorphic external values/同じprimitive builtinsを入れてよい。それらの型に変更対象の高いf rowsを別入口から露出させない。fへのアクセスはこのpublished schemeか、それを受け取ったclient formalを通る。閉じた外部型/保持する低coordinatesからなる型は不変である。元builtin `if`を含める場合、その独立schemeのfreshened rowは後述のnon-f client rowとして元値を保持する。新しいclient内generalizationではない。

固定output contractsは任意有限個の `type(e_k)≤E_k`。E_kは独立のclosed regular descriptor、または保持するexternal/low coordinatesから形成したdescriptor。Function/Recordの全shapeを比較し、行のsupportだけに投影しない。clientのlambda-formal/App/Sel rowsを指す既存出力側coordinateも本構成では値が不変なので使用できる。変更するf高座標を読んで契約自体を変えることは許さない。output equalityや任意追加constraintを入力に紛れ込ませない。

元whole parentの全source/全client、A/B、foreign continuation、principality、combined terminationはこのdomainへ縮小しない。今回の成果はこの明示したnative modelでshape-specific FN制限を除くことにある。

## 2. 原storeと実allocationを残す

A(z)=Record(a:z)、K=Fun(Y,Record(first:J,next:R))。

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

qではY,Tをlevel1のtにし、旧boundを全て残す。NL5の検査はY≤Tがt≤tになり、他のleaf levelが下がるだけ。oからY,Tはともにreachableなのでclass saturationも成立する。NL6を任意有限個mのfree-f useへ適用する。

beforeのi番目useはo_i,B_i,Y_i,J_i,R_iをlevel1へcloneし、両bound listsを全て写す。afterはo_i,B_i,J_i,R_iをclone、Y_iはshared t。C,D,Tは共通、Hは未到達でも元storeに残す。Fの意味で呼び出したかどうかに関係なく、Var fを評価するinference occurrenceごとにcloneする。

pinned Typer.scala `typeTerm` が作るclient rows/seedsは正確に次である。

| constructor | allocation / result / seed |
|---|---|
| Var monomorphic x | allocateなし、ctxの同じtypeを返す |
| Var f | 上記の実freshen、o_iを返す |
| Lit | allocateなし、同じIntType object |
| Lam(x,b) | fresh U_x:1をformalに束縛、結果Fun(U_x,type(b))、新比較なし |
| App(c,a) | fresh V_app:1、seed type(c)≤Fun(type(a),V_app)、結果V_app |
| Sel(r,l) | fresh V_sel:1、seed type(r)≤Record(l:V_sel)、結果V_sel |
| Rcd fields | 各fieldを元順序で推論、結果Record(labels,child types)、追加rowなし |

`res`はlazyなのでLam/Rcd/Var/Litに隠れたresult rowはない。通常builtin true/false/succ/add/notは固定monotype、同じPrimitive objectsを使う。builtin ifのlookupがあれば独立元schemeの実freshenを行い、そのfresh rowsと全boundsを保持する。

**LF1（levelとpublicationの分離）。** let-free clientをcaller1で推論すると、formal/App/Sel、全f clones、builtin if clonesはlevel1。型項の全leaf levelは1以下。Lamはlevelを上げず、App/Sel/Rcdも同じlevelなので構文帰納で従う。従ってclientのconstrainはwrong-level extrusionを新規に要しない。

原level2 f rowsは直接client ctxにない。clientが触るlevel1 anchors/clonesのboundsにlevel2 rowsを入れることはNL1に反するため起こらない。したがってclient replayが原high templateへ逆流して次のf fresheningの高いboundsを書き換えることはない。low anchorsがclient constraintsを蓄積しても、次のfreshenはそのlow rowで止まり同じanchorを共有する。元high templateのcloneは元の全両boundsのまま、anchorの新boundsは共有実storeの一部である。実interleavingを「毎回別の空low store」と置き換えない。□

これは有限generation/各実有限prefixの不変条件。全constrain処理の停止性をLF1だけから結論しない。

## 3. 一つのvaluation repair

beforeの全original store、全clone/client seeds、全output contractsを満たすP1-modelρを取る。τ=ρ(T)、δ=ρ(D)、c=ρ(C)。固定する値は次の全て。

* H,C,D,T、全external coordinatesとPrimitive identities。
* **全client lambda-formal U_x、全App result V_app、全Sel result V_sel。**
* builtin ifの元empty rowと、使われた全独立fresh rows。その他変更対象外の全allocated rows。

変更するのは元fのhigh rowsとそのpublication clonesだけである。FN1の同じguarded graphを使う。

```text
G* = μg.Fun(τ,Record(first:δ,next:g))
F* = Fun(c,G*)
q(Y)=t : τ
B,B_i : c        J,J_i : δ
R,R_i : G*       o,o_i : F*
```

FN1からF*≤ρ(o_i)、G*≤ρ(K_i)、G*≤ρ(R_i)。元baseにも同じ主張が成立する。ここでB_i=cへ広げることは、各expressionを無差別に下げる操作ではない。直接clientに露出するroot o_iの意味値がF*へ下がることだけが必要であり、内部domain coordinate B_iには反変方向が働く。

FN1は元Y_i≤τ、δ≤J_i、K_i≤R_iからdepth-n simulation帰納で得たもの。R_i=G*や全copy/parent equalityを仮定しない。ρには高階clientから追加したR_iのupper constraintsも含めてよい。FN1のlower-bound導出はそれらの存在で壊れない。

before/afterの同じclient構文導出を対応させ、after termの型をt'_e、beforeをt_eとする。formal/App/Selのrow名はこの対応で同じ新規identityへ対応付ける。実時刻やmemory addressの等式ではない。以下でρ'をafter valuationとする。

## 4. 高階構造帰納

**LF2（seed preservation + expression refinement）。** 任意の有限let-free derivationについて同時に:

1. ρ'は全after client seedsを満たす。
2. 各subexpression eで `⟦t'_e⟧ρ' ≤ ⟦t_e⟧ρ`。
3. lexical binding/captureの各利用は同じ元formal/external rowを使う。

証明。元resolved lexical derivationへの構造帰納。環境不変条件はmonomorphic binderのtypeの解釈がbefore/afterで同一であること。各lambda formalは元ρの値に固定したので、bodyへ入る時にこの不変条件がそのまま成立する。

**Var。** monomorphic formal/externalは同じ値、Primitiveも同じobject。free f occurrenceではFN1のF*≤ρ(o_i)。shadowed fはordinary formal case。固定builtin if occurrenceは同じfreshened graphの元値を保持し、そのboundsも同じなので型は不変。同じaliasを再使用して新f cloneを作らない。

**Lit。** 同じIntType objectで反射性。

**Lam。** d=ρ(U_x)=ρ'(U_x)を同一domainとする。bodyの帰納仮定b'≤bとFunction covarianceによりFun(d,b')≤Fun(d,b)。domainをbody/resultのrepair値へ置換しない。bodyが自由なfや別formalをcaptureしても、そのresolved rowsに同じ帰納仮定が適用される。lambda自身にはApp以前のseedを捏造しない。

**Rcd。** 同じlabel順とfield対応で、各childの帰納仮定からRecord covariance。追加allocation/seedはない。latent Function fieldもそのまま値として比較し、bodyの実行を推論上追加しない。

**App。** c',a'をafter operandの解釈、c,aをbefore、r=ρ(V_app)=ρ'(V_app)とする。帰納仮定c'≤c、a'≤a、元seed c≤Fun(a,r)がある。Functionの反変性から

```text
Fun(a,r) ≤ Fun(a',r)
c' ≤ c ≤ Fun(a,r) ≤ Fun(a',r).
```

これが同じactual Appのafter seed。App結果は旧row rを保持するのでexpression refinementは反射性。argumentが高階lambda、f自身、computed App、Record、同じformalの複数利用であっても同じ式が成立する。Functionのmonotonicityから不正にinversionを推測したのではなく、P1の定義済み反変comparisonを使っている。

**Sel。** r'≤r、元seed r≤Record(l,s)、s=旧V_selの値を固定する。推移性によりr'≤Record(l,s)。結果rowは同じsなので反射性。同じrecordに複数のselector上界を課す場合も全てのseedを個別に保つ。

各caseで子の全seedsも帰納仮定に含む。これで同時主張を得る。□

これはsyntax全体の型に対する**一方向のrefinement**である。λの負位置に新しい値を無条件代入していない。client formalを旧値に固定したことが高階/capture/aliasを保つ要点である。Appの結果をG*と固定する以前のFN proofと異なり、任意の高階contextが選んだ旧result valueを残せる。

## 5. 全旧bound、closure、同じ出力契約

**LF3（全constraint model）。** ρ'はq後の元store、全publication bounds、全client seedsと全original output requirementsを満たす。

元base/clonesはFN3の全store検査と同じ。A(t)≤BはA(τ)≤c、B≤Cはc≤c、D≤Jはδ≤δ。K≤RはG*≤G*。o.lowerはF*≤F*、o.upperはA(τ)≤cとG*≤G*。H≤Fun(C,D)、C.lower=A(t)は元値のまま。t≤tは反射。原storeに存在する他のempty rowsも元値を保持する。

client seedsはLF2、fixed external/builtin boundsは恒等。出力契約はLF2と元modelから

`⟦t'_e⟧ρ' ≤ ⟦t_e⟧ρ ≤ ⟦E⟧ρ = ⟦E⟧ρ'`。

これはFunction/Recordのfull contract比較であり、printed endpointやoutward rowの一致ではない。保つのは同じ要求、保持client rowsの意味値であり、lambda/Record等の構造的expression値はより小さくなる場合がある。

**全allocated boundsへの拡張。** nativeが保存するboundと発行するcomparisonは、元seedsからのVar/CutVar、Fun反変/result、Record first-matchの有限導出である。P1の反転/推移、P2のclosure帰納により、after全有限closureと実各有限prefixの保存boundをρ'が満たす。beforeで得たderived boundをqで写したものも、qが構造規則/variable cutと可換するためafter closureに入る。古いboundを削除して整合性を作らない。重複labelは§1のmodel境界通りであり、P2のfirst-match前提を勝手に一般化しない。□

全client結果rowsを元値に固定しても、そのrowsの下界にf由来の新しいlambda型が入る場合、LF2のApp/Record/Lam比較がその下界を保つ。上界にも旧同じrow値を使うため、別useからの共有要求を見落とさない。clientが低C/D/Tへreplayする新boundもclosure帰納に含まれ、anchorsの意味値を後から変更しない。

**LF4（有限let-free reverse coverage）。** この明示したP1-domain/context/output条件の任意有限clientについて、before可解性からafter可解性が従う。逆向きはNL6/NL7で、client新rowsに恒等、publication clonesにq_mを使う。Lam/App/Rcd/Sel型項と同時代入は可換し、output Eは固定される。従って同じ保持anchors/output要求ごとに可解性が同値である。

mは全resolved free-f occurrencesの有限数。lambdaが後で何回実行されるかとは別であり、そのruntime回数をinference freshening数へ置換しない。source syntaxにLamがあることはnative scheme generalizationを行うことではない。LF4はlocal Let-polymorphismの可解性やinterleaved新しいgeneralizationへは適用しない。

## 6. 達成した親差分と残る元義務

FNの特殊なG/Q/O文法を使わず、任意の有限let-free高階monomorphic Lam/App/Rcd/Sel/Var/Lit clientを扱った。同じfを高階引数へ渡す、lambdaから返す、captureする、複数aliasで使う、任意のcomputed calleeへ渡すことをnative structural model内で許す。元whole recursive store、実root freshening、低anchors、全output constraintsは保たれる。

これはactual source effect/whole-carrier/receipt/world/provider意味論の証明ではない。source laneはsame-code Delay/Force checkingとcomputed-callee phaseを別に供給する必要がある。nativeのmodel existenceからInt返却の純粋性やχを得ない。ReadInvokeのName-only scopeも拡張しない。

元parentに残る責務は、local Let/LetRec polymorphism、model外raw record embedding、source/native complete correspondence、source receiving/TY資格、任意のforeign/State/continuation、原A/B全量化、principal inferenceとcombined termination。LF4を全source arbitrary NL7 converseとして記録しない。

## 7. Freeze / handoff

契約と15 pinned inputsのactual SHA-256を照合し全一致。直接証拠はTyper.scalaのtypeTerm、constrain、freshenAbove。FN1/P1–P3/NLの帰属は元frozen notesの通り（本workerとprimary、reviewed scopeを維持）。本稿は本worker単著、独立査読未実施、descendants/coauthorなし。primaryのmoving carrier稿は読まず依存にしない。

Mutual TODO LF-SOURCE: primaryは元sourceのfull same-code χ/phase evidenceを供給する。falsifierはscalar結果型からargument purityを推測すること。LF-LET: native publication ownerはfresh local schemeの新constraints/clone correspondenceを証明する。LF-RECORD: governing source ownerは一意label source domainのembeddingまたは原first-matchを保つduplicate-aware証明を供給する。どれもこのpacketが実装権限を与えるTODOではない。

三stages: authentic generation/levels、構造的transport、full bound/output/親適用。190秒上限、予約全charge。Requested inherited Astra/medium、observed model/effort/duration UNKNOWN。static read/hash/文書検査のみ。tests/build/probes/compiler/implementation/network/Git/scratch/descendantsゼロ。唯一の新writeは本稿。

r1 frozen。全writes STOPPED。hashをfinal handoffに返す。


## 独立査読の受理範囲

査読対象 SHA-256 `6d67b4eea83511b3f272f8450bea39be5a308236ce4e592f5425ab9d6b885808`。`/root/astra_semantics_review` は、LF1–LF4 を明記した unique-label structural model、external-context、let-free scope で受理した。 BLOCKING/MAJOR 指摘なし。本文の独立査読前表記は producer freeze の履歴。primary の査読後変更はこの status/receipt の追記のみ。[outcome](../../tasks/agent-loop/sprints/let-free-carrier-20261024-outcome.md) に元の未完了義務を保持する。
