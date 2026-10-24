# nonrecursive Let の実 extrusion と残る一様輸送義務

LOCAL-LET-COMPUTED-RESULT-20261024/r1。Author `/root/astra_scoped_join`。独立査読前。Contract SHA-256 `f3a1ce51332e32d53310944ef8e44a9fde1465b843b882e2f7a92eaabac84dd2`。Baseline `f6b4dcd810f0e0fa0aea70128d99e6a0810c5bb2`。

**結論の範囲。** 全finite nonrecursive Let extensionは未証明。本稿は実level上昇/extrusion/fresheningを持つ一つのauthentic higher-order clientについてbefore/after全boundを構成し、単純なrow対応が失うcoordinateを特定する。これはapproved intrusionの反例でも、全Let reverse-coverageの証明でもない。

## 1. 固定する原storeとclient

P3/LFの全original prepublication storeを保持する。H,C,D,Tはlevel1。o,B,Y,J,Rはlevel2。A(z)=Record(a:z)、K=Fun(Y,Record(first:J,next:R))。元boundsはH≤Fun(C,D)、Fun(B,K)≤o、o≤Fun(A(Y),R)、A(Y)≤B≤C、Y≤T、D≤J、K≤R、A(T)≤C。全他listは空。qはY/Tだけをlevel1のtへ写し全旧boundsを残す。NL5/class saturationは既存P3/LFで成立する。

実clientをcaller1で次とする。

```text
lambda k.
  let a = k f
  in a
```

letはnonrecursive。`Lam`のkはmonomorphic row k:1。元`typeLetRhs(false,a,...)`はRHSをlevel2で推論する。f lookupは元boundary1 schemeを実freshenし、o_i,B_i,Y_i,J_i,R_iをlevel2で作る。C,D,Tはそのまま。RHS AppはV:2を作り

`k ≤ Fun(o_i,V)`

を発行する。これはlevel1のkへlevel2構造を入れるので、実negative extrusionが必要である。letをlambda applicationへ文字列展開してこの境界を消さない。

## 2. beforeの全新規allocationsとbound

extrude(Fun(o_i,V),negative,target1)は空polar memoで始まる。Function domainで極性が反転する。

| parent/key | actual new row | selected copied side |
|---|---|---|
| o_i positive | O:1 | o_i.lower=Fun(B_i,K_i) |
| B_i negative | b:1 | B_i.upper=C |
| Y_i negative | y:1 | Y_i.upper=T |
| J_i positive | j:1 | J_i.lower=D |
| R_i positive | r:1 | R_i.lower=K_i |
| V negative | v:1 | V.upper=empty |

K_iは構造termでrowではない。R_i positiveは再帰前にmemo登録される。R_i.lowerのK_iを降りる時は既存Y_i−,J_i+,R_i+のmemoを使う。K_c=Fun(y,Record(first:j,next:r))とする。exact追加clausesは

```text
o_i ≤ O                 Fun(b,K_c) ≤ O
b ≤ B_i, b ≤ C          y ≤ Y_i, y ≤ T
J_i ≤ j, D ≤ j          R_i ≤ r, K_c ≤ r
v ≤ V                   k ≤ Fun(O,v)
```

全original clone clausesも残す。新copyのselected lists以外は空。k.lowerは空なので最後のrewriteから追加replayはない。parentへのone-sided linksは元extrudeの直接list挿入であり、それ自体を別constrain呼出しとして数えない。上表以外のcopyはない。

RHS resultはV。aのschemeはboundary1、root V:2。body `Var a`はcaller1でfreshenAbove(1,V)しV_a:1を一個作る。V.lower=[v]なのでV_a.lower=[v]、upperは空。vはlowで固定される。結果client型はFun(k,V_a)。hidden result rowはない。

この具体的履歴は有限である。polar memoの6entries、有限structure traversal、空k.lower、最後の一row fresheningで尽くされる。一般native solverの停止性はここから推定しない。

## 3. afterのauthentic traceと失われるcoordinate

q後fのlevel2 fresh useはo_i,B_i,J_i,R_iを作り、Y_iは作らず共通tを使う。same clientが同じRHS App seed k≤Fun(o_i,V)を発行する。negative extrusionはO,b,j,r,vを作るが、t.level=1なのでY側はearly returnとなる。**yのcopy allocationが消える**。

K'_c=Fun(t,Record(first:j,next:r))。全追加clausesは§2のy関連を除き、K_cをK'_cに変えたもの。V_aのfresheningは同じ一row。元H,C,D,T、k、V、V_aと他copiesを同じ役割で対応できるが、beforeのyだけはafterのtに対応する。

従って「f由来high rowsだけrepairし、それ以外の全old allocationの値を同じ対応先に保持する」というLFの単純延長は一般には定義できない。yは本当に新しく生成されたlow rowであり、ρ(y)がρ(T)と等しいという制約はない。

これはbefore modelでρ(y)=Int、ρ(T)=Topを選べるため具体的である。原/cloneのY_i=Int、B_i=A(Int)、J_i=Int、R_i=G_I=μg.Fun(Int,Record(first:Int,next:g))、o_i=Fun(A(Int),G_I)。anchorsはC=A(Top)、D=Int、H=Fun(C,Int)。b=A(Int)、j=Int、r=G_I、O=Fun(A(Int),G_I)、v=V=V_a=Int、k=Fun(O,Int)とする。元baseにも同じInt系値を置けば全§1–2 boundsを満たす。Primitive identitiesは不変。このyの値をtへ保つことはTop=Intを要求するので不可能。

これは**対応関数/証明候補の失敗**であり、after可解性の否定ではない。yを固定外部inputとして新しいclient equalityを発行したわけでもない。次節で実際にafter modelを構成する。

## 4. この実Let clientの全bound repair

任意のbefore P1 modelρを取り、τ=ρ(T)、δ=ρ(D)、c=ρ(C)とする。元anchorsとk,V,V_a,O,b,j,r,vの値は保持する。yはafterに存在しないので独立保持しない。元highとf cloneはFN1の

```text
G* = μg.Fun(τ,Record(first:δ,next:g))
F* = Fun(c,G*)
B,B_i=c; Y,Y_i→t=τ; J,J_i=δ; R,R_i=G*; o,o_i=F*
```

でrepairする。

元clausesからρ(y)≤ρ(Y_i)≤τ、δ≤ρ(j)、ρ(b)≤c、K_c≤ρ(r)、Fun(ρ(b),K_c)≤ρ(O)。FN1と同じdepth-n simulation帰納をこのcopy graphへ適用すると

`G*≤ρ(r), G*≤ρ(K_c), F*≤ρ(O)`

を得る。最後はFunction反変domainのρ(b)≤cを使う。これはcopyをfull original F/Gと同一視したものではなく、上記selected clausesからの別guarded比較である。

全after追加clausesを検査する。

| clause | supplier |
|---|---|
| o_i≤O | F*≤ρ(O) |
| b≤B_i、b≤C | ρ(b)≤c |
| J_i≤j、D≤j | δ≤ρ(j) |
| R_i≤r | G*≤ρ(r) |
| K'_c≤r | τ≥ρ(y)よりFun(τ,Record(j,r))≤ρ(K_c)≤ρ(r) |
| Fun(b,K'_c)≤O | 同じresult covarianceと元Fun(b,K_c)≤O |
| v≤V、v≤V_a | 元値を保持 |
| k≤Fun(O,v) | 元値を保持 |

元store/high/clonesはFN3と同じ全bound検査で成立する。従ってafter全seedsと全実stored boundsを満たす。P1/P2のtransitivity、Function/Record inversionで全closureにもmodelを与え、Badを排除する。client結果Fun(k,V_a)は**同じ意味値**なので、それに対する元fixed full output contractを全て保持する。

このtraceは、新extrusionを無視してLFを再掲したものではない。roleごとの実polarityと、存在しなくなるy、元new-low-copyのselected boundsを使ってモデルを修復した。

## 5. 全nonrecursive Letへの二つの試みと正確な未完了field

### A. RHSの構造帰納をそのまま一般化する試み

LF2は一つのRHSのsyntax resultを下位型にする。しかしLetはそのresult値だけでなく、実時点の全reachable bound graphを保存して後にfreshenする。§3では実graphのlow row yがafterには存在しない。従って全non-f rowをold値で恒等対応するLFのinvariantは、そのままではLetの保存graphへ適用できない。§4のlocal repairはこの特定selected graphに対する補修である。

### B. NL4/NL6だけで全future useへ輸送する試み

NL4は一つの実snapshotのlow/high partitionsと全bound copyingを正確に記述する。NL6には両storeのlevel invariant、同じroot-reachable q-class saturationと全clause写像が必要。新しいLet RHSが作るpolar copiesとその後のfresheningについて、元q(Y)=q(T)だけからその全snapshot correspondenceは与えられない。afterで消えるyと、後でそのrowを共有する各scheme/bodyの対応を別途構成しなければならない。NL7の逆向き一般化でそれを置き換えない。

**最初の未証明fieldは LET-POLAR-PUB。** 任意のfinite nonrecursive Let derivationの各実publication snapshotについて、before/afterの全registered rows、polar extrusion genealogy、low shared coordinates、high cloned coordinatesを一つのdependent correspondenceで結び、

1. 全旧boundとselected-sideコピーを保つmodel action、
2. 同じlow coordinateを参照する全future useで一致するaction、
3. 各実freshenAboveへの全bound transportとroot refinement、
4. 元fixed output contractsの保持

を同時に与える必要がある。特に「f-source rootは下位型になる」というsyntax事実だけで、内部Y/B座標とその極性copies全ての作用は決まらない。

本稿はこのfieldを一般に証明していない。逆に全Let extensionをrefuteするauthentic mismatchも得ていない。§3のcountervaluationは誤った恒等row方針だけをrefuteし、§4が同じclientのafter解を構成するため、これをsource-qualified反例として扱うことはできない。

## 6. 元parentへの適用と次のboundary

達成したことは、nonrecursive Letで実際に増える「低いpolar copyを含むRHS graph」の一例について、元全storeを残したまま合法なpublicationと逆modelを構成したこと。全client proofの新しい責務をLET-POLAR-PUBに具体化し、単純なLF再利用とNL7 converseの二経路を排除した。

次のnative ownerは§2のcopy-interface guarded comparisonを、任意のactual polar graphと複数schemeの共有へ拡張する必要がある。成功条件は新しいlowcopyのsemantic actionを全alias/useで一つに決めて全selected boundsを証明すること。falsifierは同じshared rowにuseごとに別repairを割り当てるか、消えるrowを外部coordinateと同一視すること。

元whole sourceのA/B、full call/effect/current-world/provider、source receiving/TY資格、principality/terminationは未完了のまま。primaryのcomputed-result source laneは別責務であり、本稿のnativeモデルからcarrier/receipt truthを得ない。

## 7. Frozen handoff

契約と20 pinned inputsのactual SHA-256を照合し全一致。TyperのtypeLetRhs(false)、typeTerm Lam/App/Var、extrudeのpolar selected bounds、freshenAboveを原ownerとして使用。LF/FN/P1の既存証明は各reviewed scopeだけ再利用。本稿は本worker単著、独立査読前。primaryのmoving source稿は読まず依存にしない。

Outcome: bounded actual native construction + precise remaining premise、全Let theoremはOPEN。Mutual TODO LET-POLAR-PUBは上記native ownerへ、COMPUTED-SOURCEはprimaryの元source result constructor ownerへ。190秒/3stages予約、延長なし。Requested inherited Astra/medium、observed model/effort/duration UNKNOWN。

static reads/hash/文書検査のみ。tests/build/probes/compiler/network/Git/scratch/descendantsゼロ。唯一のnew writeは本稿。r1 frozen、全writes STOPPED。hashはfinal messageに返す。
