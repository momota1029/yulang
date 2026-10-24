# Let publication: signed copies, relative low rows, and nested freshening

LET-POLAR-RESULT-SLOT-20261024/r1. Author `/root/astra_corrected_machine`.
Candidate mathematics; independent review pending. Requested inherited Astra/medium; observed UNKNOWN.
Baseline `0a358d4972bb9e2a8b5edf9c115d0a5d302116cd`.

## 1. 元の目標と今回の到達点

P1 の unique-label regular-tree model、LF の fixed external context/output contracts、元 f の全 prepublication store を維持する。q は Y/T だけを t:1 に同定する。native source grammar に任意有限 nonrecursive Let を加えた一般 LET-POLAR-PUB は本稿では閉じない。失敗したのは coverage ではなく、signed construction の publication case である。以下では一般の極性 copy に必要な不等式を実規則から導き、nested Let が「low copy を固定する」という方針を破る最初の実 constructor を示す。既存の一段 example を全 Let theorem と再掲しない。

使用する regular tree は Primitive identity/Top/Function/unique-label Record の P1 domain のまま。Top を native syntax に追加しない。任意の model ρ に対し τ=ρ(T)、δ=ρ(D)、c=ρ(C)、

```
G* = μg.Fun(τ,Record(first:δ,next:g)),  F* = Fun(c,G*)
```

とする。FN1 は元 f とその全 ordinary clones の B/Y を広げ、J/R/o を狭める repair を既に与える。これは単一行の全 occurrences に共変 action を行う操作ではない。

## 2. LP1: actual signed-copy obligations

一回の extrude(t,ε,k) の actual polar memo を固定する。native の Function domain だけで sign を反転し、result/Record field では保持する。key は (parent,sign)、target は invocation 固定。行の名前から sign を推定しない。

parent a の新 copy c_a に必要な元 clauses は厳密に

```
ε=+: a≤c_a,   extrude(l,+,k)≤c_a   (l in a.lower at creation)
ε=-: c_a≤a,   c_a≤extrude(u,-,k)   (u in a.upper at creation).
```

copy は selected list の再帰前に memo 登録される。opposite list は copy へコピーされないが、parent の全 clauses は残る。後着 bound の replay は別 constructor であり、この displayed list のみによる証明では扱えない。

**LP1。** 一つの実 finite polar traversal で、上の各 actual new-row clauses を満たす一つの valuation が与えられた場合、その extrusion の parent links、selected lists、memo-sharing を全て満たす。さらに term action が各 leaf の実 sign に従うなら Function/Record の外側比較はその sign に従う。

証明。構造項への帰納。Function domain の逆向き比較は P1 の反変 rule、result/Record は共変 rule。variable の初回 miss は上の actual clauses を作る。memo hit は同じ c_a の値を読むので別 witness を選ばない。低 level leaf は恒等。finite registered graph の cycle は既登録 key で止まる。これは valuation の存在を証明する命題ではなく、**必要な local inequalities とそれらから得られる全 traversal の証明**である。□

一般 reverse action を LP1 に供給するには、positive/negative の selected lists だけでなく、将来保存される両 list と公開時の全 reachable graph を扱う必要がある。消える negative Y-copy y に τ を代入する場合、元 y≤T は y≤τ を与える。しかし新しい retained upper y≤U があれば τ≤U の証拠が必要である。反変 producer exposure からそのような update が生じない、または U に一貫した action があることを実 source induction で証明すべきであり、LP1 の creation-sign からは出ない。

## 3. 二つの publication を持つ authentic native history

次の original native fragment を caller1 で推論する。外側 Let も内側 Let も nonrecursive。

```
let p = lambda k.
          let a = k f in a
in {left=p, right=p}
```

これは Let を Lambda application に展開しない。Typer.scala typeLetRhs(false) は p RHS を level2、a RHS を level3 で推論する。

### 3.1 inner extrusion

k:2、f の clone o₀,B₀,Y₀,J₀,R₀:3、App result V:3。C,D,T:1 は共有。seed は

`k≤Function(o₀,V)`。

negative extrusion target2 の actual keys/copies は

```
o₀+ ↦ O:2, B₀- ↦ b:2, Y₀- ↦ y:2,
J₀+ ↦ j:2, R₀+ ↦ r:2, V- ↦ v:2.
```

K_c=Fun(y,Record(first:j,next:r)) とすると全新 clauses は

```
o₀≤O, Fun(b,K_c)≤O,
b≤B₀, b≤C, y≤Y₀, y≤T,
J₀≤j, D≤j, R₀≤r, K_c≤r,
v≤V, k≤Fun(O,v).
```

parent links は extrude の直接 list insertion。k.lower は空なので rewrite の追加 replay はない。R₀+ は bounds 再帰前に memo に入り、K_c の再訪は同じ y,j,r を使う。原 f clone の全 lists は別に残る。

a scheme の boundary は2、body Var a の caller は2。実 freshen は V:3 を V_a:2 へ写し、V_a.lower=[v]。v:2 では止まる。p RHS result は Fun(k,V_a)。ここまでが先行 one-Let note と同じ source constructors を **実際に一段高い lexical level** で適用したもの。anchors C,D,T を level2 に動かしてはいない。

### 3.2 outer publication が変えるもの

p の boundary は1。root Fun(k,V_a) から reachable な level2 graph はちょうど

`k,V_a,O,b,y,j,r,v`。

O.lower の Fun(b,K_c)、b.upper=C、y.upper=T、j.lower=D、r.lower=K_c、V_a.lower=v、k.upper=Fun(O,v) を辿る。o₀/B₀/Y₀/J₀/R₀/V は逆向き parent links の parent 側にあり、この root から到達しない。全 old rows は store から消さない。

各 Var p は one-memo freshenAbove(1,Fun(k,V_a)) を caller1 で実行し、上の **8 rows 全て**を別添字 i∈{L,R} の level1 rows に複写する。両 bound lists を写し、C,D,T は同じ元 rows。返却型は Fun(k_i,V_ai)。外側 Record に隠れた result row はない。

after q では f 内の Y₀ が共有 t:1 となる。inner negative extrusion はこの leaf をコピーしないので y:2 は存在しない。従って p publication の high graph は7 rows、各 use も7 rows。before y_L,y_R に対応する独立 after rows はなく、両方の K_ci に共通 t が現れる。

**LP2（実際の first failed publication case）。** 「polar copy の target が caller level だから low として以後全 uses に固定する」という invariant は、上の outer `freshenAbove(1,...)` で偽になる。y は inner operation に対して low=2 だが、outer publication に対して high=2>1。actual before uses は y_L,y_R を独立に持つ一方、after はどちらも t を使う。low/high は publication boundary に相対的でなければならない。

証明は直上の actual traversal と NL4。新しい source restriction、row owner、SCC 仮定はない。□

## 4. 独立利用を潰さない countervaluation と限定された repair

この first failed case が単なる名前の問題でないことを全 bound model で確認する。τ=Top、δ=Int、c=Record(a:Top)、H=Fun(c,Int) とする。base と inner original f clone には FN の G*,F*、Y₀=Top,B₀=c,J₀=Int,R₀=G*,o₀=F* を置く。inner copy に y=Int、b=c、j=Int、r=G_Int=μg.Fun(Int,Record(first:Int,next:g))、O=Fun(c,G_Int)、v=V=V_a=Int、k=Fun(O,Int) を置く。

Y₀=Top なので y≤Y₀、G*≤G_Int なので R₀≤r、F*≤O。残りは反射/元 anchor clauses。全 inner old rows を含めて成立する。

outer clone L は y_L=Int、r_L=G_Int、j_L=Int、b_L=c、O_L=Fun(c,G_Int)、v_L=V_aL=Int、k_L=Fun(O_L,Int)。clone R は y_R=Bool、r_R=G_Bool、j_R=Int、b_R=c、O_R=Fun(c,G_Bool)、v_R=V_aR=Int、k_R=Fun(O_R,Int)。各 clone が持つのはコピーされた selected graph の clauses であり、元 parent R₀≤r_i という新 clause はない。y_i≤T、K_ci≤r_i 等は成立する。Primitive Int/Bool は異なる object のまま。

従って before には y_L≠y_R の一つの同時 model が実在する。y_L,y_R の値を after の t にそのまま保存する作用は不可能。ただし **coverage の反例ではない**。

実際、この graph には全使用を一度に扱う repair がある。t=Top を固定し、消えた各 y_i を term 内で t に置き換える。他の clone rows k_i,O_i,b_i,j_i,r_i,v_i,V_ai は上の旧値に固定する。K'_ci=Fun(Top,Record(first:j_i,next:r_i))≤K_ci なので K'_ci≤r_i と Fun(b_i,K'_ci)≤O_i が成立する。after inner graph は同じ検査、元 f high graph は FN repair。root Fun(k_i,V_ai) は **等しい**まま。任意有限個の同じ publication uses に同じ式を使え、共有 t を利用ごとに変えない。

この検査が除くのは「独立 y_i が違えば shared t は不可能」という誤った反例候補。一般の Let client が y_i/j_i/r_i に後着 constraints を加えた場合まで、この selected graph の検査を適用したとは主張しない。

## 5. 一般 signed relation を閉じる際の正確な停止箇所

一般構成には、各 publication b ごとに actual rooted graph を保持し、同じ行が別 b では high/low のどちらにもなれる relation が必要。全 actual uses の high clones と共有 low の一つの valuation を同時に作る。LP2 によって単一 permanent-low classification は撤回される。

試した stronger invariant は、producer root の正 exposure、Function domain 反転、selected lower/upper traversal によって、消える Y 系 copy の全 retained appearances を負として追うものだった。syntax の Var f/Record/Lambda/App で double sign flip を数えるだけでは、**freshenAbove が両 bound lists を辿る** case が閉じない。native の ordinary replay は、その後さらに両側の別 provenance を合成する。

固定 f の internal clauses だけでも、o.lower=Fun(B,K) と o.upper=Fun(A(Y),R)、B.lower=A(Y) を全部保存する必要がある。source expression の outward type が下がるという LF2 は、これら全 registered rows の同時 action を与えない。LP1 は selected traversal を閉じるが full freshening は selected traversal ではない。LP2 の authentic trace では、この違いが newly allocated y の outer cloneという具体的 constructor に現れる。

未証明の最小一般化は、各 **actual client-added bound** の constructor origin に沿う signed transport と、各 freshening snapshot の両 lists に対するその自然性を同時帰納で証明すること。特に y≤U が later replay で保存された時、afterで y が消えるなら τ≤U' を同じ whole action が供給する必要がある。供給できない case を推測で「producer は正だから不可能」としない。本稿はその update-origin induction を完成していないし、そのような incompatible update が actual source から到達する反例も得ていない。

したがって full LET-POLAR-PUB、元 all-client coverage/principality は OPEN。LP1 は general polar constructor obligations、LP2 は generalization 境界の誤った不変条件への authentic counterexample。nested graph repair はそれを source coverage の反例と誤判定することを防ぐ。元 LF4、P1–P3、FN1、NL4 は各受理済み範囲で維持する。primary の moving source/EI note は未読・未依存。native regular model から source carrier/world/receipt truth、T/Y資格、termination は導かない。

## 6. Handoff と停止

契約 SHA-256 `f9866914a67be89a28e1e42114d81935b9cd0f97ab8d2be5d6033ecc7ae9d1b9` と27 pinned input hashesを全件照合、一致。直接使用：Typer.scala typeLetRhs/typeTerm/constrain/extrude/freshenAbove、NL3–NL4、LF1–LF4、FN1、P1–P3、先行 nonrecursive-let-client-coverage §§1–5（SHA `fc7007497df333bb260cf1806eff1672a4a6d07af8fa3f987c1bb99b43c5d16d`、author `/root/astra_scoped_join`）。本稿単著、独立認証なし。

結果を親へ適用：source signed proof に必要な selected polar constructorを明示し、nested actual publicationで永久low対応を排除。先行未完了 field を全体定理と改称していない。次の owner は original native source/replay signed-update induction。最小 falsifier は actual source-generated later upperが shared τ action を破る全store model。新しい semantics/lease/implementation依頼はない。

三段階：signed constructor、nested authentic history、全bound検査と親適用。190秒予約、延長なし。requested Astra/medium、observed model/effort/elapsed UNKNOWN。static reads/hashと本稿のみ。tests/build/probes/compiler/network/Git/scratch/descendantsゼロ。新規pathは本稿だけ。**all writes STOPPED at freeze**。最終 hash は外部handoff。

## 独立査読記録

`/root/astra_semantics_review` による current80sec の独立査読は、本稿の明記した範囲で BLOCKING/MAJOR なし。査読対象 SHA-256 `c6259022dc8187efc1f1da7ec6bda9440e61b949f32593c5cfb9e866eaed4aec`。数学本文は変更せず、この receipt のみを追加した。全 Let theorem、元全 target inclusion、全 source/native 対応は未完。[統合記録](../../tasks/agent-loop/sprints/let-polar-result-slot-20261024-outcome.md)に正確な受理範囲と残項を保持する。
