# 原再帰例の全 comparison closure を満たす具体的モデル

ACTUAL-REPLAY-MODEL-20261024/r1。著者 `/root`。状態: NM1–NM3 は明記した原有限区間について独立査読で受理。全体命題は OPEN。
Baseline `3f04454825c5679cfc43e77786cd018e629ee201`。

## 1. 埋める前提

[GE6](2026-10-24-copy-genealogy-history-erasure.md) は、実コピーの系譜を消す ε と、一つの有限 closure C(Γ) のモデル ρ から、全 cut に同じ valuation を与える。この ρ を原 source の一例について具体的に構成する。Γ のモデルを置くだけで済ませず、C(Γ) の全規則に対する不変条件を証明する。

```
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first=h x, next=f {a=y}}
  in f
in top
```

区間は空 bounds から f の再帰完成までで、最初の `in f` の freshening の直前に終わる。[実 native 導出](2026-10-24-birth-level-extrusion-redundancy.md) §2 の全 seeds と store を用いる。新しい annotation、client comparison、一般化後の使用は追加しない。外側 h の source membership は本稿の algebraic model の仮定ではない。

## 2. 全変数、seeds、消去

ordinary source rows は H₁,o₂,B₂,Y₂,J₂,R₂ の六個。K は fresh row ではなく `Fun(Y,Record(first:J,next:R))` という有限構造 term である。実 builtin `if` の初期変数 v_if を Typer の全 allocated store に数える場合、その bounds は空であり本 source は参照しない。これにも後で値を与える。他にこの区間の ordinary allocation はない。`typeTerm` の `res` は lazy なので Lambda/Name/Record/Let に隠れた result row はない。

初期 bounds はすべて空、外側からの seeds は正確に次の三個である。

```
γh : H ≤ Fun(B,J)
γr : o ≤ Fun(Record(a:Y),R)
γf : Fun(B,K) ≤ o
```

H 側 extrusion は C₁↦B₂ と D₁↦J₂、後着 argument replay は T₁↦Y₂ を作る。ε は C↦B,D↦J,T↦Y、六つの base と v_if 上では恒等。Γ は上の三 seeds そのものである。`Record(a:Y)≤B`、`K≤R`、`Record(a:Y)≤C` は derived request なので Γ に追加しない。

GE2 の有限集合 T はこの Γ の endpoint subterms と base rows から成る。T の Record syntax は `a` の一 field と、`first,next` の二 fields のみで、どちらにも重複 label はない。T は variable bounds や後述の recursive tree を展開して作る集合ではない。

## 3. 木と valuation の具体的構成

ここで用いる D は、Primitive の実 object identity、二つの ordered children を持つ Function、有限 ordered labeled children を持つ Record からなる guarded regular tree の bisimilarity classes である。Record の labels は各 node 内で一意とする。finite constructor graph の unfolding でこれらを表せる。bisimilarity は同じ root constructor、同じ Primitive identity または同じ ordered labels、および対応 children の関係を要求する最大の関係である。

この定義から、bisimilarity は反射・対称・推移的である。反射関係は bisimulation、逆関係も bisimulation、二つの bisimulation の関係合成も同じ root と対応 children を保つため bisimulation になる。Function/Record の root を一段見ることで、対応 children の bisimilarity も得られる。ここで使う inversion はこの木の**等しさ**の性質である。

I を元 Typer の一つの `IntType` object とする。j は D の任意の閉じた guarded regular tree とする。未解決 native variable や自由な source effect/receipt は j に含めない。具体的な存在証人には j=I を選べる。j を固定して、次の有限 graph を作る。

```
A = Record(a:I)
G = μg. Fun(I,Record(first:j,next:g))
```

G の self-edge は Function と Record の constructor を通る。j の graph と新しい二つの constructor nodes を合わせた有限 graph の unfolding が G を与える。従って guardedness と regularity は、再帰方程式の可解性を別途仮定せずに得られる。

base valuation は次の通りである。

| row / structural term | interpretation |
| --- | --- |
| H | Fun(A,j) |
| o | Fun(A,G) |
| B | A |
| Y | I |
| J | j |
| R | G |
| K (row ではない) | Fun(I,Record(first:j,next:G)) = G |
| v_if (含める場合) | I |

最後の K の等式は G の一段 unfolding と bisimilarity による。finite syntax term の解釈は、variable leaf に表の値を入れ、構造 constructor をそのまま残す。循環 bounds をこの解釈手続で再帰展開しない。

## 4. 全 closure の成立

### 定理 NM1（全 C(Γ) の equality invariant）

任意の `(s,t)∈C(Γ)` について `⟦s⟧ρ ≈ ⟦t⟧ρ`。

証明。最小有限 closure の追加順序への帰納を行う。

* Seed γh の両辺は Fun(A,j)。γr の両辺は Fun(A,G)。γf の左辺は Fun(A,⟦K⟧ρ)≈Fun(A,G)、右辺も Fun(A,G)。すべて成立する。
* VarId は同じ variable の同じ解釈である。v_if を含めても同様。
* CutVar の二前提は `⟦s⟧≈ρ(a)` と `ρ(a)≈⟦t⟧`。bisimilarity の推移性により結論を得る。
* Fun の前提を一段反転すると、domain 同士と result 同士が bisimilar。domain の結論は逆向きだが bisimilarity は対称なので成立する。
* Record の前提を一段反転すると、ordered labels と対応 children が一致する。T の Record labels は一意なので、元 native の `first(fs,label)` はちょうどその対応 child を選ぶ。従って結論も bisimilar。

これで closure の全規則を尽くす。循環する R の bounds に対する well-founded unfolding は用いない。□

### 系 NM2（この closure に Bad はない）

証明。variable endpoint を持たない Bad comparison を仮定する。異なる Function/Record/Primitive heads は、その syntax heads を解釈後も保持するため bisimilar にならない。異なる Primitive object identities も同じである。Record の missing field は、bisimilarity に必要な同じ label list と矛盾する。すべて NM1 に反する。物理 identity fast path が分解を省略するかどうかは使っていない。この T に重複 labels はなく、GE の overapproximation が本例に偽の Bad を作ることもない。□

NM1 は任意の subtyping preorder の Function monotonicity から反転を推定したものではない。D 上の equality preorder 自体が C のモデルを与える。また D の bisimilarity を同一視し reflexivity を満たす任意の native structural preorder では、同じ ρ が C の全 comparisons を満たす。これで GE6 が要求する **C 全体のモデル**を実際に供給した。equality preorder を Yulang の全 subtype 意味論として採用する変更は含まない。

## 5. 実 store と全 cut への適用

ρ̂=ρ∘ε と置く。C=A,D=j,T=I が同時に定まり、元 base values は変わらない。全 stored clauses を列挙すると次の同じ両辺になる。

| actual stored clause | 両 endpoint の解釈 |
| --- | --- |
| H≤Fun(C,D) | Fun(A,j) |
| Fun(B,K)≤o | Fun(A,G) |
| o≤Fun(Record(a:Y),R) | Fun(A,G) |
| Record(a:Y)≤B | A |
| B≤C | A |
| Y≤T | I |
| D≤J | j |
| K≤R | G |
| Record(a:T)≤C | A |

この表以外の lower/upper list は空である。GE4/NM1 は保存済み clauses だけでなく、その前の original/replayed/rewritten requests 全てを覆う。例えば `Record(a:Y)≤B` は γf,γr の CutVar(o) と Fun から得られ、B≤C は消去後 VarId(B)。後着 `Record(a:Y)≤C`、その rewrite `Record(a:T)≤C`、実 Y≤T link はすべて同じ valuation で成立する。

### 系 NM3（具体例の simultaneous lift と比較 failure の排除）

本区間では、実 parent/copy pairs の任意の部分集合を全旧 clauses を残して等置しても、ρ̂ は全 bound、全 cut demand、選んだ全 equalities を同時に満たす。finite actual comparison failure は起きない。

証明。NM1 を GE6、NM2 を GE5 に適用する。parent/copy 上の値は ε により等しく、quotient へ一意に降りる。等置の間に valuation を選び直さない。□

比較 failure の排除は、無限 allocation を含む実 solver の termination 証明ではない。本例の普通の pre-publication 実履歴が有限なことは既存の §2.1 の全手順列で独立に示されている。intrusion の source 資格もこの model の存在から導かない。

## 6. source と公開への正確な境界

[NR2](2026-10-24-name-call-recursive-closure-membership.md) は A=Record(a:Int)、y:Int の actual source family を構成する。そこでは h の genuine advertised result projection は B_sem である。本稿の任意 j と B_sem は別の座標である。もし actual projection map が B_sem を j に送り、Function/Record を同じ原 interface の全 field とともに運ぶなら、表の J=j をその projection の像として読める。この map の存在を、native equation の成立から導くことはしない。特に j=I の concrete native witness だけで、任意の外部 h の実返却値を Int と扱えない。

NM3 は原有限区間に関する GE6 の抽象 model premise を除く。一方、full source/native correspondence は、同じ occurrence、provider、world、receipt、全 pending/future を持つ actual source diagram を要求する。source scope に従う joint strategy、公開後の各独立使用、全原 A/B と principality、combined termination は本稿からは結論しない。

publication については [NL5–NL7](2026-10-24-native-level-closure-and-publication.md) の level 閉包と class 飽和性が別途必要である。例えば B₂=C₁ だけの等置は B.lower の Y₂ を level1 row の下に残す。ρ̂ がこれを満たすことと、NL5 の level 条件が成立することは別である。この具体的差を消して publication の仮定を落とさない。

## 7. 固定入力と receipt

契約 [ACTUAL-REPLAY-MODEL](../../tasks/agent-loop/sprints/actual-replay-model-20261024.md)、SHA-256 `75351a3ec3c09bded62b2baa2da81c62855e3cc5c8c8d155ddc8d10a00965105` に直接入力を固定する。元 Typer の allocation、全 seeds、Function/Record 比較、extrusion、初期 builtin を読み、数学的帰納と finite graph 構成を行った。実装変更、test、build、compiler run はない。独立査読結果は同 sprint の outcome に記録する。

独立査読入力 SHA-256 `3c4332c1968681fbb23cf8a0eb401a7963b92242e5544fbf5deb4a6afda01306`。査読後の変更は status とこの receipt のみ。[outcome](../../tasks/agent-loop/sprints/actual-replay-model-20261024-outcome.md) に受理範囲を固定する。
