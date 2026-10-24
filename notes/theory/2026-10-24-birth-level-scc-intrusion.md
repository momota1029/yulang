# 生成レベル別 SCC と局所等置の保存

BIRTH-LEVEL-SCC-20261024/r1。著者 `/root/astra_corrected_machine`。
Baseline `d861740dddabcd3dc4d898ff00548cd52d55b119`。
状態: 新規則の graph 部分、BL4 と以下に限定した native 履歴は独立査読で受理された。BL5 の全域性には MAJOR 指摘があり、producer 停止後に primary が元の入力領域を保持する拡張条件を追加した。この修正版 BL5 の再独立査読は行っていない。全言語・主型性・combined inference 停止の閉包ではない。固定版と修正範囲は [sprint outcome](../../tasks/agent-loop/sprints/birth-level-scc-20261024-outcome.md) に記録する。

## 1. 対象、依存、元の量化

契約 `tasks/agent-loop/sprints/birth-level-scc-20261024.md` SHA256 `fe5720d7e910e6bce2df7d9117fc2eb0cc0e12f7134fadc3ed73a3fecd83af35`。新 authority は同日 design §2–4。旧 source-preservation §1,§5 の「全 lawful source derivation、必要な全有限 joint use、元の type/event telescope と完全 Call を保つ」量化を維持する。旧 F/G を跨レベルで資格ありとする前提だけは撤回済みである。

以下 Q は旧 `2026-10-24-value-scc-qualification-proof.md`、P は `2026-10-13-intrusion-source-preservation-proof.md`、N は `2026-10-13-nested-live-root-generalization-derivation.md`、O は `2026-10-12-odd-even-parent-copy-scc-derivation.md`、SG は `2026-10-08-source-generalize-definition-and-proof.md`。依存の正確な hash 表は末尾。

## 2. 誘導された経路と更新

有限 resolved source incidence graph G=(V,Ref)、不変 b:V→N を固定する。`G_k=G[V_k]`, `V_k=b^{-1}(k)` とする。`u ⇒_k v` は G の有限道で全頂点の birth が k のもの。長さ0を許す。`u ~_k v` は両方向の ⇒_k とする。

**BL1 (path/partition).** `⇒_k` は G_k の到達性に等しく、`~_k` は V_k の一意な SCC 分割である。
証明: 道の各辺は両端が V_k なので Ref_k に属し、逆も同じ。反射・対称・推移は0長道と連結から従い、最大性と condensation の非循環性は Q.S2 を G_k に適用する。端点だけの検査は十分でない。例えば b(u)=b(v)=1,b(w)=2、辺 u→w,w→v,v→u では全 graph の u,v は同一 SCC だが G_1 では異なる。これは算法 shortcut の反例であり source typing 反例ではない。□

**BL2 (exact update).** 新辺 a→b で birth が異なる場合、全 G_k の SCC は不変。同じ k の場合、旧成分 A,B について B⇒A がなければ不変、あれば正確に `Reach(B)∩Pred(A)` を merge する。証明: 異レベル辺はどの Ref_k にも入らない。同レベル辺には Q.S3 の新辺を一回使う cycle の証明をそのまま適用する。他レベルの成分は変わらない。新頂点の登録はその birth の singleton 追加と incident edge の逐次追加に分解できる。既存 b を書換える操作はない。□

**BL3 (stable labels).** label は `(k, representative)` とし、最小の immutable Value identity を代表に選ぶ。辺追加で非 merge 成分の label は不変、merge 成分はその最小代表へ canonicalize する。旧 label は union/find handle としてのみ保持し、その現在代表を比較する。証明: 非 merge 類の集合は同じなので最小値も同じ。merge は類の和集合であり代表も一意。挿入順序に依らない最終分割と代表を得る。ただし merge した各旧 label の数値が永遠に等しいとは主張しない。birth 自体と Value identity は常に不変。型 quotient の操作はこの証明の入力を書換えない。□

ここでは Value identity に固定された全順序を一つ取る。この代表選択は数学的な表示例であり、実装での encoding や union/find 方針を採用する決定ではない。

helper は b の定義域外である。まず各 semantic incidence u→v を確定し、その両端が同じ k のものだけを残す。これを helper path へ展開する場合、各 helper-only path の縮約がちょうど残した一辺になり、逆に各一辺が展開可能、という Q.S1 の双方向条件を要求する。この条件で道を semantic vertex ごとに分割する帰納が BL1 の到達性を保存する。helper に便宜的 k を与えて先に filter する方法を正当化しない。

実 occurrence e の全 signed pair list P_e を保持し、資格を `b(origin)=b(receiver)=k ∧ origin~_k receiver` とする。Q.S5 の初回 activation と公平な再検査を各 level に適用すると最終発行集合は正確に `{(c,p) | e qualifies, (c,p,...)∈P_e}`。cross-level reference は元 Ref に残る。固定 n_k 頂点の成分 merge は合計 `Σ_k max(n_k−1,0)` 以下、pair 発行は `Σ_e|P_e|` 以下。これは Q.S6 の有限集合 bound であり新しい型・event を作る全 propagation の停止定理ではない。Q.S4 の初回 seal 正確性は各 G_k の正しい表現について再利用できるが、旧コードが birth filter を実装済みとはしない。

## 3. extrusion と等置の二方向を正確に区別する

空の polar memo、有限 store、有限 structural tree/variable cycle という Q.E1 の前提で一回の extrusion は停止し、全返却変数は target level 以下になる。positive は `t≤extrude(t,+)`、negative は `extrude(t,−)≤t`。Function 反変位置の polarity flip、Record 全 field、variable の直接 link と memo を用いる P.§4 の証明を再利用する。

**BL4 (local equality correspondence).** 同じ cut の旧 store と元 demand を満たす valuation ρ ごとに、各実 copy c の値を実 parent p の ρ(p) とする同時 extension ρ* が存在する。旧値を変えず、今回追加された全 bounds と rewrite demand と全実 pair 等式を満たす。逆に rewrite store とその任意の qualified pair 等式の解は元 demand を満たす。
証明: 正方向は P.§4 の同時置換。選択 bound に今回他 polarity が追加した copy が含まれても双方が同じ parent 値になる。cycle は variable leaf の同時置換で扱い無限展開しない。逆方向は上の一方向近似と transitivity。資格がどれであるかは正方向の構成に影響しない。全 clause を保持する型 quotient は Q.S7 の全単射でこの equality-constrained store と正確に対応する。□

従って「extrusion があるので親子等置で元 demand を表せる」は、この同じ cut・元 demand の valuation という量化では成立する。旧 extruded store の任意の解を保持するという意味ではない。また、別々の use frame の存在 witness を共有 copy 一個へ置く選択はこの定理の量化外である。

## 4. nested f/g の全 original native 履歴への適用

対象は N.§4 の原 Simple-sub AST:

```
let rec f = lambda x.
  let g = lambda y. (lambda z.y)(f y)
  in {a=succ(g 0), b=g true}
in f
```

F の birth=1、G の birth=2。実参照 F→G,G→F は保持するが、BL1 によって G/F event は非資格。以下は元 Scala の Value Function/Record fragment の履歴であり complete Yulang Call/effect 実装の履歴とは区別する。

1. boundary0 で o,A:level1。g initializer で B,Z,R,S:level2。`o≤B→R` が唯一の wrong-level demand。
2. negative extrusion は C,D:level1 を作り B≤C,D≤R,o≤C→D。event `(G,F)` の全 pairs `(C,B,+),(D,R,−)` は非資格なので追加等式なし。
3. wrapper 比較 `(Z→B)≤(R→S)` は R≤Z,B≤S。全 level2 なので extrusion なし。
4. g を boundary1 で公開。二回の freshen は B_i,S_i:level1、C は同一 anchor。`B_i≤C,B_i≤S_i` を保存。R,Z,D はこの公開 root から届かず、旧 store には残る。freshen は event を作らない。
5. 第一 Call は int≤B0,S0≤V0。succ Call は V0≤int,int≤W0。第二 Call は bool≤B1,S1≤V1。全新 result は level1、全比較の payload も level≤1。反対側 replay は int≤C と bool≤C 等を蓄積するが逆辺 C≤B_i は生成しない。
6. f completion は `(A→{a:W0,b:V1})≤o`。上界との replay は C≤A,`{a:W0,b:V1}≤D`。D≤R≤Z への伝播も ground/level1 payload を level2 へ入れるので extrusion なし。C の int/bool 下界は A へ伝播するだけで、int/bool を相互比較しない。
7. 最後の `in f` は boundary0 の root-reachable graph を一つの freshen memo で level0 に複写する。bound restoration であり新しい constrain demand/extrusion occurrence ではない。

この一覧は Rcd の全 field inference、wrapper、succ、二 use、再帰閉包、最後の freshening を含む。型検査で record field を走査することは runtime の latent field を Force するという主張ではない。各 propagate pair は上記 variable-to-variable/link、同じ primitive、Function 分解、record payload に帰着する。唯一の extrusion の非資格を示しただけで停止せず、以後の全比較が新しい wrong-level payload を作らないことまで確認した。

満たす native valuation の一例は C=A=int∨bool、B_i=S_i=V_i が各 int/bool、W0=int、D=R=Z={a:int,b:bool}、B=S=int∨bool、o=(int∨bool)→{a:int,b:bool}。全 bound と demand が成立する。従ってこの original fragment の旧 equality 由来の bool≤int 拒否は現行規則では生じない。元 Scala の上記有限比較列も primitive mismatch を持たない。これを Yulang 全 source membership/whole compiler acceptance に拡張しない。

## 5. odd/even のどこまでが全履歴か

O.§3 の原 grammar analogue `let rec odd=lambda n. let even=lambda m. odd m in even n in odd` では O/E birth=1/2。全 native 履歴は O.§3 の6段で固定される: O,A:1; B,R:2; O≤B→R の唯一の extrusion C,D:1; even の fresh B',R':1 と shared C,D; outer A≤B',R'≤S から D≤S; completion から C≤A,S≤D; 最後の odd freshening。以後全 demand は level1 内、または低 payload の高 row への伝播なので追加 extrusion なし。唯一の `(E,O)` occurrence は非資格。型 bound cycle C→A→B'→C、D→S→D は Value SCC に用いない。この analogue の履歴は完成しており旧等式 B=C,R=D は追加されない。

ただし literal な odd/even の `<=`, subtraction, conditional を含む Yulang source は別である。O.§5、N.§7 はそれらの native lowering/admission と全 Call/branch effect を未確立と明記する。確定できるのは実 inner-call event が `(E,O)` なら、その event の全 pairs (追加 polar pairs を含む) が非資格ということだけ。primitive/conditional に由来する全他 occurrence の一覧は凍結入力に存在しない。ここに仮の builtin や helper を加えて「全 event を検査した」とはしない。**exact source acceptance は OPEN**、first missing evidence は conditional/infix source owner の actual recipes と event provenance。原 grammar analogue の完成履歴でこの欠落を隠さない。

## 6. 同 birth の残余を factorization として構成する

単なる同 birth を telescope equality に替えず、局所 diagonal が運べる正確な条件を求める。固定された一つの原 source strategy s と有限 joint clients を取る。合法な全入力環境/歴史の集合を X、実 copy c が元 scope で読める情報への restriction を π_c:X→X_c とする。Shared は use index を読めず、EventField は実 event を、Desc は元 type telescope を読む。parent の値関数を a_p:X→D とする。

**BL5 (fixed-strategy set-level factorization and total extension).** `I_c=im(π_c)` とする。像上の関数 `f_I:I_c→D` で `f_I(π_c(x))=a_p(x)` を全 x に対して満たすものが存在する必要十分条件は

`π_c(x)=π_c(y) ⇒ a_p(x)=a_p(y)`。

元の全領域にわたる関数 `f_c:X_c→D` が同じ等式を満たす必要十分条件は、この fiber constancy に加えて、**補集合上の関数 `b_c:(X_c∖I_c)→D` が存在すること**である。

証明: 必要性は同じ入力への関数値の一意性と f_c の補集合への制限。十分性では `f_I(π_c(x))=a_p(x)` と定義し、fiber constancy から代表によらない。全域版は互いに素な I_c とその補集合上で `f_c=f_I∪b_c` とする。D に指定された元 d₀ があれば、補集合では定数 d₀ を使える。π_c が元の X_c へ全射であれば補集合は空である。一般にはどちらも仮定せず、b_c を必要条件として残す。例えば X=∅,X_c={*},D=∅ では fiber constancy は成立するが全域関数は存在しない。□

この集合上の定理は source-admissibility を結論しない。copy の許される型・証拠が入力 z に依存する場合、像上でも元 parent の値と完全証拠がその fiber に属することを示し、補集合上でも **元の全合法入力** に対する lawful section と証拠の transport を与える必要がある。未訪問の入力を不正と宣言したり、X_c を像へ縮小したりしない。将来・event・permission を含む元の条件を残す。

有限の全実 copy について、この全域 factor と相互に整合する完全証拠を同時に構成し、各 cut の元 demand を満たす s と元 scope の transport があるなら、BL4 を各 cut に適用して全等式と constraints を満たす joint strategy を構成できる。publication/use の allocation maps μ_i がこの **全域** factorization と可換 (`μ_i(c)=μ_i(p)` の意味で双方を同じ factor へ送る) なら、各 use で substitution により等式を保存する。共有 class は一 factor、eligible な独立 class は各 frame の factor となる。これは明記した全域・証拠・可換性を入力とする条件付き構成であり、finite clients で未訪問の challenge を除外しない。

source coverage は全 lawful derivation について、その conclusion を保つ**いずれかの**strategy にこの条件を成立させる義務である。与えられた任意の内部 assignment を保存するという過強な義務にはしない。

BL1 は π_c と a_p を一切制約しない。純粋な依存反例として X={0,1}, X_c={*}, a_p(0)=int,a_p(1)=bool を取れば、birth が同じ任意の二頂点の SCC を併置しても factor は存在しない。これは BL1→BL5 という証明推論の反例であり、lawful Yulang source 反例ではない。旧 F/G の two-use 例をここへ再利用することはできない。

一つの適用範囲は、まだ generalize されていない一つの再帰 component 内で、全該当 parent/copy が同一 monomorphic telescope と全合法入力領域を持ち、parent の関数と完全証拠が既にその全領域で定義され、原 constructor が copy 側への証拠 transport を与え、公開時の eligible/shared 分類と作用が一致する場合である。このとき f_c は parent の全域関数そのものであり、補集合でもその既存の値と証拠を使用する。SG §3.3 の Internal/MemberEntry は recursive occurrences の共有を供給するが、**全 actual copy にこれらの前提を与える定理ではない**。同 birth の別 scope、lowered anchor、既に公開された input の replay を、この適用に含めない。

この新資格に対する残余 BL-JOINT は次の判断である: actual source Call→accumulation/replay→extrusion の owner が、still-qualified event の全 polar pairs に元 telescope、全合法入力領域と publication allocation を割り当て、必要な source conclusion を保つ strategy について BL5 の fiber constancy、全域への lawful extension、full evidence transport と publication/use の可換性を導出すること。これは複数の必要条件を含む判断であり、全言語の他の未完了義務を置き換えない。first check は same-birth receiver の row が earlier low anchor を含む replay で、target level と copy の scope が receiver birth だけから決まるかである。birth が k でも target row level が必ず k とは authority は述べない。これを同一視して「same-birth event は extrusion を起こさない」と証明する shortcut も採用しない。

## 7. 親への適用、資源、停止

新規則の path/SCC/update/activation と local 二方向対応は上の候補定理。nested f/g と odd/even original analogue の全 native 比較列から、旧跨レベル等置による拒否の前提を除去した。exact Yulang odd/even の残る recipes と BL-JOINT を識別した。全 language soundness/principality/combined termination は OPEN。旧 raw-recursive membership の RP-FULL をこの新規則の証明済み前提にしない。

Mutual TODO: BL-JOINT は source Call/Desc/Shared/Event と publication owner、BL-ODD-EXACT は conditional/infix admission owner、BL-NATIVE は birth incidence/occurrence consumer owner。primary が lease と次の検証を割り当てる。実装変更は本稿の権限外。独立 reviewer は primary が任命し、著者による認証なし。

Requested Astra/medium; observed model/effort/duration UNKNOWN。190秒/3 stages の固定枠、追加更新なし。静的文書と source 読み・hash 検査のみ。契約と12依存 hash は全一致。コード・tests・build・probe・Git・network・descendant・scratch はゼロ。唯一の新規/変更 path は本稿。最終 hash は handoff に記録。**Writes stopped; no descendants.**

## 8. 凍結入力


| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-12-value-reference-copied-row-ownership.md` | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| `notes/design/2026-10-10-local-self-recursive-binding.md` | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` |
| `notes/theory/2026-10-24-value-scc-qualification-proof.md` | `6275229a0ac3c5db2d4757c4b18c43b33c78a5110d028d29e65e6d2dee187045` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/theory/2026-10-13-nested-live-root-generalization-derivation.md` | `f72404c661736ee9e0b6226dfc471724795836510c7aa3a0582d209be47f8dd9` |
| `notes/theory/2026-10-12-odd-even-parent-copy-scc-derivation.md` | `238e21c0a027aa9f0ca14c563c3fbaa11188ee268e8b819a049f81dd6afd5830` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
