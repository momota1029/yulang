# コピーの系譜による有限 native 履歴の消去

CALL-REALIZATION-HISTORY-20261024/r1。Author `/root`。Status: GE1–GE6 は明記した有限区間について独立査読で受理。元の全体命題は OPEN。
Baseline `ef2b33d76045802cfb61c9ed82d7115a4b9ca9f8`。
査読対象 `a637c98a3aa1db18c85018723e7461ae2a685cdb3c56d07bb5298953a95f6c45`。査読後はこの status と receipt だけを primary が追記した。[outcome](../../tasks/agent-loop/sprints/call-realization-history-20261024-outcome.md)に範囲を固定する。

## 1. 親命題へ戻す対象

[局所 diagonal lift](2026-10-13-intrusion-source-preservation-proof.md) §4 の有限合成は、各 extrusion の直前に「元の demand を同じ valuation が満たす」ことを要求していた。本稿は、publication/fresh use をまたがない有限履歴について、全 demand と保存 bound を一つの有限な初期制約の closure から導出する。従って各 cut の成立を独立に仮定する必要はない。

ここで構成する closure は **native の構文的な比較導出** である。意味論上の Function の単調性から Function 比較の反転を導くことも、source の full Call/effect の truth を native の発行記録から得ることもない。source の joint strategy、複数の独立使用、元の A/B、required principal coverage、combined termination は同じ親義務として残る。

適用対象は元 `Typer.scala` の Function/Record/Primitive/Variable、実 `constrain`/`extrude` と、実 extrusion の parent/copy pairs だけを併合し全 clause を保持する intrusion である。intrusion の source 資格は[生成レベル別 SCC](../design/2026-10-24-birth-level-scc-intrusion.md)のまま。本稿の erasure を資格規則に追加しない。

## 2. 有限区間と固定する座標

有限の開始 store Σ₀、その開始時点で未処理の comparison seeds、および区間中の外側の source generation が発行する comparison seeds を固定する。この有限区間に `freshenAbove` による scheme use は含めない。ordinary `freshVar` による source 変数の生成は含める。

変数 raw identity は不変であり、代表元変更後も証明上の名前を保持する。各 **実 extrusion allocation** が新しい c を作る瞬間に、実 parent a への辺 `c ↦ a` を記録する。positive/negative のいずれも親は同じ a でよい。memo hit は新しい辺を作らない。親は allocation 順で古いので、この系譜は有限で非循環である。これに対し bound graph は循環してよい。

系譜辺を持たない変数を base と呼ぶ。ordinary source allocation は新しい base となる。ε(a) は a から親を反復して到達する唯一の base。Function/Record は構造と field の順序を保って ε を作用させ、Primitive は実 object identity を保つ。bound graph は展開しない。従って各有限 type term に対する ε は有限に計算できる。

開始時点以前の copy は、系譜を開始入力として与えない限り base として扱う。その場合、その古い parent/copy pair を区間中に併合する履歴は本定理の入力ではない。古い pair も併合するなら、その実 allocation ancestry を開始入力に含め、開始 store/seeds の全変数をこの同じ ε で読む。fresh use の新しい変数を extrusion copy と見なして祖先を結ぶことは許さない。

これらは原言語から case を除去する提案ではなく、有限区間補題の境界条件である。親命題への一般化には、区間の境界をまたぐ source/publication 対応が別途必要となる。

### 補題 GE1（系譜と quotient）

実 parent/copy pair の併合だけからなる代表元関係 q は `q(a)=q(b) ⇒ ε(a)=ε(b)` を満たす。従って ε は各代表元 class 上で一意であり、全 bound、保留 demand、memo 値を代表元へ読み替えても erased term は変わらない。

証明。併合する一辺 `(a,c)` は定義により ε(a)=ε(c)。その対称・推移閉包も等式を保存する。代表元の選択が最小 level、最古、最若のどれでも結論は同じ。構造 term への主張は構造帰納。parent が既に代表元の場合も、その class の ε は一意なので同じ。□

この補題は全旧 clause を保持することを要する。旧 row を捨てる、保留比較を完了扱いにする、無関係な変数を同じ class に入れる操作を正当化しない。level 条件の保存は別の [NL5](2026-10-24-native-level-closure-and-publication.md) の義務である。

## 3. 初期制約だけから作る有限 closure

Γ を次の erased comparisons の集合とする。

1. Σ₀ の各 lower `s ∈ a.lower` に対する `ε(s) ≤ ε(a)` と各 upper `t ∈ a.upper` に対する `ε(a) ≤ ε(t)`。
2. 開始時点の未処理 demand と、区間中に外側の source constructor が発行した各 seed の ε 像。

replay、構造分解、extrusion による rewritten demand は 2 に追加しない。それらは後で導出する側である。ordinary source allocation でできる base はすべて有限集合 B に含める。T は Γ の全 endpoint の構造 subterms と B の和集合。変数の bounds を subterm として無限に展開しない。Γ が有限なので T も有限である。

`C(Γ) ⊆ T×T` は次の規則で飽和した最小集合である。

```
Seed     (s,t) ∈ Γ                  ⇒ (s,t) ∈ C
VarId    a ∈ B                     ⇒ (a,a) ∈ C
CutVar   (s,a),(a,t) ∈ C, a ∈ B     ⇒ (s,t) ∈ C
Fun      (Fun(a,b),Fun(c,d)) ∈ C    ⇒ (c,a),(b,d) ∈ C
Record   (Record(fs),Record(gs)) ∈ C
         (label,t) ∈ gs, first(fs,label)=(label,s)
                                     ⇒ (s,t) ∈ C
```

`first` は実 native の `fs.find` と同じ最初の一致である。重複 label を暗に排除しない。missing field、異なる constructor head 同士、異なる実 Primitive object 同士の比較を `Bad(C)` とする。variable endpoint がある比較はこの head mismatch に含めない。同一 Primitive object は failure でない。

実 native の最初の fast path は `lhs is rhs`、すなわち物理的同一性である。したがってこの closure は、物理的に同じ Record object の比較について、実行が省略する分解まで行うことがある。特に重複 field の場合、同一 object の比較をさらに分解して Bad を得る可能性がある。ここでは closure と actual cache/実行の完全同値を主張しない。**実際の failure を closure が覆う**向きだけを用いる。Primitive の印刷名だけを見て異なる object を同じにしない。

### 補題 GE2（有限構成）

C(Γ) は有限回の rule application で構成でき、comparison は高々 |T|² 個である。

証明。全規則の結論は T×T にある。Fun/Record は既存 endpoint の subterm を選び、CutVar は既存 endpoint を組み合わせるだけで、新しい constructor を作らない。Γ と全 VarId を入れ、未追加の結論がある規則を反復して追加する。追加のたびに有限集合 T×T の未登録要素が減る。停止時は全規則に閉じており、任意の閉集合に包含されることを各追加への帰納で示せる。よって最小閉集合である。Bad はこの有限集合の endpoint を検査して定まる。□

これは証明用の有限 closure であり、新しい production inference、typing search、rollback の採用ではない。実 native の停止を |T|² から結論することもない。異なる copy/cache key が同じ ε 像を持ちうるためである。

## 4. extrusion が作る term と bound

### 補題 GE3（構造を保つ copy）

各実 extrusion `extrude(t,p,l)` の返却 term t' は `ε(t')=ε(t)`。同 invocation の全 parent links とコピーされた selected bounds の erased comparison は、invocation 開始以前の erased stored comparisons と VarId から導出される。開始後に他の polarity が入れた link を selected list が読む場合も含む。

証明。低 level の early return と Primitive は恒等。Function は引数 polarity を反転しても、左右の子の ε 像が同じなので同じ構造 term になる。Record は同じ順序と label で各 field を処理する。

wrong-level variable a の初回は新しい c に `c ↦ a` を付け、polar memo へ登録してから selected bounds を処理する。よって ε(c)=ε(a)。positive link a≤c と negative link c≤a はともに VarId へ消去される。positive で lower s≤a をコピーすれば、新しい lower は s'≤c であり、その像は ε(s)≤ε(a)。negative の upper a≤t も同様である。

selected entry が invocation 開始以前の bound ならその同じ erased comparison を使う。開始後に他 polarity が同じ original row へ入れた entry は実 parent link なので VarId である。例えば Function(a,a) の argument で negative copy c− が生まれ、その後 result の positive copy c+ が lower c− を読む場合、新しい c−≤c+ の像も ε(a)≤ε(a)。新しい copy の selected bounds が後から読まれる場合も、それまでに構成した同じ erased comparison を使う。

memo hit では登録済み c を返すだけで、同じ ε(a) である。finite bound cycle は変数 leaf と memo により処理し、無限展開への帰納を使わない。具体的には、全 invocation で登録された新しい copy の ε を parent に沿って同時に定め、実 constructor evaluation の各有限 prefix で上の不変条件を保つ。返却値への主張は constructor が完了した時点に得られる。□

## 5. 全履歴の同時帰納

### 定理 GE4（seed から全 request への導出）

§2 の任意の有限 native 履歴 prefix において、次のすべての erased comparison は C(Γ) に属する。

* 既に保存された各 lower/upper bound。
* 新規に呼ばれた、または保留中の各 `constrain` request。
* 各 extrusion の書込みと rewritten request。
* parent/copy 併合後に保存・再送される全旧 comparison。

証明。実 write/request events の順序への同時帰納を使う。

**開始と外側生成。** Σ₀ の clauses、開始 pending、後続 source seed は Γ に含まれる。新しい source 変数は base、空 bounds なので追加義務を作らない。

**identity/cache return。** その request の ε 像は呼出し元の帰納段階で既に得られている。物理 identity または cache hit は clause を追加しない。cache に記録されたことを「比較済みの証明」としては用いない。native が branch 実行前に variable pair を cache に入れる場合も、この議論は同じ。

**Function。** request の ε 像に Fun を適用する。実 native の child order は右引数≤左引数、その後左 result≤右 result であり、両方が導ける。後半まで実行が到達しなくても、実際に生じた request は覆われる。

**Record。** 実 `find` の選択した field に Record を適用する。存在しない label は Bad。list の順序・重複は同じである。

**upper 追加。** `a.upper ::= t` の request は既に C にある。各既存 lower s≤a と今回の a≤t の ε 像に CutVar を適用すると、replay s≤t の像が得られる。ε(a) は base なので規則の中間条件を満たす。

**lower 追加。** 同様に今回の s≤a と各既存 upper a≤t から CutVar。native の片側 insertion、opposite-side traversal の順序にそのまま従う。片方向 link を両 row に勝手に格納しない。

**level mismatch。** GE3 により extruded term の ε 像は同じなので、rewritten request は元 request と同じ C の要素。GE3 の各 selected comparison は、今回以前の stored comparison、または VarId から得られる。リンク挿入時に native が即 replay を行わないことも、帰納に追加の要求を作らない。

**intrusion。** GE1 により quotient による読み替えで像は変わらない。保持した clause は帰納仮定を持つ。併合に伴う lower/upper の新しい組合せからの replay は CutVar であり、両中間 row は同じ base に写る。intrusion の具体的 drain/order/cache がある場合は、これらの通常 write/request または保留のままのいずれかを満たす必要がある。証明は pending の消失や処理完了を仮定しない。

**失敗。** request の像は既に C にある。actual native の missing field/constructor clash なら、その同じ field/head が ε でも残り Bad が得られる。異なる Primitive object の比較も同じ object identities が残る。以上が全 native branches。□

### 系 GE5（有限区間の rejection 保存）

`¬Bad(C(Γ))` なら、上の区間のどの有限 prefix も native の missing-field/constructor-clash を発生させない。従って実 parent/copy のどの部分集合を intrude しても、この条件の下ではその種の新しい拒否を導かない。

証明。最初の failure があれば、その request を GE4 で C に移すと Bad が得られ矛盾。□

これは原 unlevelled 実装の成功との同値、全種の compiler error の排除、termination、source principal coverage を意味しない。有限区間の syntactic closure が持つ failure の不在から、実 native 比較の failure 不在を導く定理である。

## 6. 一つの valuation による全 cut の diagonal lift

各有限 native term を同じ constructor interpretation で読む意味論を固定する。ρ は B の valuation であり、C(Γ) の全 comparison を満たすとする。`ρ̂(a)=ρ(ε(a))` と定義し、constructor へ通常どおり延長する。

### 定理 GE6（同時 lift）

ρ̂ は区間内の全保存 bound、全 original/replayed/rewritten demand、全実 parent/copy equalities を同時に満たす。任意の finite subset の侵入等置を満たし、初期 base valuation を変更しない。

証明。構造帰納により `⟦t⟧ρ̂=⟦ε(t)⟧ρ`。各 comparison は GE4 により C に属するので、その ρ における成立が同じ ρ̂ における成立を与える。parent/copy は ε が等しい。代表元上でも GE1 により一意。全 cut で同じ式を使うため、途中で valuation を選び直さない。□

従って局所 diagonal lift §4 の「各元 demand がその cut で成立する」という列の前提は、**初期 erased seeds から機械的に構成した一つの C の model** へまとめられる。各 cut の demand が何かを先に全て仮定する形ではなく、Fun/Record/CutVar によるその有限 derivation が GE4 にある。

ただし、ρ が Γ だけを満たすことから C 全体を満たすとは、任意の意味論では結論できない。その追加主張には、Fun/Record の構造的な inversion がその同じ意味論で妥当である証明が必要になる。reflexivity/transitivity、Function の contra/covariance という introduction rule だけでは inversion は出ない。complete Yulang Call/interface に対する当該 inversion もここでは仮定・採用しない。GE6 はこの点で GE5 の構文定理と区別される。

さらに ρ̂ は native の値割当てであり、各 original source scope で選べる dependent evidence strategy だという主張を含まない。level を消したことから independence、source lifetime、actual receipt、current world を消すことはできない。

## 7. 元の具体例への適用

[同 birth の replay 例](2026-10-24-birth-level-extrusion-redundancy.md)の原 source を保持する。

```
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first=h x, next=f {a=y}}
  in f
in top
```

base を H,o,B,Y,J,R、`K=Fun(Y,Record(first:J,next:R))` とする。h x の demand は `H≤Fun(B,J)`。実 extrusion が C/B positive、D/J negative を作るので `ε(C)=B, ε(D)=J`。後の original seeds は `o≤Fun(Record(a:Y),R)` と `Fun(B,K)≤o`。

CutVar(o) と Fun により `Record(a:Y)≤B` と `K≤R` を得る。保存 B≤C の像は B≤B。したがって前者を C へ replay した demand の像も `Record(a:Y)≤B` である。その positive extrusion が T/Y を作っても、`ε(T)=Y`、新しい C の lower `Record(a:T)` はまさに同じ導出済み comparison となる。これは source seed から後着 copy T の demand までの有限 derivation であり、後着 demand を独立した前提に入れていない。

[result replay の例](2026-10-24-replay-extrusion-commutation.md)でも、R≤C の境界へ `Record(a:B)≤R` が replay され、新しい T/B を作る区間に同じ議論が適用できる。`ε(T)=B` とすれば rewritten `Record(a:T)≤C` は元の CutVar(R) の結果へ戻る。publication 後の B₀/B₁ は fresh-use variables なので、この系譜へ T/B と同じ意味で接続しない。そこで発生する独立 Int/Bool 使用の coverage は GE6 では閉じない。

両例で ε は copy の **type genealogy** だけを消去している。actual origin/receiving Value、birth、保持 source-reference graph、SCC、received carrier のどれも変更・推測しない。RG-OWNER の actual receiving occurrence は、この証明とは別に source/native transport から定まる必要がある。

## 8. 完了範囲と継続点

GE1–GE6 は、循環 bound graph、両 polarity、late replay、memo/cache、全旧 clause を保持する parent/copy quotient を含む有限区間の native 構成である。有限 prefix ごとの native demand の成立条件を source 全体の成立条件と取り違えない。

親へ残る具体的な接続は、(i) 元 source の full judgment から C の joint model/evidence を構成すること、(ii) その strategy の source scope を保持すること、(iii) publication/fresh use の独立 frames を接続すること、(iv) level/canonicalization 条件と combined termination、(v) actual receiving occurrence の対応である。これらは今回新たに加える採用条件ではなく、元の parent theorem の義務である。特に「SCC があるから ρ̂ は source-admissible」とはしない。

## 9. 固定入力と作業記録

直接の契約は `tasks/agent-loop/sprints/call-realization-history-20261024.md`、SHA-256 `17cb330a3184cf267784141239bbfd42e9e91b1950bd7e1b9ce5a1806a9d9339`。その frozen input manifest に局所 lift、native level/publication、birth replay、元 Typer.scala を固定する。

追加の直接読取りは、native `is` と `===` の意味を確認する `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/package.scala`、SHA-256 `c33b015e51baf32cb42ca48e6452ab005c85ac185a590ec870c19ef198b4fcb2`。`is` は `eq`、`===` は `==` である。この追加は実装変更・新しい語義の採用ではない。

本稿は primary 単著。実コードの read と数学的 constructor induction だけを使い、test/build/compiler run、試験 script、新しい production algorithm は作成・実行していない。独立査読の対象 hash、判定と修正は同 sprint outcome に記録する。
