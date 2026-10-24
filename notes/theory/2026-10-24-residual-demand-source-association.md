# 極性を持つ要求の残余と source occurrence の対応

BIRTH-RESIDUAL-CLOSURE-20261024/r1。著者 primary。独立査読は RD1–RD5 の明記した限定範囲を受理し、RD1 の fresh comparison を cache miss と明記する修正を求めた。primary がその条件を補った。元の全体義務を維持する。[契約](../../tasks/agent-loop/sprints/birth-residual-closure-20261024.md)に入力を固定する。

## 1. 問題を constraint constructor へ戻す

既存稿で取り出した正の extrusion link は `u:R≤C`、後着の下界は `l:A≤R`、ordered replay は `p:A≤C` である。A=Record(B) の場合、p が T/B の実 copy を作る。source union に複数の Call があることと、この実 link がどの要求の一部かは区別する。

本稿ではまず、source receiver を一切使わず、元 native 規則における **要求の残余**を構成する。次に、それを source Call へ戻す際に必要な constructor を明示する。新しい receiver selector の非含意を再度証明して、元の対応証明の代わりにはしない。

## 2. signed boundary と residual comparison

一回の actual extrusion で作られた copy c、parent a、target k、極性 ε、creation invocation j を固定する。copy 作成時の実 parent link と選択側は次の通り。

| ε | native が作る link b | a の選択側 | 後着する bound d | replay の結論 |
| --- | --- | --- | --- | --- |
| + | a≤c | lower | s≤a | s≤c |
| − | c≤a | upper | a≤s | c≤s |

`B=(j,a,c,ε,k,b)` を boundary record とする。これは Value の新規頂点でも、型行の恒久 owner でもない。元の extrusion の一つの具体的な port と parent link を指す。

型不等式の証拠は、型付きの有向辺として書く。`d₂∘d₁` は d₁ の終点と d₂ の始点が同じときだけ作る cut であり、結果はその始点から終点への比較である。native replay の pair はこの cut の端点を計算する。

**RD1（両極性の native residual）。** この boundary の選択側へ後着した bound d と b の ordered replay は、正では `b∘d`、負では `d∘b` である。結果の低い端点は同じ c である。fresh comparison、すなわち cache miss で branch dispatch に達する比較が wrong-level structural side を持つとき、元 constrain はその側を同じ極性で k へ extrusion する。cache hit では比較 request の端点だけを結論し、新しい extrusion を結論しない。

証明。正の場合、`s≤a` の rhs-variable branch は a.lower に s を保存し、既存 a.upper の c と比較する。a.upper に c が既に存在する履歴では `constrain(s,c)` が生成される。s.level≤k なら rhs-variable accumulation で終わる。s が高い構造であれば rhs-variable の guard が失敗し、positive extrusion を k で呼ぶ。s が Variable の場合は二つの level 比較の少なくとも一方が成立するため、variable/variable 比較自体では extrusion しない。

負の場合、`a≤s` の lhs-variable branch は a.upper に s を保存し、既存 a.lower の c と比較する。`constrain(c,s)` で s.level≤k なら蓄積、高い構造なら negative extrusion を k で呼ぶ。やはり variable/variable だけでは新 copy を作らない。ordered input は両方とも lower,upper であり、b が常に upper にあるとは限らない。□

既存 bound が先にある場合、extrude 本体は a の選択 list を同じ ε で写して c の対応 list に置く。RD1 は、その list に後から加わる要素の constraint を同じ c へ要求する規則である。別 invocation の memo を共有するとまでは主張しない。

## 3. 保持した境界を持つ導出の構成

### 3.1 型付き hole

正 boundary に対する hole を `□:(s≤a)` とし、式 `b∘□:(s≤c)` を作る。負では `□:(a≤s)` と `□∘b:(c≤s)` を作る。hole の型の middle coordinate a、低い端点 c、b の creation record は固定する。新しい d を入れる操作を `plug_B(d)` と書く。

この構成は普通の cut の一つの境界を印付けしたものである。lower/upper の両証拠、元の occurrence、全 source support は残す。印を付けない側の証拠を捨てたり、そこにある元 Call を別の Call へ変更したりしない。

**RD2（residual factorization）。** RD1 の actual ordered replay は `plug_B(d)` の端点消去と一致する。正負のどちらでも、plug は B の c と b を変えない。さらに、型座標の単射改名 θ に対して

```text
θ(plug_B(d)) = plug_{θB}(θd)
```

が成立する。θ は source Value、birth、Call identity、過去の receipt を変更しない。

証明。正では両辺が `θb∘θd`、負では `θd∘θb` になる。typed cut の middle equality を θ が保存する。fixed source data は θ の定義域に含めない。入力を交換した式は一般に別の middle coordinate/type を持つため、この等式から source union の任意要素を境界として選べるとは結論しない。□

### 3.2 structural descent、memo、reuse

Function の比較では、result の cut は同順、argument の cut は反対順へ分解される。例えば

```text
F0≤F1≤F2
argument: A2≤A1≤A0
result:   R0≤R1≤R2.
```

従って境界が比較のどちら側に位置するかは argument で反転する。Record は実際に比較した field の inclusion と label を保持して同順へ分解する。元 bound b の部分比較を、その実 constructor path とともに運ぶ必要がある。常に `Replay.upper` を取る無極性の探索を一般規則にはしない。

一 invocation 内では `(variable,polarity)` の memo を copy 作成直後に登録し、その後で選択 bound を辿る。再訪は同じ copy を返すため、無限の型展開は要らない。finite operation history の各生成 step について、先に存在する bound occurrence と当該 step の実 port を記録すれば有限の証拠になる。RelationId の再利用や source の再帰を、証拠木そのものが非循環であるという仮定に置き換えない。

変換済み output の reuse は fresh creation ではない。元の PairGroup と新 reuse occurrence を別々に残し、新しい processing derivation から新 occurrence の境界を構成する必要がある。RD2 の fresh boundary b だけから、任意の reuse の association を移植しない。

## 4. source Call へ戻すための構成と到達点

source Call e の生成時に必要な二つの出力を区別する。1 は元の association 規則で決まり、2 の source/native の同時対応が証明対象である。

1. 名前解決された callee Value と definition-root origin。直接 Call-demand extrusion の association は承認規則で固定される。
2. 実際の Call obligation と、それを検査する native demand の導出。full Call の provider、current world、whole carrier、receipt、pending、W/Z arms と future はこの元の obligation に残る。

2 の対応が構成された場合、直接 extrusion の境界 B をその demand の実 port に挿入できる。source の証拠におけるその port の受け取り先を ξ_B とする。source 型付き写像まで持つ場合、後着 d を hole に入れる操作は middle interface 上の合成であり、ξ_B は同じ boundary incidence に留まる。signature receiving incidence と solver occurrence を同じ sort と宣言しているのではなく、boundary B の生成を媒介にする。

ここには二つの異なる結論がある。

**RD3（構成した source residual の receiving incidence）。** 元の source demand の typed interface と、d の同じ middle interface への typed map が実際に構成されているとき、plug_B(d) は元 ξ_B を保つ。direct source event の origin/receiver を、その residual constructor へ保持する表示を構成できる。

証明。正では d の codomain と b の domain を同じ middle interface で同定して合成する。合成の codomain は b の ξ_B のままである。負では比較方向が反転しており、b の source-side boundary を同じ typed object として保持する。Function argument では前節の反転を適用する。元の whole dependent tuple の field map を使うので provider/world/receipt を marginal ごとに選び直さない。□

**RD4（native と source の残る接合点）。** RD2 の native cut と RD3 の source residual を同一の生成 operation に対応させるには、source の actual typed map を native bound d,b に送る写像が必要である。単なる scalar constraint の証拠や source support の集合から、その map を生成したとは言えない。RD3 の前提をこの写像の存在と読み替えて RG-OWNER を閉じない。

従って RD1–RD2 は実 native の両極性の生成を閉じ、RD3 は必要な source interface がある場合の合成を構成する。source-to-native constructor がその二つを同時に出力することは独立の義務である。ここでその義務を仮定した全体証明は提出しない。

## 5. 既存の ScopedDemand は何を与えるか

この接合点で、保持済みコードの `ScopedDemand` を調べる。これは `(original_call,use_instance,root,output_scope,input)` を持つ。`candidate_context_seed` は source Call の local slot0 の actual introduction から作る。`candidate_context_value_rewrite` は実 whole-Function extrusion の rewrite に合わせて root を変え、元 Call index を保つ。

`candidate_context_begin_replay` は lower の demand が空であることを検査し、upper.demand を child へ運ぶ。従って **この demand が生きている whole-Function の経路**には original_call の具体的な残余が存在する。これは新しく加えた selector ではない。

しかし次の二つの消費点がある。

1. `candidate_function_port_admit` は authentic whole-Function root を照合した後、demand を None にする。effect の argument/result はそれぞれ stamp/protect transformer へ、Value の argument/result は transformer0へ進む。Function の child path は別の Dependency record に残る。
2. `bound_scoped_payload_for(..., ExtrusionLink)` は Value parent に対して default ScopedFlow を返す。直接 extrusion の R≤C や D≤J は、元 Call の全 Function demand を carry しない。この link は新しい全 Function demand ではないためである。別途 Derived と extrusion creation record は残る。

**RD5（既存 demand field の適用範囲）。** scoped path が有効で上記 constructors が成功する有限履歴では、seed から whole-Function bound/replay/rewrite を通り port 消費前までの original_call は同じ seed の index である。一方、fresh Value extrusion link とその scalar descendants の receiver をこの field 単独から得る方法は、実 constructor の reset により成立しない。

証明。seed は actual by_occurrence の index を格納する。ordinary bound は同じ flow、rewrite は root だけを更新、replay は authentic upper flow を運ぶため、これらの列への帰納で index が保たれる。FunctionPort は明示的に None にし、ExtrusionLink は default を返す。後者の default から original_call は読み出せない。source/dependency record の消滅を意味するのではなく、この field が担当する意味の終端を示す。□

前稿の具体例では、h の全 demand に index h があっても、R≤C の ExtrusionLink でこの payload は空になる。従って「保持した original_call を読むだけで T/B の receiving を閉じる」という経路は使えない。元の Derived/Replay/creation による backtrace は有効なまま。必要なのは RD4 の source-to-native map であり、ScopedDemand の別の仕事を受け取り先の定義に流用することではない。

## 6. 親への適用

新しい [birth-level native falsifier](2026-10-24-birth-level-extrusion-redundancy.md)は、元の grammar の次の source を空 store から構成した。

```text
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first = h x, next = f {a=y}}
  in f
in top
```

h の demand は `H₁≤Function(B₂,J₂)` であり、正の boundary `u:B₂≤C₁` を作る。自己呼出し F/F は `o₂≤Function(Record(Y₂),R₂)` を作り、その入口では copy はない。f completion の Function argument 分解が `v:Record(Y₂)≤B₂` を作ると、replay `u∘v:Record(Y₂)≤C₁` で T₁/Y₂ が実生成される。

RD1–RD2 によって、この new case の native residual は正の `plug_B(v)` と正確に一致する。v の source path には Argument/Swap があるが、u はその外の保存された B≤C boundary である。従って外側の plug の順序は u∘v のまま。この例で RD3 を適用するために必要な source map は、まさに v の complete source argument comparison を u の h 側 middle interface へ送る map である。v の scalar derivation が存在するだけではその source map を作ったことにならず、RD4 は残る。

これにより、(a) 同 birth なら全 descendant の extrusion を消せる、(b) ScopedDemand.original_call を scalar link まで読むだけで残りが閉じる、という二つの近道は使えないことが確定した。前者は具体的 native history、後者は実 field の消費/reset constructor による。元の graph と provenance は存在している。

現在閉じた native の進展は、positive/negative の両 residual constructor、実 replay との端点対応、改名との可換性、ScopedDemand の実 constructor が与える範囲の確定である。全 source correspondence、source-scoped joint lift、一般化・全使用、全体の A/B と停止性は未完了のまま維持する。今回の二つの失敗候補を、生成レベル別 SCC の規則そのものの反例とはしない。

直接入力は契約の30固定入力。実装変更、tests/build/probe/compiler 実行はない。凍結査読対象と primary の cache 条件明記後の hash、元の残項は [outcome](../../tasks/agent-loop/sprints/birth-residual-closure-20261024-outcome.md)に記録する。
