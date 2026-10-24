# Actual copy histories: finite polar witness amalgamation

ACTUAL-COPY-HISTORY-20261024/r2 intake correction. Author `/root/astra_corrected_machine`; primary supplied interpolation suggestions and this scope correction.
Candidate mathematics, independent review pending. Baseline `61e509ae976aa1e0007fa76a5ff2f33e91362a11`.
Requested inherited Astra/medium; observed UNKNOWN. Sole output: this note.

**Primary intake correction — AH2 is not available as stated below.** The producer's frozen r1 had SHA-256 `868003002c1fb3def7493f5b53611c7c54b307749a3a1f3447b15cb9ca440ea2`. Its simultaneous assignment argument treats unchanged low leaves and actual after-parent values as fixed, without requiring them to be outside the newly reassigned destination family. A copy from an earlier operation can be a later operation's low leaf or parent. Its newly assigned value then need not equal the chart's old ambient value or any listed parent witness. The all-history application of AH2 is withdrawn pending a theorem with an explicit fixed ambient valuation, actual-parent anchoring and signed occurrences of every reassigned destination. AH1 and AH3 remain unreviewed candidates. The text below preserves the construction and its precise witness-supplier gap for further work; it is not an accepted premise for the Lean root proof. No source counterexample follows from this defect.

## 1. 固定した親と今回の差分

CH6 の一つの canonical model ρ* を固定する。これは元の任意の successful finite Let/LetRec history h の Γ_h に対する model から構成されたもの。P1 unique-label regular-tree domain、全 Z values、元 anchors と output contracts を維持する。CH0–8 と SU/EC の受理範囲をそのまま使う。

目標は実 earlier-Y=T history h′ に model を与えること。CH7 の同じ有限式への等式追加とは区別する。本稿では、異なる factor を一つの polar memo key に集める際の **具体的な値構成** を証明する。単一の factor を任意に選ぶ方法を置き換える。有限 regular-tree 値の共同構成は得られるが、全 h′ events に必要な witness family の供給は最後まで閉じなかった。従って actual-history coverage 全体を宣言しない。

## 2. AH1: P1 の有限 regular join と bounded meet

P1 は Primitive object、Top、Function、unique-label Record の最大 simulation preorder。値は bisimilarity class とする。任意の非空有限集合 S に join ∨S が存在する。S が common lower bound を持つなら meet ∧S が存在する。これらも guarded regular trees で、入力の有限 graph から構成できる。native に union/intersection constructor を追加する意味ではない。

二項構成を述べる。Top は join の吸収元、meet の単位元。同じ Primitive はその Primitive。異なる非Top heads の join は Top、meet は存在しない。Record join は共通 labels と field joins、Record meet は label union と共通 field の meets。Function では

```
join(Fun(a,b),Fun(c,d)) = Fun(meet(a,c),join(b,d))
                         if meet(a,c) exists, else Top;
meet(Fun(a,b),Fun(c,d)) = Fun(join(a,c),meet(b,d))
                         if meet(b,d) exists.
```

Record meet は共通 field の全 meet が存在する場合のみ。空 Record は元 P1 constructor のまま。

**構成の有限性。** 全 input graph nodes の有限集合 V を取り、V×V に `MeetOK` を定義する。Top pair/same Primitive は可、異種非Top heads は不可、Record は共通 field pairs、Function は result pair の MeetOK を要求する。単調 boolean operator の最大 fixed point は有限消去で得られる。Function domain には join が常にあるため MeetOK の追加条件はない。各 pair の Join/Meet node を先に登録し、上の constructor equations に従って children を結ぶ。Topによる alias は既存 input node、その他の再帰 edge は Function/Record を通るので guarded。有限 graph である。n項は有限回の二項構成。

**正当性。** common lower z がある pair は z の root inversion によって MeetOK の postfixed family を作る。従って上の存在判定は common lower がある pair を落とさない。逆に MeetOK の constructed meet は両入力以下という simulation を構成できる。join が双方以上、meet が双方以下という四つの関係を同時に検査する。Function は domain を逆向きにし、Record は label intersection/union に対応する。任意の upper u について join≤u、任意の lower l について l≤meet も同じ同時 simulation で従う。domain meet 不存在で Function join=Top とした場合、非Topの共通 upper Function があればその domain が二 domain の common lower となって矛盾する。異種headsも非Top upperを持たない。よって lub/glb の両 universal properties が成立する。有限 fold はこれらを保つ。□

この構成は「model の存在を仮定して新しい model を要求する」ものではない。既知の ρ* 値の有限 graph から各新値の graph を具体的に作る操作である。

## 3. AH2: repeated-key の一つの値と全 selected entries

finite after-operation/memo/use indices を固定する。各 actual polar key k=(operation,parent,sign,target) に有限非空の candidate witness values W_k を付ける。異なる operations の同じ parent/sign は別 key。memo hit は同一 k。publication の shared low row に複数 use が達するなら、それらは **同じ destination row** に属する一つの family として扱う。ここで allocation bijection は要求しない。

一つの destination copy c が複数の original intermediates に対応する場合、P_c をその original parent-value witnesses の非空有限集合とする。全て同じ ρ* で解釈する。sign+ では全 p∈P_c,w∈W_c に p≤w、sign− では w≤p を要求する。これを cross-parent condition と呼ぶ。これは per-use ごとの別 witness 選択より強い。

実際に返す値は

```
value(c+) = meet W_c,       value(c−) = join W_c.
```

positive meet は任意の p∈P_c が common lower なので AH1 で存在する。negative join は無条件に存在する。従って全 p について p≤value(c+) と value(c−)≤p。二つの signs が同じ actual parent にある場合、その parent witness を介して value(c−)≤value(c+) も得る。

### selected-bound charts

各 selected entry e の copied finite syntax term を t_e とする。各 target candidate w∈W_c について、t_e の全 copied leaf occurrences に、その actual destination key k の W_k から一つの値を割り当てた chart χ_(e,w) を保持する。unchanged low leaves は元と同じ値。chart は各 occurrence の field/path/sign と original bound origin を保持し、次を実際に証明する：

```
c positive:  interpret(t_e,χ_(e,w)) ≤ w;
c negative:  w ≤ interpret(t_e,χ_(e,w)).
```

同じ key の複数 occurrences は chart の段階で別 witness を持っていてよい。結論の値では必ず一つにする。必要なのは **全 entry × 全 target candidate** のこの矩形の証拠であり、entryごとに一つだけ都合のよい target を選ぶことではない。

**AH2。** cross-parent condition と上の全 charts があるなら、表示した meet/join assignment は全 parent links、全 selected bounds、全 mutable cross-sign links を同時に満たす。

証明。positive extrusion の各 copied leaf は、net-positive なら meet≤その chart witness、net-negative なら chart witness≤join。Function domain で不等式を反転する構造帰納から、新しい t_e の値は各 chart の値以下。従って全 w∈W_c 以下であり、glb property によって meet W_c 以下。negative extrusion では同じ帰納の外側方向が反転し、新しい t_e は各 chart 値以上。全 w 以下ではなく **全 w が新 t_e 以下**なので、lub property により join W_c≤新 t_e。これが全 selected entries の要求である。

opposite polarity が traversal 中に追加した entry は c−≤c+。上の parent-link chain がこれを証明する。target以下で early returnする low rows は値を変えない。memo hit は既に定義した一つの値を読むので再選択なし。複数 payloads が同じ key を訪ねても、その全 charts を最初から有限 family に入れてある。全条件は一つの finite history に対する同時条件であり、行を割り当てる途中に異なる valuation を選ばない。□

AH2 は異なる後着 payload を同じ memoへ登録する問題に対して明示的な値を与える。conditional な「compatible valuationが存在すれば使う」命題ではなく、witnessed inequalities から regular-tree valuationを作る theorem。ただし、それら inequalities の actual-event supplier は別に証明しなければならない。

## 4. semantic inversion による chart の実構成

各 chart を opaque premise にする必要はない局所caseがある。original finite syntax t、同じρ*における tの値、candidate cap w の実 inequality `⟦t⟧ρ*≤w` を持つとする。tとwの構造に沿って反転する。

* w=Top なら比較は無条件。この subtree の leaf witness には元ρ*の leaf値を使える。
* Function/RecordでwがnonTopなら、P1 inversion が同じ対応field/domain/resultの不等式を与える。
* copied variable leaf aで止まった時、net+ならρ*(a)≤対応w-subtree、net−ならそのsubtree≤ρ*(a)。このsubtreeを当該keyの candidateへ登録する。
* unchanged leafは元値のままで、その残 inequalityを保持する。

negative方向 `w≤⟦t⟧ρ*` も左右とsignを反転する。Topが右側の variable value に出る場合は適切な元 leaf witnessを保持し、Topから nonTop構造の child義務を捏造しない。chart の skeleton は実 finite term t のままで、wの必要な有限depthだけを読む。

**AH3（有限 witness closure の局所境界）。** fixed finite set of original parent/term values and initial caps を与え、上の反転だけで candidates を増やすなら、全 candidates はそれら有限 regular graphs の subtree values に属する。finite key set Kとの積 K×SubValues による worklist は有限。新syntaxrowを作らず、bound cyclesは登録keyを参照する。

証明。反転は子nodeを取り出すだけ、Top fallbackは既存parent値。有限 term interpretationsのconstructor nodesも初期有限集合に含める。全追加候補はこの集合に閉じるため、重複 pair を処理しない closure は有限。□

注意：途中で AH2 の meet/join **結果を新しい cap として再投入**すると、この有限集合の証明はそのまま適用できない。AH3 は元ρ* subtreeから chartsを閉じ、最後に一回 AH2を適用する手順の補題である。また、候補を追加しただけでは新しい entry×candidate inequalityは真にならない。その全cross comparisonsを元証拠から得る必要がある。

## 5. CH8/ECへの実適用と actual-history側の最初の未完了case

uninterrupted staged/direct extrusion では EC1 の c(a,σ) が各 single keyの witnessed valueを供給する。同じ keyの別 occurrenceは同じ値なので Wをsingletonに取れる。EC1のselected entry proofが上の全 charts、EC2のclone-parent chainsがpublication後の cross-parent conditionになる。従って AH2 は EC1/EC2を含み、複数の正当な候補がある場合にはsingletonという制限を外せる。

CH8の実 y.lower=L に対しては、actual boundary callから低い Qとleaf inequalitiesがある。CH6で解釈したQは同じ全usesで共有される。これはinput term Lのchartを供給する。fresheningが高leaf a_iを複写しても、実both-list copyの a_i≤b_low（またはdual）が cross-parent inequalitiesを供給する。古いbinding/worldを変更する話ではなく、このnative familyの同じρ*の話である。

しかし新 after extrusionがaのselected listから別payload Uを読むと、必要になるのはinput Lのchartではなく

```
for every candidate w of copy(a,σ),
  copied-U chart ≤ w                  (σ=+)
  or w ≤ copied-U chart               (σ=−).
```

CH8のQが作られたcallと、Uが挿入されたcallが異なる場合もある。元parent linksとCH6から **untransformed** Uとwの適切な比較を得る場合、AH3でchartを生成できる。ここでさらに生成したleaf candidateが別payloadのtarget candidateにも加わるため、全cross比較を閉じる必要がある。各entryに一個のfactorがあることからこの矩形closureは従わない。

実constructorの最初の未完了欄は after

`extrude(a,σ,k).selectedList.map(extrude(_,σ,k))`

の **memo hitで以前登録した同じcopyへ新selected payloadのchartを追加するcase**。source由来はCH1の E client-request insertionと、その後の実source Let/LetRec lookupのboth-list fresheningである。原programの任意clientがこのoriginを持ち得ることはSU/CHで量化済みだが、別historyのそのa/keyに対するoriginal-row/subtree witness relationは本稿では全域に構成できていない。cacheは新しいpayloadを再処理した証拠にしない。

互いに衝突し得る義務を正確に書くと、same destination positive copy cに対する

`p_i≤c≤w_1`、`p_j≤c≤w_2`、および全transported selected payloads `U′_r≤c`

である。p_i≤w_1とp_j≤w_2だけでは足りず、p_i≤w_2、p_j≤w_1とselected-entry chartsが要る。AH2はこれらを満たすときのcを明示した。満たさないactual source/historyは今回得ていないので、これは coverageの反例ではない。payload/keyの違いを無視して二つの無関係なextrude callsの値が異なることを反例にもしない。

## 6. 親への適用・残余・次の責務

新しい成果は、P1のfinite regular interpolationと、many-to-one copy relationに対する **全memo/全selected entriesの明示的同時valuation constructor AH2**。親の「各candidateと互換な値を選べる」というexistence premiseは、有限 subtree witnessesと矩形inequality checksに置換できる。candidate valuesを元ρ*のterm/subtree解釈として保持し、AH1の有限graphで一つの結果を作る。共有low rowは一回だけ構成し、全usesで同じ値を使う。

全 earlier-Y=T historyへの適用はOPEN。未完了はmodelの再選択ではなく、source event/operation/memo/useでindexしたafter-row→original witnessesの全域生成と矩形closure。元CH6は全originalLet/LetRec履歴を既に修復しているため、その同じ定理を再度残余にしない。CH8は実 low factorを既に供給しているため、単なるlow-factor存在も残余にしない。新afterselected traversalと異なるlookup-time snapshotへのその **共同**供給が残る。

次のin-scope ownerはactual native event relationのproducer。必要な証拠は、各after parent fiberに対して全候補capsが同じoriginalparent/clone derivationの保存linksで全fiberを拘束すること、またはAH3で生じるcross comparisonの別の実supplier。falsifierは一つのactual source-derived sharedcopyで上のcross inequalityを破る全before modelと全actualafter selected obligations。proof mapが未構成であることをsource counterexampleへ昇格しない。source receiving/SCC資格、fullYulang semantics、原A/B、principality/terminationは維持する。

## 7. Handoff/checks/STOP

Contract SHA-256 `741a7041254bbbb7916d0c7970abb1c8f9d7125b6a749d956c27b0a7f2a5c259`。17 frozen inputsをbyte hashで照合し全一致。中心依存：CH0–8 `5e8479d3c9272f08e7b99213f9b1fc502f7fffc0e5e4a5b3d38eee1035c3a894`、SU/EC `f21c438b0ed20a5bc2218fd3b6bfc3e2a1b360dbef535b0ee6a9dac2891c10e8`（両者primary著、独立査読済みscope内）、P1/NLとpinned Typer.scala。primaryの補間構成への助言を含む本稿は独立査読前。primaryのmoving companionは未読・未依存。

三stages：event/key obligations、regular witness amalgamation、actual source/native applicationとexact boundary。190秒予約、延長なし。requested inheritedAstra/medium、observed model/effort/elapsed UNKNOWN。read/hash/数学と本稿だけのwrite。tests/build/probes/compiler/network/Git/scratch/descendantsゼロ。唯一の新pathは本稿。**writes STOPPED at freeze; no descendants**。hashは外部handoffへ返す。
