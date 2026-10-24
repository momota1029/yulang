# 現 world の joint cell による handler 分岐の保存

Assignment-ID: CORRELATED-HANDLER-OBS-20261024/r1
Author: `/root/astra_scoped_join`; descendants: none.
Status: 未査読の候補機械上の構成的証明。source/native 対応、全言語健全性、production authority は OPEN。
Post-freeze review: r1 は指定された有限候補 graph の範囲で独立査読 ACCEPTED、BLOCKING/MAJOR 指摘なし。[査読記録](../../tasks/agent-loop/sprints/correlated-handler-20261024-outcome.md)を参照。この receipt のみ primary が査読後に追加した。
Contract: `tasks/agent-loop/sprints/correlated-handler-20261024.md`, SHA-256 `f2debbf830e4b4726af992ec6d1817090fbbd8d493c9f15c76b43c4699ae306e`。
Baseline: `d52c2c48e0e876be4e3e6588e2b1b3b4b27933ea`。
Requested model/effort: Astra/medium; observed model/effort/duration: UNKNOWN。

## 1. 元の親と今回閉じる成分

元の親は承認された source 領域の任意の型導出と有限実行 prefix に関する全言語健全性である。Simple-sub A/B、自然な推論、主型性、停止性、独立した foreign continuation の量化はそのまま残す。本稿の局所結論は、固定有限 interface の修正候補機械における CO3-OBS、すなわち joint cell の query から handler の真偽両分岐と後続 inclusion を構成することである。旧証明書や全 raw source の graph 生成を認証しない。

共起の訂正は、動作原理から同じ共変位置の変数表示を説明するものである。`'e?` の独立意味論、任意の A_all、別 receipt/provider/route の同一視を導入しない。保護解除は元の Origin と actual route の H、現在の L/activity を使う。

以下の依存を S、O、CM と略記する。

* S: `docs/yulang-source-type-safety-ja.tex`、R-Project、W-Eligible。
* O: `docs/yulang-operational-type-safety-ja.tex`、候補検索、wait、No/Yes の接続。特に 1652–1659 行の pending event と再観測。
* CM: `notes/theory/2026-10-24-corrected-machine-simulation.md` revision 2、joint diagram、Refine/Refresh/Extend/Fork、current-world Rejoin と修正 graph。

CM の局所 simulation と Rejoin は、その列挙された action と有限 interface の前提内で再利用する。本稿は CM の「filter は単調」という記述を、以下の具体的な二分岐構成と handler path の帰納へ展開する。

## 2. 同じ cell における query の導出

固定 interface I の joint cell c は、同じ pending packet q、候補 h、現在 world に関する named register の equality partition と Boolean diagram を持つ。各 witness 行は、scope s、immutable Origin、receiver r、route identity、H membership、対象 packet への membership を一緒に保つ。hidden witness は完全な行 vector β ごとの occupancy e_β を持つ。別列の marginal を直積して witness を作らない。

一行 w について、S の R-Project を次のように因数分解する。

```
Z(w)    = ∃t∈H(w). L(s(w),t) ∧ Match(t,s(w))
Live(w) = Prot(w) ∧ ¬(Act(r(w)) ∧ Z(w))
D_j(w)  = 当該 packet/candidate に必要な元の receipt/Path/Observe/incidence/activity 条件
F_j(w)  = [r(w) ≠ owner(h)]
P_j     = ∃w. D_j(w) ∧ Live(w)
PF_j    = ∃w. D_j(w) ∧ Live(w) ∧ F_j(w)
```

D は元の query の残りの activity 条件を全て含む。Act が偽で Live が真に戻るだけで expired evidence を有効化しない。Match は同じ Origin と target の capture table の同じ行で成立する関係であり、scope 名や family の一致だけで代用しない。実際の現在 state x から作る α_I(x) では Z を実関係から評価する。hidden endpoint を有限 table で表現し切れない場合、Z は joint な derived bit として保持/Refresh する。unary marginal から決定するとは言わない。

**補題 H1（query exactness）。** α_I(x) の named 行と occupied hidden vector に上式の連言を適用して disjunction を取ると、実際の同じ x,q,h の P_j、PF_j に等しく、PF_j⇒P_j。

証明。具体 witness population を named singleton と hidden 完全 vector の領域へ分割する。各連言は領域内で一定なので、その存在は対応 occupancy と同値。PF の各証人はそのまま P の証人である。L/H/Match と owner equality は同じ行で評価しており別証人を合成しない。□

Base=Act(h)∧Act(owner(h))∧RoleAllows(q,h)∧Covers(q,h)。GC/GW は同じ現在 query の receiver-local Path と instance/direct port による authentic grant。これらは別の permission witnesses を許す元の式に従い、勝手に protection witness と同一と要求しない。ただし各 grant の内部 Path/receiver/instance の連言は同じ witness のまま保つ。

従って S の W-Eligible は cell の全域 Boolean 関数

`e(c)=Base(c) ∧ (¬P(c) ∨ GC(c) ∨ (GW(c) ∧ ¬PF(c)))`

となり、α_I(x) 上で実 eligibility と一致する。query は world、Origin、grant、event を更新しない。

**補題 H2（固定 scalar の完全分類）。** 同一 cell の Base/GC/GW について以下が成立する。

| 条件 | e |
|---|---|
| Base=0 | false |
| Base=1, GC=1 | true |
| Base=1, GC=0, GW=0 | ¬P |
| Base=1, GC=0, GW=1 | ¬PF |

最後の行は PF⇒P より `¬P∨¬PF=¬PF`。これは cell ごとの場合分けであり、無関係な代替全体で scalar を固定する許可ではない。全 cell 集合をこの四領域に分割してから各式を適用する。新 candidate、world 変更、path 変更では分類自体も再計算する。

## 3. 真偽両 filter と十分な抽象化条件

有限 cell universe S_I に対し b∈{0,1}、

`F_b(X)={c∈X | e(c)=b}`

とする。両方を保持する。各 F_b は任意の union を保存し、F_b(∅)=∅、冪等で、`F_0(X)∪F_1(X)=X`、両者は互いに素。証明は同じ c の membership 展開による。e 内の否定は集合 X を補集合にする操作ではないので、X⊆Y⇒F_b(X)⊆F_b(Y)。

**最小 lost-branch discriminator。** 同じ Base=1, GC=GW=0 の二つの syntactic cell c0,c1 を取る。c0 には qualifying live witness がなく、c1 には一つある。c1 の行は Prot=D=Act=1、Z=0、同じ固定 scope s とする。c0 の対応 occupancy は 0、c1 は 1。他の query scalar は同じ。保護観測だけの略記なら U(c0)=∅、U(c1)={s} である。

`F_1({c0,c1})={c0}`、`F_0({c0,c1})={c1}`。

U を union して一つの protected state にすると true branch が消え、intersection すると false branch が消える。これは候補 finite diagram の情報損失であり、二 cell の actual source reachability は主張しない。実 query を一般の scope set U に置換する証明でもない。

既存 scoped-join の α=(intersection tags,union protections) と正の antichain は Stamp/Protect/Release の後の所定の観測だけに対して正しい。F_0/F_1 と handler action は継続言語を増やす。特に一つの existential may-P の否定は、各代替に filter をかけた結果と異なる。既存定理からこの拡張の congruence は出ない。

その検査条件も明示できる。cell quotient π:S_I→Q が両 filter と可換であるための必要十分条件は、各 π-fiber で e が一定であること。十分性は `ē(π(c))=e(c)` を定義し membership を展開する。必要性は同じ π(c)=π(d) で e(c)≠e(d) の singleton 二つを調べれば矛盾する。全後続 relation R も exact に quotient する十分条件は、同じ π-fiber の c,d で `{π(y)|c R y}={π(y)|d R y}` が全 action について成り立つこと。この場合、各 action と filter の image が π と可換となり、列長への帰納で全 finite trace の quotient 観測が一致する。これは有限 table 上の確認可能な追加条件であり、native weight が満たすとは仮定しない。

## 4. action と Rejoin の関係、正しい二つの検索 path

各 port の型を保つ有限 relation R⊆S_I×S_J に対し、`R[X]={d | ∃c∈X.c R d}`。relation composition は `(R;Q)[X]=Q[R[X]]` とする。image は任意の union を保存し、composition は結合的で両側の relation union に分配する。filter は対角 relation `{(c,c)|e(c)=b}` と見なせる。

Rejoin は保存済み immutable projection i と現在 ambient cell a の **joint pair** (i,a) から union-interface cell d への有限 relation J である。J は、d の immutable restriction が i、現在座標への restriction が a、共有 identity/sort equations が整合する全 diagram を列挙する。過去の L/activity/query は i に含めない。i は pending packet 自身の route population に制限される。Rejoin の入力集合は pair の関係であり、独立 marginal の直積を exact と呼ばない。直積で余分な組合せを許す実装ならそれは overapproximation であり、ここでの union law は joint-pair 集合に対する image の法則である。

以後の準備 relation Prep は必要な candidate/owner endpoint を Expose/Refine し、現在の L、D、Z、F、grant query、Base を equation で更新または Refresh する。現在表現していない equality は fresh comparison column として列挙し、古い candidate の F を次 candidate にコピーしない。

候補 index は固定 finite graph の control node/slot であり、実 runtime identity と混同しない。具体的 handler path を次のように分ける。

| graph edge/path | 読む状態と結果 |
|---|---|
| Search_j → Skip_j → Search_k | `F_0; Next_{j,k}; Prep_k`。arm を実行せず残りの候補へ移る。Next が検索 context/owner を変えれば activity も更新する。 |
| Search_j → Attempt_j | `F_1; Invoke_j`。元 pending packet の Imm を保持し、arm/guard/default を候補の外で実行する。 |
| Attempt_j → Attempt step | arm の現在 world を通常 action relations で逐次運ぶ。新 event はその event の経路へ送る。元 pending event を新しく seed しない。 |
| Attempt_j → Yes → Result | 正常 Yes result と現在 world を結果 port へ送る。未実行の残り検索へ元 request を送る規則ではない。 |
| Attempt_j → No → Search_k | 現在 world と元 Imm の pair を J で Rejoin、`Next_{j,k}; Prep_k` を適用し、その後で `F_0/F_1` を両方かける。k は元の残り arm/候補に応じた slot。 |
| Search exhausted → Forward | 残り検索がない具体規則に従い元 event と継続 frame を外側へ送る。元 Origin/route を fresh emission に置換しない。 |
| Attempt request/capture → resume → pending return | revised CM の world-threaded action と Rejoin を使い、現在の世界で上の No/Yes path へ接続する。foreign code 自体の契約は別前提。 |

No は eligibility false ではない。前者は e=1 を通った computation の正常タグで、後者は arm を起動しない query 結果である。型付き result tag と eligibility bit を同じ Boolean として表現しない。

**補題 H3（No の current-world 復帰）。** 元 packet q を保存し、arm の有限 computation が world y で No を返したとする。CM の action relations がその実際の有限 prefix を含み、q の immutable evidence が保持されるなら、上の No path は y での元 q と次候補 k の実 cell を含む。

証明。current-world port は各 arm step の出力を順に受ける。CM Rejoin 補題により (Imm(q),α(y,current operands)) から実 joint cell が J に含まれる。実 Next の context/slot 更新と Prep の concrete comparison は、定義式または Refresh の列挙に含まれる。H1 によりその実 cell の filter は y,k の実 eligibility と同じ。□

具体的 discriminator として、保存時 H(w)={t}, Prot=D=Act=Match=1、(s,t)∉L を取り、最初の候補 j では GC=1 として arm を起動する。arm 中の actual crossing が L に (s,t) を追加し、No を返す。次候補 k では Base=1,GC=GW=0、他の選別条件を維持すると、現在 Z=1 なので P=0、e=1 となる。古い L/Z を復元すると P=1、e=0 となり次 branch を落とす。独立 scope が残る場合はそれにより P=1 のままでもよく、全保護が解除されたとは推論しない。これは修正候補 action の状態 discriminator であり、source program による到達性は未証明。

## 5. 有限 revised graph に対する branch/successor inclusion

有限 control graph G の各 node v に有限 joint-cell universe S_v を割り当てる。edge は §4 の filter、action、joint-pair construction、Rejoin、Prep および CM が局所 simulation を証明した relation である。saved pending data と現在 world を扱う際は、実行 configuration の finite abstraction にその joint coordinates を含める。関係を使わず二つの unrelated predecessor fact を exact に結合する規則を加えない。

initial set I_v と edge relation R_e を固定し、node sets X_v の closure 条件を

`I_v⊆X_v`、`R_e[X_v]⊆X_w  (e:v→w)`

とする。各 universe が有限なので、空集合から seed/edge image を union で追加する反復は有限回で安定する。これを TABLE と定義する。

**定理 H4（TABLE 内の exact path semantics）。** TABLE_v は、この **有限 relation graph 自身** の seed から v への有限 path の image の和集合と等しい。

証明。path 長の帰納で全 path image が各 closure solution に含まれる。逆に各反復で追加される要素は seed または既に構成済みの有限 path に edge を一つ追加したもの。有限安定点は両包含を満たす。filter の真偽 partition と relation composition の法則により、Search/Attempt/No を展開した path でも同じ。□

**定理 H5（具体 branch と successor の保存）。** 修正候補機械の有限実行 prefix を固定する。初期 α が seed に含まれ、各実 action が上記分類された relation を持ち、有限 interfaces が現在 query/pending data を表すなら、prefix の各地点の実 α は対応 TABLE node に含まれる。実 query の真偽 branch と、実 arm の Yes/No/request 後続も含まれる。

証明は prefix 長の同時帰納。通常 step は CM の local simulation と edge inclusion。query step は H1 により実 c が正しい F_b に残る。false branch は Next/Prep、true branch は Invoke が実 successor を含む。arm の各 step は帰納仮説から現在 world を運ぶ。No は H3、Yes/request は現在 result/event relation と CM の route creation/preservation を用いる。resume は CM の現在世界入力を使い、独立した source/foreign continuation introduction 契約を仮定する範囲だけに適用する。TABLE は closure を満たすので各 successor が次 node に入る。□

H4 の exactness と H5 の片方向 inclusion を混同しない。Refresh、hidden multiplicity、unknown alias の列挙は実現不能な cell/path を含みうる。TABLE の全 path が concrete trace になるという逆方向はない。global L、実 identity 数、stack を有限に制限した定理でもない。旧小 annotation/certificate がこの TABLE の inclusion を満たすことは別検査であり、本稿から導かれない。

## 6. 親への適用、未解決 owner と反証条件

候補機械の CO3-OBS は、H1–H3 により「実 query の joint 情報」「真偽両 branch」「No 後の現在 query」まで具体化された。H4–H5 により、その指定 revised graph の全有限 path に接続できる。これにより、単独 may-protection summary から Boolean handler decision を推測する隙間がなくなる。typed receipt recipe は Match の同一 tuple 条件に使用できるが、これだけで全 source がその recipe を生成するとはしない。

| 残る TODO / owner | 必要な証拠と exact falsifier |
|---|---|
| CO3-GRAPH: primary/source graph generation、O handle/wait と S W-Eligible/N-Transfer/R-Cross | 実際の生成 graph が両 F_b、Invoke、No の current-world/Rejoin/Prep、Yes/request edges を含むこと。falsifier は具体 α successor を一つ落とす edge、または No から stale query に戻る生成規則。 |
| CO3-NATIVE: `ConstraintWeight::parallel_union` と downstream consumer、native replay/context owners | 実 weight の解釈が H1 の joint cell と both-filter/action congruence または sound inclusion を保つこと。falsifier は §3 の二 branch の一方消失、別 receipt の guard/owner predicate の混合。今回 native source inspection/implementation は行っていない。 |
| CO3-REJOIN: pending packet/capture/resume owner | immutable route/H/Origin を保存し mutable world を現在 port から供給する実対応。falsifier は §4 の No/current-L discriminator、または新 candidate に旧 F/GC/GW をコピーする遷移。 |
| ORIGINAL-SOURCE / F1/FK1 | 全 surface/source elaboration、元の accepted behavior、foreign continuation introduction と typed responses/reentries を独立に示す。local handler path をその代替証明にしない。 |

implementation は除外されている。これは最小 read-only source/table evidence TODO であり、compiler、tests、semantics の変更許可ではない。generation、accumulation、propagation、levels、extrusion、qualifying intrusion、generalization と witness/provider/residual の独立量化を弱めない。全言語親、natural inference/主型性、production は OPEN。

## 7. 凍結入力、帰属、資源、停止

以下の SHA-256 を現 worktree bytes と照合し全件一致した。

| Input | SHA-256 |
|---|---|
| scoped-weight join | `6e69a697e4d1268ab6048f43f5a36d3f1b7635bdde4c3683346bb6a8179c9bed` |
| source recipes | `ee99b45dbc49c3563220335b350814ed422bf0fbe7edfcb4cfaef476da986cdb` |
| corrected machine simulation | `fffb4f1540739020a0702d4f7b07d41cd9b68a9063f36d24292914b84e6b606d` |
| semantics/soundness guide | `3db3211294e76f74590fa188409c4adca8cf629c2c90788d50a6f70d10657036` |
| operational tex | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| source tex | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |

join 本文の producer は本 worker、primary の査読 receipt を含む凍結版を依存とする。recipe は primary。CM revision 1 は `/root/astra_corrected_machine`、revision 2 repairs は primary、既存独立査読の範囲を拡大しない。原稿は各 frozen file の既存帰属に従う。再利用は revised joint diagrams と current-world simulation の実前提内のみ。旧 stale snapshot、route/event collapse、missing witness insertion は再利用しない。

三段階: frozen source/query audit、both-filter/action 構成、graph induction と親適用。上限 190 秒、三段階、全予約を charge、observed active duration UNKNOWN。検査は hash、指定式の直接読解、数学的導出、artifact fence/whitespace の静的 inspection。tests/build/compiler/network/Git、独立査読は実施していない。

新規・scratch path は本ファイル一つのみ。final message が唯一の handoff。r1 凍結、全書込み終了、descendants ゼロ、worker STOPPED。次は Luna intake と fresh independent review、CO3-GRAPH/NATIVE/REJOIN の owner evidence。親は OPEN。
