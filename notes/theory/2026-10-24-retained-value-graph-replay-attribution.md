# 保持 Value グラフの SCC と replay の境界経路

RETAINED-GRAPH-REPLAY-20261024/r1。著者 `/root/astra_corrected_machine`。
Baseline `14860b9ba4792c74bfb4d8610cc3ff10b5d0578f`。
具体的 graph/provenance 構成。凍結 r1 は独立査読で記載した条件付き範囲に BLOCKING/MAJOR 指摘なし。査読後の変更はこの状態行のみ。[査読範囲と hash](../../tasks/agent-loop/sprints/retained-graph-replay-20261024-outcome.md)を参照。原 Simple-sub A/B、完全 source/Call、独立使用の量化を維持する。
契約 SHA256 `e91b05d5274ea45d43a5c1cb3034665f876dd8eb9495a12a348e749f9d2366bb`。

## 1. 今回取り出す graph

```
let top = lambda h.
  let rec f = lambda x. (lambda z.{a=x})(h(f x))
  in {a=succ((f 0).a), b=(f true).a}
in top
```

前稿 BR の scalar store と primary PR1–PR3 は凍結入力である。本稿は実 compiler を実行せず、保持 constructor の graph を数学的に展開する。元 Scala AST と Yulang LocalSource の同一性は仮定しない。以下では「definition top の RHS を source root とし、対応する LocalSource の Name/Apply/Lambda/Record/FieldTail/Block を持つ場合」の constructor 出力を明示する。この rooted correspondence 自体が実行済み HIR artifact で認証されたという意味ではない。

P=top definition、F=local f、H=parameter h、X=parameter x、L=wrapper Lambda expression、K=Record(a=x) expression、U=f x result、V=h(f x) result、W=L(V) result。Q0=f 0 result、Q1=f true result、A=succ((f 0).a) result、O=outer record expression。S=succ の resolved declaration、T_bool=true の resolved declaration が graph.resolved の対象になる場合だけ、それらの頂点も存在する。type row T（B の copy）とは区別して T_bool と書く。

Graph::Value は Module/Local/Parameter/CatchBinder/Expression (`candidate_value_graph.rs:5`)。型行 o,B,R,C,D,T はこの集合に加えない。unused formal z は semantic source の binder であっても、この graph constructor では Name 参照がないため intern されない。f の Lambda expression も、callee に直接現れず expression result を intern する分岐もないため、F と別の graph 頂点として生成されない。L は wrapper Call の receiver なので intern される。

## 2. 全隣接表と生成時レベル

### 2.1 実 constructor の semantic-vertex projection

`candidate_value_graph.rs:99–216` の owner walk と `:218–306` の fragment helper を縮約する。helper 内部は source 真部分木に向かう DAG。Name helper の末尾だけが resolved semantic Value に入る。semantic-to-semantic 道を helper-only segment ごとに切れば、下表の辺と双方向に対応する。helper を semantic Value として扱わず、birth を付けない。

| vertex | source birth（導出値） | outgoing semantic incidence |
|---|---:|---|
| P |1| S が resolved なら S（FieldTail の注意を下記参照） |
| F |2| F,H,X |
| H |1| ∅ |
| X |2| ∅ |
| L |2| ∅ |
| K |2| X |
| U |2| F,X |
| V |2| H,F,X |
| W |2| H,F,X |
| Q0 |1| F |
| Q1 |1| F、および T_bool が resolved なら T_bool |
| A |1| S が resolved なら S |
| O |1| S が resolved なら S |
| S,T_bool（存在時）|外部 constructor 由来、ここでは数値未認証| この closed builtin 例では source 内への辺なし |

F の自己辺は実 recursive Name。F→H は実 h Name、F→X は f x と wrapper record の x Name。W の fragment は callee L を透過しない。argument V の nested Apply fragment だけを通って H,F,X に達する。従って W→K,W→L,W→U,W→V はない。V→U もない。K→X は Record field helper による。Q0/Q1 は f の型使用コピーとは異なる source result 頂点であり、F へ Name incidence を持つ。

**実装の FieldTail 境界。** この表は graph constructor を忠実に読んだ表である。`candidate_value_graph` の owner walk に FieldTail case はなく、fragment の対象にも FieldTail はない。一方 `candidate_source.rs:1261–1262` は FieldTail.receiver を訪問する。従って `(f 0).a` と `(f true).a` の内部 Name は graph の owner walk では訪問されず、P→F や P→T_bool はこの walk からは生成されない。全 expressions を走査する第2 pass は Q0/Q1 とその fragment を生成するので、Q0→F,Q1→F は存在する。選択結果の独立 graph vertex はこの constructor では intern されない。A と O の fragment も FieldTail を通過しないため、A→F,O→F を補わない。

定義 root が source-owned body の全 resolved Name を所有する元 authority に従う semantic graph では、FieldTail を普通の子として辿って P→F と、Name として resolved なら P→T_bool を加える。これを現在の保持 graph に既にある辺とは呼ばない。差分は明示した二種の辺であり、下記 SCC 結果はどちらでも同じである。

top をさらに外側の local Let として一つの source に入れる場合、default owners は outer source root になる。FieldTail 未訪問の Q0/Q1 はその default owner を持ち、P とは限らない。このため above whole-source associations をその representation に無条件転用しない。内側 U,V,W の owner は訪問される F なので、この違いは争点の3 seed に影響しない。外側最終 Name top の source root E が別にある場合は E→P のみを追加し、戻り辺はない。

### 2.2 birth の由来と保持の限界

上の数値は現在 row level の読取りではない。`candidate_source.rs:1204` の source RHS visit level1、`:1274–1339` の lambda/formal 同 level、`:1347–1368` の nested initializer level+1、`:1515–1527` の initializer visit から constructor 時点の値を導出した。原 Scala の top RHS/f RHS の level と一致する。Names は resolved Value の同じ birth を使う。

しかし現 `Graph` (`candidate_value_graph.rs:10–25`) は birth field/map を持たない。別の component_levels/parameter_levels は solver component/parameter position を key にし、Graph::Value から immutable birth への全域 joint map ではない。したがって「現 Graph 一個から arbitrary source の birth-induced SCC を計算できる」は成立しない。上表では source constructor の derivation を添付して初めて数値を与えた。external S/T_bool の出生数値を primitive type level0 から捏造しない。

## 3. SCC を実際に取り出す

**RG1.** 上表の全 semantic SCC は singleton。FieldTail authority 差分 P→F,P→T_bool を加えても同じ。

証明。H,X,L と閉じた builtin 頂点は出辺なし。F からは F,H,X にしか行けず、F 以外へ進むと戻れない。K,U,V,W,Q0,Q1,A,O はそれぞれ表の target へ進むだけで、それら自身へ戻る辺はない。P の出辺先から P に戻れない。任意の非自明 cycle の最初の頂点をこの場合分けに当てると矛盾する。よって自己 cycle F→F 以外に cycle はなく、全 singleton が最大強連結集合である。追加 E→P も同様。□

誘導 graph G_2 は F→F,F→X,K→X,U→F,U→X,V→F,V→X,W→F,W→X の辺を残し、H への辺を filter する。G_1 では Q0/Q1→F は filter される。external birth が未認証でも、external から戻り辺がないので singleton という結論は不変。全 path の頂点を filter したので equal-endpoint-only shortcut ではない。

| source checking seed | association | induced SCC verdict |
|---|---|---|
| e_r: f x | F/F | 真。birth2 の同一 singleton |
| e_h: h(f x) | F/H | 偽。birth2/1、かつ異なる singleton |
| e_w: wrapper App | F/L | 偽。birth2同士だが異なる singleton |
| outer f0/ftrue（top RHS root representation） | P/F | 偽。birth1/2、異なる singleton |
| succ Call | P/S（resolved時） | 偽。戻り道なし、異なる singleton |

FieldTail の default-owner 問題を含む別 representation では outer seeds を actual default E に置き換える必要がある。それでも E と F の戻り道はなく偽。wrapper/result を F に alias して e_w を真にすることは、この graph に反する。

`Graph::qualifies :340` は現状、全 graph の component equality のみを比較する。本例では RG1 により新旧どちらでも上の真偽になる。これは新 birth-level rule の一般的実装対応が済んだという意味ではない。

## 4. Pair と保持された ordered provenance graph を join する

### 4.1 保持データは source union 以上のものを持つ

Parent は copy,parent,polarity,target,sources,comparison:TypedPairKey,occurrence を保持する (`candidate_intrusion.rs:53–61`)。PairGroup は occurrence と実 pair range、by_output は `(comparison,output)`、Reuse は group,sources,new occurrence を持つ。Parent 単体には RelationId がないが、それだけで全経路情報が失われたとは言えない。

`candidate_context::Dependency :331–365` は Derived、FunctionPort(field)、RecordPort、**順序つき Replay(child,lower,upper,lower_input,upper_input)**、Transport(use_origin,witness) を保持する。Origin は実 source occurrence と relation を持つ。`BoundAdmission :560–570` は bound,origin,relation と `ExtrusionLink{processing:Option<RelationId>}` を、BoundEmission は exact physical slot/readback を保持する。従って lower と upper の経路は区別できる。CircuitEvidence::dependencies/origins/bounds はその同じ retained graph を公開する。provenance DAG を新しい Value-reference edge に変換しない。

### 4.2 この fresh pair に対する具体的な逆引き

前稿の scalar cut は

```
r_r : o <= Function(B,R)       source e_r
r_h : H <= Function(R,J)       source e_h
u   : R <= C                  ExtrusionLink from r_h
r_c : Function(B,W) <= o       f completion
v   : W <= R                  FunctionPort(Result, Replay(r_c,r_r))
l   : Record(B) <= R           Replay(Record(B)<=W, v)
p   : Record(B) <= C           Replay(l,u)
a   : B <= T                  fresh positive ExtrusionLink while processing p
```

これを actual contextual records 上で認証する query は次の有限 relational join である。endpoint correspondence を満たす実 source actions が成功してこの graph を作った cut に適用する。scalar notation だけから live record ID を捏造しない。

1. 争点の Parent が copy=T,parent=B,polarity=+,target=1 を持つことを照合する。
2. direct link `BoundKey(B,Negative,T)`（Value upper side）を持つ BoundAdmission のうち、cause=ExtrusionLink{processing:Some(p)} で、対応 BoundEmission の physical slot/readback が同じ B≤T を示すものを選ぶ。`candidate_extrusion.rs:134–139` が pair retention の直後にこの link を生成するので、fresh T・未 quotient/rollback の今回 cut では creation emission が一意である。後続 ordinary emission と区別する。
3. p の pair が Record(B)≤C であること、Dependency::Replay の upper_input が R≤C の physical bound key、upper relation が u であることを照合する。lower=l も独立に照合する。単に p.sources に e_h があるかを調べる操作ではない。
4. u の bound admission/emission の ExtrusionLink processing を辿る。初回 C が R の positive copy として作られた exact group/parent `(C,R,+,1)` と比較し、r_h の actual Source Origin が h Call の checking であることを確認する。
5. checking→event→Association を辿ると e_h=(F,H)。別経路 l→v→r_r の source checking は e_r=(F,F)。RG1 の component lookup を二つの association に個別適用する。

**RG2 (retained boundary query).** 上記実 emission/Replay 前提の下で、争点 fresh copy の target C に至る direct upper extrusion-link 境界の association は一意に F/H、lower の recursive-return route は F/F と判定できる。

証明。fresh C は r_h の今回 copy であり他の copy creation と identity が異なる。u の cause と physical bound の一致が r_h を固定する。p の ordered upper_input はその u を指定する。fresh T の creation link は p を固定する。各 join は同じ actual object identity を使い、graph の SCC は RG1 により計算済みである。lower の route は FunctionPort.Result と replay parent r_r の順序つき証拠によって固定される。従って source support union の順序や set iteration に依存しない。□

この構成により「保持情報が union だけなので h 側を戻れない」という主張は否定される。boundary query は既存 ordered DAG で表現できる。Parent.comparison が RelationId でないことも、今回 fresh direct-link admission による逆引きで補える。

### 4.3 reuse と認証の範囲

前述一意性は fresh・未 rollback・未 quotient の fixed cut に限定する。general memo reuse は original PairGroup/by_output と新 Reuse occurrence を参照し、再利用された output と新 processing context を照合する必要がある。`recapture_candidate_extrusion :388–422` は original Parent を書換えず distinct reuse を作る。fresh T creation link を全 reuse の processing relation と同一視しない。BoundAdmission/FreshUse/BoundTransport と snapshot/coverage がこの区別のために保持されている。裸の row ID から retired snapshot を復元することはしない。

## 5. 実 consumer の答えと元の operation の答え

現 consumer は `retain_extrusion_parent :324–326` と recapture で、source set の **いずれか**の event が qualifies なら pair を pending に入れる。p の support は lower経路の e_r と upper経路の e_h を含む。RG1 で e_r=true、e_h=false、e_w=false まで計算したため、実 any consumer のこの graph 上の結果は true である。単なる「どちらかかもしれない」ではない。

一方 RG2 が計算した **target boundary query** の結果は F/H、したがって false。これらは同じ retained graph に対する異なる、実際に評価できる query である。境界 query のための情報は今回 cut に存在する。SCC 自体の計算不足ではない。

元 authority は actual extrusion occurrence の origin/receiver と実 pair の対応を要求する。target boundary query を常にその対応とするという general source/native correspondence は、この code のどの constructor theorem からもまだ導かれていない。現 any consumer をその対応とすることも同様に未証明。新しい ownership policy を選択するのではなく、次の精密な bridge を残す。

**RG-OWNER:** actual structured comparison Record(B)≤C の source interpretationを、保持 ordered Replay と ExtrusionLink の意味に沿って展開したとき、generated pair T/B の receiving Value が、RG2で抽出した C の h-call 境界であることを示す。lower recursive relation はその境界へ運ぶ payload の source evidence であって、別の receiving boundary を追加しないことを original Call/transport rule から示す。

この命題はデータがないという主張ではない。検査対象の data/graph は本稿で具体的に構成した。足りないのはこの query が actual occurrence semantics の receiving boundary を返すという owner theorem であり、その証明を source-set any predicate の実装事実で置き換えない。もし原規則の展開が別の association を与えるなら、それを同じ retained graph 上で示すことが反証になる。ユーザーに新規の意味選択を求める必要はなく、既存 source/transport の証明作業である。

## 6. PR1–PR3 と親への適用

RG1/RG2 により「C は低いから h だろう」という推測を、exact upper-bound creation path の照合へ置き換えた。RG-OWNER が成立すれば disputed pair は非資格、PR1 の独立 B_i と共有 T、PR2 の二使用が適用される。現 any consumer の条件が実際の pair/processing graph に満たされ公開前等置が消費されれば PR3 の Bool≤Int が適用される。いずれも complete original Yulang membership を原 Scala acceptance から導かない。

原 source graph の FieldTail correspondence、全 Graph::Value の immutable birth join、実 source→四port/receipt/Force graph の完成、一般 reuse の認証、RG-OWNER が残る。全証明は OPEN。本稿は source incidence の具体的漏れと birth未保持を記録したが、実装編集はしていない。実装 TODO の falsifier は上表の graph constructor projection と authority の P→F 差分、および birthの異なる同一全graph SCC。所有者は candidate_value_graph/source construction。RG-OWNER の所有者は complete Call/ordered replay transport proof。

## 7. 資源と凍結

三 stages: actual graph extraction、SCC tables、ordered provenance join と適用。190秒固定、延長なし。requested Astra/medium、observed model/effort/duration UNKNOWN。19依存と契約 hash は全一致。静的読取り・数学・この note のみを書いた。tests/build/probes/compiler execution/Git/network/scratch/descendants はゼロ。唯一の新規/変更 path は本稿。著者は `/root/astra_corrected_machine`、査読は primary が独立に任命。最終 SHA は handoff。

**STOP: writes stopped; no descendants.**

## 凍結入力


| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/theory/2026-10-24-birth-level-scc-intrusion.md` | `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/progress/2026-10-14-value-occurrence-intrusion-implementation.md` | `35dca7a9033a52d46367229c0119887b944bc6c0f37a560de74f33da4653c0e5` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `5893555fe89c594feabca200d1d8f26631877200da61e6ae39c80d375f748bb1` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/syntax.scala` | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| `notes/design/2026-10-12-value-reference-copied-row-ownership.md` | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| `notes/theory/2026-10-24-birth-level-replay-intrusion.md` | `7bc8ccee1ee9c0a2ce168e5f1687ae76e7794b097cb3d35dc85ccb5d4f717c5b` |
| `notes/theory/2026-10-24-birth-level-publication-replay.md` | `0e84e618a077b6f3d138707349fbfe51d09e8ccdd54628ad772640f6c12ea244` |
