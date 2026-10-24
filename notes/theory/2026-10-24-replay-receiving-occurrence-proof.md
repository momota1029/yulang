# 完全 Call の receiving incidence と delayed extrusion のラベル

Assignment REPLAY-RECEIVER-PROOF-20261024/r1。Author `/root/astra_scoped_join`、descendants なし。
Status: source placement の条件付き導出、与えられた reduct に対する構造公理の相対的な非含意。凍結 r1 はこの限定範囲で独立査読を通過した。査読後、primary が reduct の入力条件と source-path の語義を明記した。RG-OWNER の一般成立、全 source counterexample、production authority は未成立。
Contract `tasks/agent-loop/sprints/replay-receiver-proof-20261024.md` SHA-256 `122f3fd0c681de36116811ee1c37e959aadbc7a45956dc07ea61a8d583c0b2d5`。
Baseline `aab952fa1c1ecd66c5f785262976de0b9d8727d9`。Requested Astra/medium、observed model/effort/duration UNKNOWN。

## 1. 固定された source と具体 cut

```
let top = lambda h.
  let rec f = lambda x. (lambda z.{a=x})(h(f x))
  in {a=succ((f 0).a), b=(f true).a}
in top
```

F は local f、H は parameter h、e_r は `f x`、e_h は `h(f x)` の actual checking occurrence。definition-root origin は双方 F、resolved callee Value はそれぞれ F,H。f の初期 type B と内側 result R は level2、h 側で作る C と delayed copy T は level1。birth-induced SCC では F/F が真、F/H が偽。これは既存 RG1 の具体結果を再利用し、型行の SCC と混同しない。

前稿の actual retained-cut premises をそのまま固定する。

```
r_r: o <= Function(B,R)       at e_r=(F,F)
r_h: H <= Function(R,J)       at e_h=(F,H)
u:   R <= C                  positive extrusion link, processing r_h
v:   W <= R                  recursive result-port replay
l:   Record(B) <= R           lower result propagation
p:   Record(B) <= C           Replay(lower=l,upper=u)
a:   B <= T                  fresh positive extrusion link, processing p
```

a の BoundEmission/Admission と p の ordered Replay、u の creation processing r_h を照合すると upper route は e_h、lower route は e_r に戻る。これは保持データの定理 RG2 である。今回の課題は、copy pair (T,B,+,1) の original receiving Value がその upper route と一致するという **source-law** の証明である。native source-set-any は e_r を含むので真であり、その事実も固定する。

全 source/Call の original scopes、whole carriers、providers、current worlds、原 receipt/Force、pending suffix、W/Z alternatives、complete futures を残す。ここで扱う cut が全原意味の独立 CompleteMem witness を既に持つとは主張しない。

## 2. complete Call/signature 規則から実際に得る receiver

### 2.1 source Call ごとの固定 index

complete-call contribution authority §5 の `Idx(e)` は source Call、lexical u_f、checking u、ElimOrigin、actual provider/world、reg/route、O0/O1、SpecCall/C0 と κ_e を一つの tuple に保持する。e_r と e_h のこれらは別 occurrence のまま。

`call-source-interface-construction` §4 の FrameCall を二回構成する。

* FrameCall(e_r): callee は同じ f/root、argument は x の whole carrier、receiver slot はその actual f を ExecuteCallable する slot、return は R の source result slot。
* FrameCall(e_h): callee は actual h、argument は **内側 e_r の計算全体**を reify した whole carrier。receiver は h の actual returned provider/current world を使う slot、return は J の別 slot。

後者の `arg` 内に前者の `receiver` が残る。h の argument carrier に内側 f の結果があることは、f の invocation/Force/receipt を消すことでも、h と f の receiver slot を同一にすることでもない。whole carrier の slot は open hole であり、この source Delay はその diagonal section に過ぎない。

### 2.2 構成された placement の式

source-signature incidence §3.2–3.4 の constructor を適用すると、内側 result port h_r の outer placement は、actual dependent field map を省略せず概念的に

```
ρ_inner = inner-result projection/placement at FrameCall(e_r)
ρ_arg   = outer-arg injection ∘ reify/latent injection ∘ ρ_inner
ρ_outer = outer Call enclosing/root insertion ∘ ρ_arg
```

となる。composition の middle telescope は actual result/provider/current world の同じ tuple。これは arbitrary field assignment を satisfying Call tuple にする写像ではない。

PortProv の Operand/Ref/Scope/Rename は元の constituent owner を保持する。Root insertion は actual receiving signature β_r と route を追加する。従って外側の slot に運んでも inner constituent origin はそのまま、outer receiver placement は h Call 側に現れる。Conjunction/Bind は同じ whole tuple、Union は全 branches と実選択 tag を保持し、別 witness の marginal は合成しない。

**命題 RP1（完全 source placement）。** 二つの Call の authentic inputs と local typed field maps が与えられると、inner contribution の original origin と、outer h Call argument slot の receiving incidence を同時に保持する有限 κ/PortProv diagram が構成される。

証明。各 Call の IF-Insert/IF-Use、Delay、Bind、FrameCall を actual source tree の順に適用し、上式の contextual injections を合成する。PortProv の Operand は child partition 全体を tagged copy、Ref は実 antecedent、Root insertion は receiver と route のみ変更する。したがって whole origin partition Ω と β_receiver が区別されたまま残る。source challenge/observation を選ぶ前に構成でき、空 contribution fiber も schema として残る。□

ここで β_receiver は **signature/root placement** の添字、FrameCall.receiver は actual execution slot、extrusion の receiving Value は **別の sort/責任**である。actual call seed では resolved callee が両 source descriptions を結び付けるが、RP1 は新しい solver pair を入力にも出力にも持たない。Ω の origin を extrusion origin に、β_receiver を extrusion receiving Value に自動的に cast する規則はない。

## 3. eager/delayed diagram のどこまでが可換か

R の lower Record(B) が初回 positive extrusion 時点で既にある eager route は、R→C を作る同じ extrusion invocation の polar memo を使って Record の正位置 B を target1 に移す。fresh copy を T_E と書く。direct-linkと transformed lower は

`B<=T_E`, `Record(T_E)<=C`

となる。native constructor はその pair を当該 extrusion invocation の occurrence に登録する。その invocation が source r_h に直接根拠を持つ場合、その seed association は e_h=(F,H)。

delayed route は先に fresh C と R<=C を作り、後から l と u の replay p を処理して新たな extrusion invocation で fresh T_D を作る。得る scalar/link は `B<=T_D`, `Record(T_D)<=C`。T_E↔T_D の fresh renaming の下でこの局所 scalar fragment が対応することと、**異なる processing occurrence の source label が同じ**であることは異なる命題である。

```
R lower Record(B) -- early expand at r_h --> (T_E/B, processing r_h, sources {e_h})
       | delayed lower arrival                         | desired label agreement
       v                                               v
Replay(l,u)       -- expand at p -------> (T_D/B, processing p, sources including e_r,e_h)
```

RP1 は二経路の source payload と outer h placement を同じ diagram に置ける。しかし lower evidence を source graph 内で transport したことから「新しい native extrusion occurrence p の receiver=outer h」と結論するためには、次の **異種 graph 間の式**が必要である。

```
ReceiverOfCopy(p,T_D/B)
 = ReceivingValue(UpperBoundary(p,u,r_h))
```

左辺は solver extrusion の occurrence interpretation、右辺は RP1/RG2 で構成済みの source/retained-boundary interpretation。IF の relational commuting diagrams は source/operator field maps 同士の式であり、この新たな左辺を含んでいない。したがってその可換性を引用するだけでこの式を証明したことにはならない。

### finite/cyclic polar memo の範囲

`candidate_extrusion.rs` は key=(endpoint,polarity,target) ごとの memo を一 invocation 内で持ち、copy を登録してから selected bounds を辿る。正では lower、負では upper、Function child は指定極性を反転する。finite row/structure graph の同一 key は再訪時に既存 copy を返すので、その invocation 内の有限/cyclic traversal は同じ pair identity/occurrence を使う。構造 port を通るからといって各再訪で fresh association を作らない。

しかし eager の同一 memo と delayed の別 invocation の memo は同じ object ではない。一般に双方が同じ copy-sharing graph を作ることも未証明であり、局所 fragment 以外へ alpha 同型を拡張しない。Reuse は元 PairGroup/by_output と新 Reuse occurrence を持つ。元 Parent の immutable fields は保持され、新 processing/source context は新 occurrence に属する。RG2 の fresh creation-link 一意性を reuse 全般に使わない。本稿の次の independence witness は fresh cut に限定するため、一般 reuse correspondence を前提にしない。

## 4. audited structural axioms に対する明示的 independence witness

ここで証明するのは **列挙した構造公理から delayed label equation が導かれないこと**であり、二つの full Yulang semantics、二つの lawful complete source execution、元の preservation 不可能性ではない。

### 4.1 固定 reduct と変える一フィールド

D を §1 の actual pre-intrusion cut のデータとする。source graph/birth/SCC、全 source Call idx/κ/Ω/receiver/receipt、full provider/world/future interfaces、r_r/r_h/l/u/p とその ordered evidence、fresh T_D、a の emission/processing、memo/pair records、source union、native any consumer の計算は全て D に含め固定する。未証明の C0等の evidence を捏造せず、与えられたものは同じまま、symbolic schema は同じまま保持する。

新たな source-native interpretation field を

`SelectedSource(p) ∈ {e | e は p の retained source support の実 seed}`

とする。これは選択済み semantic policy の定義ではなく、未構成 interpretation の一つの model parameter である。原 source seeds については `SelectedSource(r_r)=e_r`, `SelectedSource(r_h)=e_h` を固定する。新 p では双方の seed への ordered evidence paths が D にある。

二つの expansions を構成する。

* D_U: `SelectedSource(p)=e_h`、その whole association (F,H) を新 p の解釈に使う。
* D_L: `SelectedSource(p)=e_r`、その whole association (F,F) を新 p の解釈に使う。

origin/receiver の cross product は作らない。p、T_D/B の actual identity、polarity、target、creation processing は同じ。D_L は literal に p の processing を r_r に書き換えるモデルではない。processing は p のまま、p の source interpretation の選択だけが違う。どちらも original Parent や別 occurrence を書き換えない。

### 4.2 何を axioms として検査したか

| audited axiom/construction | 二 expansions が保存する理由 |
|---|---|
| Actual source resolution と complete Call idx | e_r/e_h の callee、lex/check facets、entry、Force、return/future、C0/κ の全既存 field は D のまま。SelectedSource(p) は source Call 形成の引数にない。 |
| IF-Insert/IF-Use/FrameCall | 全 actual declaration/use slots と typed injections は不変。inner f receiver と outer h receiver を同一化しない。 |
| PortProv/DeclContribution/Root insertion | Ω、original owner、β_receiver、route、whole tuple と license witnesses は全て不変。新 selector を Ω と解釈しない。 |
| Source checking seed association | r_r は F/F、r_h は F/H、definition-root origin F は固定。どちらの source call の規則も変更しない。 |
| Replay retains whole provenance | p の lower=l, upper=u と双方の input keys、retained source union は同じ。選択は保持を削除しない。source union から別 endpoint pair を合成しない。 |
| Actual extrusion occurrence/pair retention | p の fresh extrusion occurrence と (T_D,B,+,1)、one-sided link a、levels/memo は同じ。selector はその pair を別 extrusion に移さない。 |
| Copied-row Value graph rule | type copy を Value vertex に追加せず Value reference を相続/retarget しない。source graph と全 birth は不変。 |
| Birth-induced qualification formula | interpretation の origin/receiver に式を適用する。D_U は false、D_L は true。式を変えず、結論が異なる。 |
| Fixed native any consumer | 両方で sources は同じなので true。native pending/enqueue の観測も同じ。consumer=original interpretation という未証明の対応式は公理に追加しない。 |
| Whole-map/freshening retention | この finite cut には freshening/reuse step がなく、その規則の実 instance は不変。source-name の injective renaming を行うなら selector の実 seed参照も同じ rename で運べる。|

重要な限定として、authority の「actual receiving Value」をこの finite structural inventory が完全定義したとは言わない。上表は origin/receiver を正しく **保持し、資格判定する**規則を満たすが、delayed processing p の actual source interpretation を決定する constructor equation は監査対象規則に見つからない。SelectedSource(p) を一方へ固定する未記載の source-law があるなら、この independence はその追加 axiom を含まない。それを実証明として supply することが次の作業になる。

また上表は **intrusive equality を適用する直前**の同じ unlabelled history を比較する。native any の executionを両方で同じまま保持できるが、それが ideal qualification に一致するとは両方で主張しない。D_U の ideal obligation は非等置、D_L は等置なので、ideal operation を実行した後の unlabelled stores が同じという主張はない。そこまで同じと要求すれば争点の結論を先取りする。

**定理 RP2（限定された相対的非含意）。** 上表の exact structural axioms を満たす reduct D が与えられたとする。新たな interpretation symbol SelectedSource への二つの拡張により、これらの公理と D の保持事実は、delayed pair の association=F/H も association=F/F も一意には導かない。D 自身の full original semantic premises の整合性・inhabitance は、この定理の結論ではない。

証明。D_U,D_L は上表の各 axiom を満たし、原 reduct が同じである。それぞれ real seed support の異なる一要素を保持された whole association のまま解釈する。birth SCC rule による結論は false/true と異なる。従ってどちらかを強制する文は上表からの論理的帰結ではない。□

二つの actual checking seed と ordered retained paths、同じ full source tuples、同じ native emission cut を明記し、変更 field を追加の source-native interpretation symbol だけに分離して全監査公理をチェックした。これらの path は、独立に構成済みの二つの complete source typing witness を意味しない。**full language semantics のモデル独立性**へ一般化しない。

## 5. 親への適用と source-law owner の次の証明

RP1 により、outer h receiving placement は構成済みであり、source contribution の original origins を破壊せずに実際に取得できる。RG2 と合わせて「data がない」「scope level だけで h と推測する」という障害は除かれる。RP2 により、残った論点は SCC 計算や signature slot 生成ではなく、**新しい replay extrusion occurrence の source interpretation と original receiving placement の可換性**そのものと特定される。

eager label は original r_h から得られる。delayed label を一致させるには、original source inference/constraint transport owner が上記 ReceiverOfCopy equation を、実 scalar/typed generation ruleから導出する必要がある。新 policy として上式を宣言しただけではこの proof packet の目標達成にならない。反証条件は同じ retained source/Call tuple を持つ lawful delayed generation が別 receiving occurrence を実際に指定することである。

具体的 TODO **RG-LABEL-COMMUTE**:

1. q_fy/q_h の original source inference derivationと、r_h→u→p→a の生成/処理を一つの typed derivationで対応付ける。
2. 原 source の derived-bound rule が読む occurrence field と、その upper/lower evidenceへの substitution actionを列挙する。IF/Ωを solver occurrenceへ写す実写像をここで構成する。
3. 同一 polar memo 内の structural children と、別 invocation による delayed replay/reuse を別 case で証明する。source interpretationがprocessing/source unionのどの fieldから決まるかを、実 ruleで示す。

owner は original complete Call/source-to-constraint/transport proof。native code owners は `candidate_context::Dependency::Replay`、BoundAdmission/BoundEmission、`candidate_extrusion` fresh-pair/link construction と `candidate_intrusion::retain_extrusion_parent` / recapture。今回 code編集や追加 instrumentationはしない。

RG-OWNER が true なら前稿 PR1/PR2 の非資格 routeへ、falseならその実 source lawの結論へ進む。現 any consumer=true と source interpretation未確定の差を、原 source counterexample として閉じない。全 ordinary generation/accumulation/propagation/levels/extrusion/generalization、scope/Call/history/F1/FK1、A/B/principality は維持して OPEN。

## 6. 依存と資源

契約と26 frozen inputsのSHA-256をactual bytesに照合し全一致。全 manifest は冒頭の frozen contractにある。主要直接依存:

| input | SHA-256 |
|---|---|
| retained-value-graph-replay-attribution | `8adfe10dda01a223c2b289cec81692cd6c92cca66f3170501b96fe894ff5c1c6` |
| retained-graph-publication-consequence | `5ea7d91ece760262af4f1ddd9da6496c25a9a555e4f7d9a7c9279adf782b3574` |
| complete-call-contribution definition | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| call-source-interface definition | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| call-source-interface construction | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| native-signature formation | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| source-signature incidence | `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a` |

RG稿の authorは `/root/astra_corrected_machine`、publication稿は primary。既存数学/authorityの帰属は各凍結入力に従う。本稿は本worker単著、独立査読前。原 complete IF/PortProv の選択範囲だけを再利用し、その source-law theoremをnative extrusion label theoremと読み替えない。旧 source-set-any の実装事実は採用意味の証明として再利用しない。

三 stages: source Call/receiver placement、eager/delayed/memo、有限 independence と親適用。上限190秒、三段階、全予約charge。observed active duration UNKNOWN。静的読解/hash/数学/fence・whitespace inspectionのみ。tests/build/probes/compiler/Git/network/descendantsゼロ。唯一の新規・scratch pathは本稿。final messageが唯一のhandoff。

r1 producer凍結・STOP後、独立査読は記載した限定範囲に BLOCKING/MAJOR 指摘なし。primary の修正は冒頭と RP2 の相対的入力条件・語義の明記のみ。査読対象 hash と最終 hash は [outcome](../../tasks/agent-loop/sprints/replay-receiver-proof-20261024-outcome.md) に分けて記録する。親はOPEN。
