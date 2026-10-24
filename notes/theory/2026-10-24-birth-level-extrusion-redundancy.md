# 同生成レベル Call の子孫にも extrusion は生じる

BIRTH-RESIDUAL-CLOSURE-20261024/r1。著者 `/root/astra_corrected_machine`。
Baseline `c737e06d5d664fcd9d036f7f45c89444cf2f07b9`。
状態: 具体的 native invariant 反例は独立査読で受理された。一般 BRD2 への MAJOR 指摘を受け、primary が cache-miss 前提を補った。修正後の BRD2 の別査読は行っていない。選択された intrusion 意味論や全 source 保存の反例ではない。
契約 SHA256 `530db5ea012a4668d049ac88bd7fdf06c690f20af1aea46250f87efe760874e7`。

## 1. 判定する命題と結果

候補 INV は「origin/receiver の immutable birth が同じ Call の比較から派生する全比較では、target level が訪問する全変数の level 以上なので、実 copy は作られない」である。派生は Call demand、既存 lower/upper の replay、Function port 分解を含む。生成された型 row の ancestry や source support は、actual delayed extrusion の receiving Value と同一視しない。

以下、元 `Typer.scala` の空の native store から、実 source が INV を破ることを示す。型の開始値や bound を人為的に与えない。先行する h Call、後続する同 birth の f Call、再帰完成時の反変引数の replay を全て構文 constructor から導く。前稿の結果 port の record-return 例とは異なり、今回は **recursive argument port** を通る。

## 2. 実 source、scope、全推論履歴

```
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first = h x, next = f {a = y}}
  in f
in top
```

原 `syntax.scala:7–14` の Let/Lam/App/Rcd/Var だけからなる。`Rcd` の field list は first,next の順と固定する。未定義 Name、forward local reference、local mutual recursion、polymorphic recursion はない。f は initializer 内で一つの monomorphic root、h は外側 formal、x/y は f の二つの lambda formal。lambda は level を増やさない。後続 Name f と最終 Name top だけが通常の公開後 freshening を行う。

top RHS は level1、h の型 H:1。nested f RHS は level2。f の recursive row o、x の B、y の Y、h x の結果 J、f {a=y} の結果 R は全て level2。構造型の略記を

`A(Y)=Record(a:Y)`、`K=Function(Y,Record(first:J,next:R))`

とする。K は fresh 型変数ではない。

### 2.1 全 native steps

1. `typeLetRhs(false,top,...)` (`Typer.scala:48–55`) が RHS を level1 で推論し、Lam h が H:1 を作る。nested `typeLetRhs(true,f,...)` が o:2 を作り、ctx[f]=o として initializer を level2 で推論する。
2. Lam x と Lam y (`:63–66`) は B:2,Y:2 を作る。内側 Record の `fs.map` (`:78–79`) により first の App h x を先に推論する。h lookup は同じ H、x lookup は同じ B。App は J:2 と demand `H≤Function(B,J)` を生成する。
3. H は level1、rhs Function は level2。ordinary lhs-variable branch は失敗、rhs は変数でないので ordinary rhs-variable branch も該当しない。negative extrusion (`:121–123`) を target1、**空 polar memo M_h** で呼ぶ。
4. Function domain は polarity を反転する。B positive の memo miss に C:1 を作り `M_h(B,+)=C` を再帰前に登録。`B.upper=[C]`、C.lower は空の B.lower を写して空。J negative の miss に D:1 を作り `M_h(J,−)=D`、`J.lower=[D]`、D.upper は空。rewrite `H≤Function(C,D)` は level1 なので H.upper に入り、H.lower は空。今回の実 pair group は **C/B positive と D/J negative の2個**。
5. next field の App f {a=y} を推論する。Name f は o をそのまま返す。Record argument は A(Y):level2。fresh result R:2 と demand `o≤Function(A(Y),R)` を作る。rhs.level=2≤o.level=2 なので o.upper に保存。o.lower はまだ空。**同 birth Call のこの入口ではコピーはゼロ**。
6. body Record の型は Record(first:J,next:R)、inner lambda は K、outer lambda は Function(B,K)。再帰完成 (`:52`) が `Function(B,K)≤o` を生成し、o.lower に保存する。既存 o.upper の唯一の Function(A(Y),R) と replay。
7. Function 比較 (`:106–108`) は引数を先に反変比較して `A(Y)≤B`。B.level=2 なので rhs-variable branch (`:118–120`) が B.lower に A(Y) を保存し、既存 B.upper の C:1 へ **`A(Y)≤C`** を replay する。
8. この比較は構造 lhs:level2、rhs C:level1。ordinary rhs-variable branch の条件2≤1が失敗し、positive extrusion (`:124–125`) を target1、**新しい空 polar memo M_r** で行う。Record field Y の positive miss に T:1 を作り `M_r(Y,+)=T` を登録、Y.upper に T を追加し、空の Y.lower を T.lower へ写す。rewrite A(T)≤C は level1 なので C.lower に A(T) を保存する。今回の実 pair group は **T/Y positive の1個**。M_h の copy を再利用したものではない。
9. 引数比較が終わり、step6 の Function result 比較が K≤R を生成する。K.level=2≤R.level=2 なので R.lower に K を入れる。R.upper は空。K の中の R は variable leaf であり、この挿入は構造を無限展開しない。ここまでに追加の comparison/extrusion はない。

step8 は先行 h 呼出しの低い境界を通るが、step5 の同 birth recursive demand の反変引数からの実 descendant でもある。従って INV の全称量化は、この一つの実 native history で偽となる。

### 2.2 公開直前の全 store

全行の物理 lower/upper list を列挙する。構造名 A,K は前記の略記であり追加 row ではない。fresh 初期 bounds は全て空だった。

| row | level | lower list | upper list |
|---|---:|---|---|
| H |1|∅|Function(C,D)|
| o |2|Function(B,K)|Function(A(Y),R)|
| B |2|A(Y)|C|
| Y |2|∅|T|
| J |2|D|∅|
| R |2|K|∅|
| C |1|A(T)|∅|
| D |1|∅|∅|
| T |1|∅|∅|

初回の wrong-level comparison は step3 の H≤Function(B,J)。同 birth seed の **最初の wrong-level descendant** は step8 の A(Y)≤C。両者を取り違えない。全 fresh copy は C,D,T の3個であり、各 polarity/target/memo group は上記で尽くした。

有限性は単なる satisfiability から推定しない。比較列は step2,4,5,6,7,8,9 と level1 rewrite の有限列。recursive result K≤R は upper が空なので再帰比較を起こさない。各 extrusion の selected bounds は空、構造 traversal は一つの Function または一 field Record。したがってこの cut まで finite。通常 cache も実装通り保持するが、ここで未知の無限 worklist を cache が止めるという仮定は要らない。

### 2.3 残りの source inference と整合性

f は boundary1 で o を公開する。`in f` の実 freshenAbove は一つの memo で高い o,B,Y,J,R を level1 の o',B',Y',J',R' に写し、C,D,T は保持する。K と A の構造を同じ map で写す。R.lower=K の cycle は R' を bounds 再帰前に memo 登録するので有限。追加 constrain demand/extrusion はない。top の型は Function(H,o')。最後の `in top` は boundary0 で到達する有限 cyclic graph 全体を同じ memo で level0 へ freshen し、新 extrusion occurrence を作らない。

store には実解もある。I=int とし、Y=T=I、B=C=A(I)、J=D=I、

`R = μr.Function(I,Record(first:I,next:r))`, `o=Function(A(I),R)`, `H=Function(A(I),I)`。

すると K=R、o の lower/upper は一致し、全 direct/copy bound が成立する。fresh copies には同じ構造的写像で値を与えられる。この guarded recursive native 型 valuation は source code を実行した証拠ではない。原 Scala 型推論がこの有限列で primitive mismatch を起こさないことは上の比較列自体からも分かる。

## 3. Value graph と actual source seeds

P=top、F=f、H_v=h、X_v=x、Y_v=y とする。source constructor の不変 birth は P,H_v が1、F,X_v,Y_v が2。二番目の lambda y も2。型行 H/B/Y の数字を書き換えて birth を決めたものではなく、let/lambda の生成規則から得た値である。

F の definition-owned Name incidences は正確に `F→H_v,X_v,F,Y_v`。P は f の公開後 Name を所有して P→F。parameter 頂点に出辺なし。内側 record result の helper projection は Y_v へ、h x result は H_v,X_v へ、recursive App の Name/Record fragmentを走査する現 code の projection は F,Y_v へ進む。fragment membership の一般的 authorityをここから拡張しない。これらの result 頂点から F へ戻る可能性はあっても、F が Name でこれらの result 頂点を参照する辺はない。従って relevant SCC は singleton、G_2 内 F の自己辺が唯一の非空 cycle。

二つの actual Call checking seeds は

`e_h=(F,H_v)`、`e_r=(F,F)`。

現 birth-induced 資格では前者 false、後者 true。seed e_r の入口では pair group は空だった。それにもかかわらずその Function argument descendant が T/Y を実生成するため、「同 birth の Call の子孫は copy-free」は真に反証される。

この結論は T/Y が **actual occurrence として e_r に属する**と証明したことではない。native derivation ancestry、現 contextual source support、選択された actual origin/receiver は三つの異なる主張である。source birth と type target1 の不一致そのものを意味論反例とはしない。

## 4. code に対応する exact provenance と境界

scalar step6–8 を contextual producer が正当に発行した場合に照合すべき retained DAG は、前稿の result-port とは異なる次の **Argument/Swap** 経路である。

```
r_h: H <= Function(B,J)                         seed e_h
u:   B <= C                                    ExtrusionLink(r_h)
r_r: o <= Function(A(Y),R)                      seed e_r
r_c: Function(B,K) <= o                         recursive completion
v:   A(Y) <= B                                 ArgumentPort(Swap,Replay(r_c,r_r))
p:   A(Y) <= C                                 Replay(lower=v,upper=u)
a:   Y <= T                                    ExtrusionLink(p)
```

`candidate_context.rs:3510–3565` は Function Argument を Swap とし、親の source set を保持する。`:4043–4049` の replay は順序つき lower/upper と両 BoundKey を保持し、source set は和集合。`candidate_extrusion.rs:94–139` は actual fresh copy の直後に one-sided ExtrusionLink をその processing RelationId つきで作る。`candidate_intrusion::Parent` は target/polarity/pair/comparison/source set/occurrence を保持する。

したがって fresh T の実 link Y≤T の emission から p、p の upper_input B≤C から初回 C/B group と r_h、source checking e_h を辿ることができる。lower route v は新しい contravariant argument の e_r に戻る。parent value X_v と late parent value Y_v も異なるので、型 copy T を x の Value と同一視してはいけない。

current any-source consumer は p の support に e_r が残れば true を返す。upper-boundary backtrace query は e_h を得て false を返す。前稿の RG2 の証明方法はこの同じ fresh-link/upper-linkの構成へ適用できるが、**Result port から Argument port へ変わった点と反変 actionを保持**する。完全 Yulang source→四port/receipt/Force producer の認証を scalar history から省略しない。

この具体例を primary の residual-demand construction に渡す際、必要な source equation は次である: recursive Argument port の新しい payload A(Y) を、先に h の argument slot へ置かれた B の residual upper boundary に代入しても、h 側の receiving occurrence を変えず、元 e_r の constituent evidence も失わないこと。ここでその source equation を定義して完了とはしない。primary は別 leased artifact で original source rules から導く責務を持つ。本稿はその未凍結稿を読まず、共同著者にも reviewer にもならない。

## 5. 正しい限定補題: row-path の最初の低い境界

INV を source birth だけで修復することはできない。次の実 native 補題は使える。

**BRD1（空 lower の直接入口）。** level k の open row o に `o≤Function(a,r)` を挿入し、a,r の level≤k、o.lower が空なら、この insertion は copy を作らない。
証明: cache hit なら prologue で return し、copy を作らない。cache miss なら最初の lhs-variable branch が demand を upper に保存し、lower replay は空。どちらも extrude の呼出しに至らない。□

**BRD2（cache miss の比較が辿る正の structural payload の境界 path）。** 有限 native store の upper-row path `x0→x1→…→xm` を固定する。各辺は xi.upper にある実 row xi+1 とし、当該 path 上で比較する t≤xi は全て cache miss で branch dispatch に達するものとする。比較 request が発行されるだけではこの前提を満たさない。構造型 t の level=q。path 上最初の j で level(xj)<q があり、それ以前は level(xi)≥q とする。t≤x0 からこの path を辿る比較は j より前では extrusion せず、j で positive extrusion を呼ぶ。t の高い variable leaf a が訪問されるなら、その呼出しの空 memo に対する最初の (a,+) または structural variance が指定する polar key の miss が実 fresh copy を作る。j がなければ、この path の row境界を通る当該 payload の伝播はコピー不要。

証明: cache-miss 前提により各比較が branch dispatch に達する。j より前の各 t≤xi は rhs-variable branch の level 条件を満たす。lower 挿入は実 upper row xi+1 との comparison request t≤xi+1 を発行する。次の request も前提により branch に進むため、path 長への帰納で同じ t が j に届く。j では構造 lhs は Variable でないため lhs-variable branch は使えず、rhs-variable の q≤level(xj) も偽。positive extrusion branch が選ばれる。extrude は structural tree を降り、variable の level が target を越えた初回 key に freshVar を割り当てて memo 登録する。空 memo と実 visited high leaf が nonempty group を保証する。□

cache 前提が必要な実例は、x0.upper=[C,x1]、x1.upper=[C]、level(x0)=level(x1)=q>level(C) である。t≤x0 を処理すると C へ先に到達するので、後の x0→x1→C の最後の t≤C は既に cache にある。そこで新 copy が作られるとは限らない。この査読反例により、初稿の「replay が呼ばれれば新しい branch を実行する」という推論を撤回する。本稿 §2 の empty-start trace の relevant pairs は全て初出なので、その反例構成は変わらない。

BRD2 は path に関する局所定理であり、他の上界の replay、別の incoming demand、一般的 worklist の停止を除外して誤って全 source を狭めるものではない。dual の lower-row path 上の負の構造 demandは左右と polarity を反転して同じ分岐証明が成り立つ。Function field を越える場合は actual port の polarity flip を追加して追跡する。

本例では t=A(Y),q=2,x0=B:2,x1=C:1,j=1。Y の level2 は target1 を越え、M_r は空なので fresh T が必ず一個できる。BRD1 は step5 のコピー不要を、BRD2 は step8 のコピー必須を説明し、両者は矛盾しない。コピー不要を保証したいなら、必要なのは **当該 structural payload が通る実 retained-bound path の target 条件**であり、source seed endpoints の birth equality ではない。

## 6. 元の親への適用と残項

INV は **REFUTED（native structural invariant のみ）**。これは全一般性の source preservation を平易な vacuity で閉じる案を排除する実成果である。後続証明は、still-qualified direct source seed の descendant が low captured boundary へ入る場合を、Argument/Swap を含めて扱う必要がある。

選択された intrusion algorithm の safety/principal coverage は本稿によって REFUTED にならない。本例だけでは T=Y が必要な source acceptance を失わせる client を構成しておらず、先の PR3 の別 source discriminatorをそのまま移植しない。本例の役割は actual generation counterexample と residual-boundary lemma である。original F1/FK1、全 Call/provider/current-world/future/effect、source generalization の量化は維持する。

具体的 handoff BRD-ARG-RESIDUAL: primary source residual-demand owner は section4 の ordered ArgumentPort→Replay(v,u) を元 source Call obligation の substitution で導き、u が h の receiving boundary を保持することを証明する。入力は上の authentic source/empty-start scalar history と exact port/association。反証条件は、その source substitution が別 receiver を実際に生成するか、complete operand/evidence を失うこと。code any-source の事実だけで結論しない。別途 native correspondence owner はその source derivation と actual contextual records を認証する。実装の新権限は付与しない。

旧 BL1–BL4、PR1–PR3、EC1–EC4 は各元の前提内で維持。RP2 の added-symbol 非含意を source equation 不可能性として再利用しない。本稿は新しい source 構成により候補不変条件を具体的に判定した。

## 7. 凍結 handoff と検査

Assignment r1 / author `/root/astra_corrected_machine`。requested inherited Astra/medium、observed model/effort/duration UNKNOWN。190秒・3 stages、枠追加なし。契約と30 frozen inputs の actual SHA-256 は全一致。数学・静的 source/hash 読取りと本稿だけの書込み。tests/build/probes/compiler execution/Git/network/scratch/descendants はゼロ。唯一の新規 path は本稿。独立 reviewer は primary の別任命。親の全証明は OPEN、producer の有限 assignment はこの結果で終了する。

**STOP: all writes stopped; no descendants.** 最終 artifact SHA は final handoff に記録する。

## 凍結 direct inputs


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
| `notes/theory/2026-10-24-retained-value-graph-replay-attribution.md` | `8adfe10dda01a223c2b289cec81692cd6c92cca66f3170501b96fe894ff5c1c6` |
| `notes/theory/2026-10-24-retained-graph-publication-consequence.md` | `5ea7d91ece760262af4f1ddd9da6496c25a9a555e4f7d9a7c9279adf782b3574` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| `notes/theory/2026-10-08-source-signature-incidence-construction.md` | `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a` |
| `notes/theory/2026-10-24-replay-receiving-occurrence-proof.md` | `1acaa0bd6ec055eb66ce0922b164d154e83280344ba414f6afd8841ccbee45ce` |
| `notes/theory/2026-10-24-replay-extrusion-commutation.md` | `645c073ff0aff6ca7f972837bc8c36e652b50665fd751a4feb5fb6cc600a7a6b` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
