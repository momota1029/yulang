# 同生成レベルの再帰と低い捕捉先への replay

BIRTH-LEVEL-REPLAY-20261024/r1。著者 `/root/astra_corrected_machine`。
Baseline `7af2bbfe9588128e90f6706f99243e91b63a7ae3`。
source/native 証拠と限定定理。凍結 r1 は独立査読で記載範囲に BLOCKING/MAJOR 指摘なし。査読後の変更はこの状態行のみ。[査読範囲と hash](../../tasks/agent-loop/sprints/birth-level-replay-20261024-outcome.md)を参照。全保存・主型性の証明または反証ではない。

## 1. 元の問題と新しい具体例

契約 SHA256 `775ba304c72d0263639aefa520fbdce743848c3e02e166687500aec1e59450c2`。元の全 lawful source、全必要 joint client、完全 Call、元 scope と証拠を保つ量化を維持する。birth は不変であり型 row の現在 level と同一視しない。

```
let top = lambda h.
  let rec f = lambda x. (lambda z.{a=x})(h(f x))
  in {a=succ((f 0).a), b=(f true).a}
in top
```

これは原 `syntax.scala:7–14` の Let/Lam/App/Rcd/Sel/Var/Lit のみで記述できる。true と succ は元 Typer の builtin。f が返す field は入力 x と同じ型を保持する一方、h に渡す再帰結果の型は外側の level1 anchor によって近似される。この実例では同 birth の再帰 demand そのものには extrusion がなくても、後の replay で fresh copy ができる。

以下 S は原 Scala scalar calculus、R は現 Rust contextual implementation、A は user-selected birth-level occurrence semantics を表す。S の完全 trace、R の実処理定理、A への対応を別々に示す。S の型推論をそのまま Yulang の実行・完全 Call 証明としない。

## 2. S: 元 constructor から生成される有限履歴

### 2.1 f 公開前

H は h の formal row(level1)、o は recursive f row(level2)。B=x,Z=z,R=`f x` result,J=`h(f x)` result,W=wrapper result は全て level2。初期 bounds は空。

1. outer nonrecursive top RHS は level1。f の `typeLetRhs(true,...)` は level2 の o を作り、その initializer 中の f を同じ monomorphic o に束縛する (`Typer.scala:48–55`)。
2. inner `f x` は `o≤Function(B,R)` を生成。rhs.level=2≤o.level=2 なので U(o) に挿入する。extrusion はない。
3. `h(f x)` は `H≤Function(R,J)` を生成。H:1 と構造 rhs:2 なので negative extrusion。argument の polarity が反転し、C:1 を R の positive copy、D:1 を J の negative copy として作る。得られる全 scalar 制約は

   `R≤C, D≤J, H≤Function(C,D)`。

   この時 L(R),U(J) は空。ここで実 fresh pairs は `(C,R,+,1),(D,J,−,1)`。
4. wrapper の型は `Function(Z,Record(a:B))`。App はこれを `Function(J,W)` と比較し、J≤Z と Record(a:B)≤W を生成。J≤Z は等 level の lhs-variable branch。既存 lower D を replay した D1≤Z2 は **rhs-variable branch** (`:118–120`) に入り L(Z) に D を追加する。これは negative extrusion ではない。row/row 比較では少なくとも片側の level 条件が成り立つ。余分な Z の copy を作らない。
5. f の型 `Function(B,W)` を o に挿入して完成する。U(o) の Function(B,R) と replay し、B≤B は identity、W≤R を得る。
6. W の lower Record(a:B) が R へ流れ、R の upper C により `Record(a:B)≤C` に至る。構造 lower の level2 が C:1 を越えるため positive extrusion。新 T:1 を作り `B≤T` を保持し、lower Record(a:T) を C に挿入する。L(B) はこの cut では空。実 fresh pair は `(T,B,+,1)`。

同じ constrain 呼出し内の cache は variable を含む pair を処理前に登録する。上の graph は有限であり、新しい structural demand は Record(B)≤C とその rewritten Record(T)≤C に限られる。Function 比較と Record field 比較は有限 tree を降り、同じ variable pair の再訪は cache hit。ここまでの全 store（順序と重複を除く）は次の通り。

| row | level | lower | upper |
|---|---:|---|---|
| H |1|∅|Function(C,D)|
| o |2|Function(B,W)|Function(B,R)|
| B |2|∅|T|
| R |2|Record(a:B)|C|
| J |2|D|Z|
| Z |2|D|∅|
| W |2|Record(a:B)|R|
| C |1|Record(a:T)|∅|
| D |1|∅|∅|
| T |1|∅|∅|

この一覧は両極性 copy、wrapper の discarded result と全 inherited bounds を保持する。H と D の情報は f の公開 root から届かなくても outer store に残る。

### 2.2 公開後と最後の top

f は boundary1 で o を公開する。freshenAbove は o,B,W,R を各 use ごとに level1 へ複写し、C,T を共有する。したがって use i ごとに `B_i≤T`, `Record(B_i)≤W_i≤R_i≤C` があり、C の lower Record(T) は固定される。

`f 0` は int≤B0,W0≤V0、selection は V0≤Record(a:A0)、succ は A0≤int,int≤U0 を生成する。Record(B0) の replay により B0≤A0。第二 use は bool≤B1,W1≤V1,V1≤Record(a:A1) から B1≤A1。これらは全 level1 であり、新しい extrusion はない。特に B0≤T と B1≤T は T≤B0,T≤B1 を生成しない。top の型は `Function(H,Record(a:U0,b:A1))`。最後の top Name は boundary0 の一つの coherent freshen であって新 extrusion occurrence ではない。

この scalar store の satisfiability は具体的に示せる。U=int∨bool と置き、T=B=U、C=R=W=Record(a:U)、o=Function(U,Record(a:U))、D=J=Z=int、H=Function(Record(a:U),int)。use0 は B0=A0=int,V0=W0=R0=Record(a:int),U0=int、use1 は B1=A1=bool,V1=W1=R1=Record(a:bool)。共有 C と全 auxiliary bound を含む全制約が成立する。Scala の比較列も同 primitive の比較以外の primitive/primitive mismatch を作らない。これは元 scalar algorithm の acceptance 証拠であり、完全 Yulang source membership の代用品ではない。

## 3. R: source association の実生成から pair retention まで

### 3.1 entry seed は具体的に特定できる

`candidate_value_graph.rs:94–216` の owner walk は nested f initializer の owner を F に切り替え、lambda の中では owner を変えない。`:289–306` は各 Apply の checking slot0 に `Association {origin:owners[index], receiver:expression_value(callee)}` を登録する。expression_value は Name を resolved Value に戻す (`:77–84`)。

この source incidence に対する三つの named source handle は次の通り。

| handle | actual Apply | origin/receiver |
|---|---|---|
| e_r | f x | F/F |
| e_h | h(f x) | F/H_parameter |
| e_w | (lambda z.{a=x})(...) | F/L_wrapper_expression |

F birth2、H_parameter birth1。A では e_r は同一頂点ゆえ資格あり、e_h は birth 不一致ゆえ資格なし。e_w の receiver は f ではなく lambda expression の Value であり、lambda 全体を f と同一視して資格を捏造しない。

`candidate_source.rs:1759–1767` は active_initializer の recursive Name を Action::Link にし、`:2436–2440` は slot30 の value link として発行する。これは f の use を早期 freshen しない実分岐。Apply は `:1833–1889` で全 callee/argument/result/effect endpoints、source checking slot0 を ApplySourceInput に保存する。`candidate_context_seed :3374–3425` は checking map にあれば singleton source set、なければ空集合を relation に付ける。従って resolved Apply source とその seed association の対応は確認できる。

ただし、ここで authentic checking slot が存在することと、全 source Call recipe がその endpoint 上の scalar Function projection を実際に完了させることは異なる。R は四 port Function、receipt/Force、scoped demand、独立 effect relations を持つ。scalar trace の全 relation へ無条件に置き換えない。

### 3.2 source-set の不変条件は code から証明できる

**BR1 (source support union).** 正常に生成された contextual relation の source set は、その生成 DAG の source seed 集合の和集合である。ただし seed でない外部初期 relation はその明示的初期 source set を葉と数える。

証明: `relation :3025–3034` は processing relation の集合をそのまま継承する。Function port `:3510–3565`、bound emission `:3895–3937`、rewrite `:3480–3502` は親集合をそのまま child に渡す。replay `:4043–4048` は lower と upper の `union_sources` を渡し、`:3095–3115` は sort/dedup を行う集合和である。有限生成 DAG の各追加に帰納する。relation key は pair/context/**sources**/scoped を含む (`:3084`) ため、別 source set を同じ relation として intern して消さない。循環した型 bounds があっても、一つの実生成 record の有限親列に対する帰納であり、型の無限展開への帰納ではない。□

ここで証明されたのは **依存 support**。support に含まれる seed の全 pair を新しい extrusion の authentic ownership とする定理ではない。

scalar projection に沿う contextual path が実生成される場合、その source-set 計算を省略せず書く。f 完成の seed を S_f、wrapper lower を S_w とし、純粋な unseeded formation は空、wrapper checking の投影なら S_w={e_w} である。

```
Function(B,W) <= o            : S_f
 o <= Function(B,R)           : {e_r}
 W <= R                      : S_f ∪ {e_r}
 Record(B) <= W              : S_w
 Record(B) <= R              : S_w ∪ S_f ∪ {e_r}
 R <= C (extrusion link)      : {e_h}
 Record(B) <= C              : S_w ∪ S_f ∪ {e_r,e_h}
```

各等式は上の actual union/preserve code の直接適用である。S_f や S_w の余分な正当な seed があっても e_r,e_h は消えない。完全 source projection の authentic seed が空または e_w だけと確認されれば最後は正確に {e_r,e_h,e_w}（e_w を使わなければ {e_r,e_h}）。この有限表を、未追跡の effect/transport branch まで含む「実行済み全集合」とは記録しない。

### 3.3 実 pair、activation、memo reuse

`lib.rs:14715–14759` は structured lower と upper row の比較に positive `candidate_extrude(lower, target=row.level)` を呼ぶ。`candidate_extrusion.rs:94–139` は高 level row に fresh target-level copy を割り当て、memo に登録し、直接 link と selected bounds を保持する。従って Record(B2)≤C1 の実比較がこの経路を通れば、T1/B2 の positive pair を生成する。この時 `retain_extrusion_parent :305–361` は processing relation の `extrusion_sources()` を **全てそのまま** Parent.sources に保存し、any attached event が qualifies なら pending に入れる。

BR1 の上記 path を通った pair なら e_r を含む。この実装 predicate を A の正しい level-induced qualification に差し替えた場合でも、e_r=F/F は真なので T=B を発行する。F/H だけがコピーを所有する、と code の union から結論することはできない。逆に this any rule が A に忠実だと結論することもできない。

現凍結 `candidate_value_graph::Graph` に birth field はなく、`:340` の qualifies は全 graph component equality のみである。従って現 R が新 birth-level rule 全体の実装になっているという主張はそもそも成立しない。本例 F/F は旧/新の双方で真なので、この相違は問題の support-versus-ownership を解消しない。

memo の異なる二段階も残す。local extrusion memo は `(endpoint,polarity,target)` の同じ copy を再利用する。`finish_candidate_extrusion :365–385` は実 comparison/output に pair group を index する。後の retained-rewrite 再利用は `lib.rs:14474–14493` から `recapture_candidate_extrusion :388–422` に入り、**実再利用 output に対応する group だけ**を探し、新しい source set ごとに新 occurrence を記録する。original Parent は書換えず、first qualifying reuse で group の全 pair を一回 pending に入れる。同じ group/source は reuse_keys で重複排除する。既に current pair なら earlier `pair_is_current` return があるので、全 memo hit が recapture を通るとも主張しない。

従って「最初は e_h だけだったから以後安全」「新コピーがなかったから new association は無関係」という shortcut は code に合わない。authenticity 証明は original group と別 reuse occurrence の両方を扱う必要がある。

## 4. A への正確な適用と親に残る一点

A の authority は actual extrusion occurrence の origin/receiver とその実 pair を保持する規則であり、全 replay ancestor の seed を実 origin と認定する規則ではない。10月14日 implementation checkpoint は集合合成を「whole association handles の保持」と報告する一方、source-global correspondence と保存を明示的に除外している。今回 BR1 は合成の事実を証明したが、その除外を消してはいない。

**BR-ATTR (具体的な最初の未証明 clause).** この source の完成 replay `Record(B)≤C` が作る `(T,B,+,1)` について、source-owned complete constructor/continuation のどの actual extrusion occurrence が所有者かを導出し、その origin/receiver が `(F,F)` を含むのか、`(F,H)` だけなのか、あるいは別の正当に構成された occurrence なのかを示す。同じ問いは retained transformed output の新 contextual reuse にも必要。owner は source Call→bound replay→extrusion transport。型 target C の level だけから receiver を H と復元することも、relation support に e_r があるだけで F/F とすることも証明にならない。

これは漠然とした「同 birth でも scope が違う」ではない。実 source、全 scalar bound、実 new pair、実 source-set union、実 any consumer を固定した一つの attribution seam である。concrete source-to-contextual producer correspondence の残りも、この `Record(B)≤C` path と全 effect/receipt evidence の正当な発行に絞って指定できる。成功した compiler 実行・native probe は行っていない。

公開への consequence は次の通り。もしこの pair が A で資格を持つと証明されたなら、minimum-level quotient は B=T を level1 anchor にし、boundary1 の f 使用で共有する。第一 use の int≤B0≤A0≤int と第二 use の bool≤B1 は同じ anchor に合流し bool≤int を要求する。元 S は §2.2 の valuation と有限比較列でこれを要求しない。一方 A で非資格なら B2 の use ごとの freshening と共有近似 T1 は共存し、元 scalar witness を保てる。primary の別 leased publication note がこの use action を精密化する。本稿はその未凍結稿に依存しない。

どちらの場合も、S の acceptance だけで全 Yulang の required source coverage 反例とはしない。complete source member/Call/effect witness または独立な required acceptance がさらに必要。従って **現時点の親は OPEN、REFUTED ではない**。局所 diagonal lift は元 demand の同じ valuation に対しては再利用できるが、qualified pair の authentic attribution と publication を代わりに決定しない。

## 5. handoff / 次の証拠 / 停止

実成果: 原 grammar の全 scalar allocation/bound trace、D1≤Z2 に copy が不要という branch-level correction、実 source association seed、source support union の生成帰納、pair retention と memo recapture consumer、争点 `(T,B,+,1)` と publication consequence を特定した。前稿の抽象 BL5 を繰り返す代わりに実 source と実 code の seam を得た。全原 source 保存の閉包には至っていない。

Mutual TODO BR-ATTR: source/replay owner が上の exact occurrence attribution と complete producer path を導出する。入力は同じ resolved source、同じ three checking seeds、同じ replay pair。出力は実 original/reuse occurrence と全 polar pairs の source correspondence。falsifier は support にだけ含まれる F/F が actual origin でないのに any consumer が T=B を発行するケース。これは実装誤対応なら実装 owner の修正義務であり、ユーザー規則の反証と区別する。BR-SOURCE: original complete source formation owner が要求される witness を供給する。新規の foreign guard を作って阻害しない。

依存15件と契約の hash を静的に検査し全一致。読み取り・数学・唯一の leased note 書き込みだけ。原仕様やコードは変更せず、tests/build/probes/Git/network/scratch/descendants はゼロ。requested Astra/medium、observed model/effort/duration UNKNOWN。190秒、3 stages の固定枠、延長なし。著者 `/root/astra_corrected_machine`、独立 reviewer は primary が別途任命。唯一の新規 path は本稿。最終 hash は final handoff。**STOP: writes stopped; no descendants.**

## 凍結依存


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
