# 実際の再帰 entry と後続 h Call の receiving diagram

ACTUAL-REPLAY-MODEL-20261024/r1。Author `/root/astra_corrected_machine`。
AR1–AR2 と記載した native trace は独立査読で受理。actual extrusion receiving field と全体命題は OPEN。
Contract SHA-256 `75351a3ec3c09bded62b2baa2da81c62855e3cc5c8c8d155ddc8d10a00965105`。
Baseline `3f04454825c5679cfc43e77786cd018e629ee201`。

## 1. 定理の入力と二つの時間

対象は NR §1 の元 source

```
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first=h x, next=f {a=y}}
  in f
in top
```

である。NR1/NR2 の accepted monomorphic interpretation、genuine H*、ground A=Record(a:Int)、元 independent kernel/arm/admission inputs をそのまま用いる。GC は actual Call field maps と ReadInvoke、PF は selected native licensed projections の local profile を供給する。NR の h-result B と native formal row B を混同しないため、以下 h-result endpoint は j、native formal row は B と記す。

Native inference の有限比較列は runtime execution の順序ではない。`Record(Y)≤C` は body を実行せずに生成される。一方、以下の h(xκ′) は実際に future invocation があった場合だけ存在する。定理は前者を後者の一 trace に置き換えず、全 compatible actual events に index された suspended family を構成する。

## 2. AR1: event-indexed family の具体的構成

元 f-entry の actual typed Return/rebind event κ を固定する。NR2 により xκ=(aκ,rκ):A、実 closure gκ の capture `(h,r_h;f,r_f;xκ)`、その allocation/current world Wκ が得られる。任意の independently admitted gκ invocation と y-entry の actual Return λ を取る。yλ=(iλ,rλ):Int、world Wλ。Return がなければこの節全体はその元 entry suffix であり、yλ を置かない。

### 2.1 先行 h と recursive f

1. Wλ に合法 restriction した同じ captured h と xκ を読む。inert carrier c_hκ は `Delay(Name xκ)`。GC3/NR §5.1 でその actual h Call の完全 ReadInvoke judgment を得る。callee actual provider は r_h、receiver receipt はその Call の実 receipt ρ_hκ。
2. h の実 Return `(u,r_u,W_u)` があった場合だけ first slot にその tuple を結ぶ。h が Request なら実 q、origin、response endpoint、raw handle k_h と suffix `bind first; Call f {a=y}; build Record; return` を保持。raw resume は現在の W で同じ k_h を再開する。receipt ρ_hκ を再実行しない。h が返らない全 finite developments に次の f activation を追加しない。
3. W_u で元 r_f を Name lookup する。carrier c_r=`Delay(Record(a:Name yλ))` は同じ yλ を捕捉する。NR §5.2 により元 I_A への complete checking、actual receipt ρ_f、entry Force を持つ。Force の実 Return は a′=`Record(a:iλ)` とその実 root r_a′、current W_a′。pure payload でも f の invocation 全体を pure としない。
4. actual ValueBind は fresh key xκ′ に `(a′,r_a′)` を入れる。元 xκ は変更しない。次の actual Lambda allocation が r_gκ′ を作り、capture は `(h,r_h; f,r_f; xκ′=(a′,r_a′))`。r_gκ′ は r_f でも r_gκ でもない。f の Return はこの gκ′ と current W_g。元二 field の Record は u と gκ′ を同じ resulting world で組み立てる。u の latent result を Force しない。

これらは NR2 の ordinary membership からの正当な elimination であり、candidate S.V を完成済み証拠として使わない。NR の NF/NG をここで再証明する必要はない。

### 2.2 次の actual invocation

gκ′ の Return は invocation を生まない。任意の compatible future event e と independently admitted **actual** gκ′ invocation を別に量化する。その entry が typed Return λ′ を持つ場合、fresh yλ′ が作られる。captured x は依然 a′。λ′ の値を a′ の field へ書き込まない。

この時の Name h は r_h、Name x は r_a′ を返す。carrier c_hκ′=`Delay(Name xκ′)` は c_r とは別の carrier と source path だが、その指定された Force Return value は同じ a′ である。GC3 を合法 restriction した h:A→j と xκ′:A に適用し、元 D_h 全体を保った actual h Call certificate を得る。新 receipt ρ_hκ′ は ρ_f とも ρ_hκ とも区別する。後続 response/future はこの Call の現在の世界と actual returned provider に従う。

**AR1。** 上記 constructor は、全 original compatible entry/response/future histories について、元 pending suffix を保持する一つの dependent proof function を与える。先行 h と recursive f が必要な Return を持ち、後の gκ′ が実際に invoked された場合、その h 引数の actual designated value は厳密に `Record(a:iλ)` であり、actual callee は元 r_h である。

証明。NR §5.1–5.3 の actual Bind equations による有限 phase derivation 帰納。Return case でのみ次の constructor を適用し、Request case は同じ suffix 関数を raw continuation に合成する。future g case は NR2 の hereditary G certificate を任意の合法 event に適用する。Return/rebind/capture/Name の四 projection は全て同じ `(a′,r_a′)` を参照する。従って value/root equality は構文上の型 A の一致ではなく、実際の constructor projection の等式である。各 prefix に異なる arbitrary witness を選ばず、同じ actual trace の projections を使用する。□

## 3. AR2: whole middle の matching

middle は scalar B や旧 Wλ ではない。次の dependent object を使う。

```
Mκ′ = (actual f entry Return a′,r_a′,W_a′;
       fresh ValueBind xκ′; actual gκ′ allocation/captures;
       lawful future restriction e; actual gκ′ entry/pending suffix;
       current event at later Name xκ′;
       original source incidences/profile packet/joint witness).
```

recursive-input derivation d は、上の §2.1 の実 constructor によりこの family の first fields を作る。後の use は、実 invocation を引数に受け取る suspended projection。h-use family b はその **同じ** Mκ′ の captured x projection を取り、Name/Return/Delay と GC により h の inletへ渡す。したがって b を旧 h(xκ) の既実行証拠に固定して d と合成する必要はない。

| complete field | d と b の接合 |
| --- | --- |
| argument actual value/root | f entry Return = fresh xκ′ binding = gκ′ capture = later Name xκ′ Return。全て同じ a′,r_a′。 |
| provider | f は r_f、返る closure は r_gκ′、h は r_h。別々の port に残し、等置しない。 |
| world | W_u→W_a′→W_g→e→later g current world の実 transition/restriction chain。全 projection がこの一 chain を参照する。 |
| carrier/receipt | c_r/ρ_f と c_hκ′/ρ_hκ′ は別の実 introductions。共通 payload certificate を各 constructor が消費するのであり、carrier/receipt identity は要求しない。 |
| request/resume | 各段階の実 handle と未実行 suffix。前段未完了なら後段は dependent function のまま。 |
| profile/licensing | PF1/2 と GC の Operand/Ref/Bind/capture injections。元 imported h packet、local fields、各 licensed witness を保存。 |
| result/consumer/future | f の returned g と h の returned u の dependent families を別々に保持。bodyとcomplete invocationを区別。 |
| independent arms/guards | 元 arm law、same joint witness、現在の event のguard。source trace がない arm を新たに source witness にしない。 |

**AR2。** d と event-indexed b の実合成は whole middle 上で定義でき、次世代の actual h receiver r_h を保つ。

証明。各行は AR1 の constructor projection または GC1 の dependent square。Bind の world は後続証拠の引数そのものであり、別世界の matching を仮定しない。PF の whole transport はこの同じ square を使うため profile を再初期化しない。共通部分は actual value/capture/current-event fields、独立した receipts はそれぞれの段階の field として合成 diagram に残る。よって全 tuple の matching が構成される。□

この成果は旧 SC4 の撤回箇所を具体的に修復する。xκ を Record(yλ) へ置換する action は不要であり、AR2 はそのような action を与えない。AR1/AR2 は event family における実 semantic bridge である。

## 4. native records との同時照合と限界

BRD §2 の空 store からの同じ history を用いる。H:1、o,B,Y,J,R:2。初回 h demand H≤Function(B,J) の negative Function extrusion は M_h に C/B positive、D/J negative を作り、B.upper=C、J.lower=D を残す。recursive demand o≤Function(Record(a:Y),R) は同 level で copy を作らない。f completion Function(B,K)≤o がその upper と replay し、argument を反転して d:Record(a:Y)≤B を作る。B.upper=C との replay p が Record(a:Y)≤C を初出比較として作る。

p は structural level2 対 C:1 なので rhs-variable accumulation guard が失敗する。新空 polar memo M_p で positive Record extrusion、Y の初回 miss が T:1、M_p(Y,+)=T、Y.upper=T、T.lower=∅ を作る。rewritten Record(a:T)≤C を C.lower に保存する。M_h と M_p は別。単独 Variable/Variable 比較から T が生まれたのではない。以後 K≤R は upper空なので追加 extrusion なし。

SC1/SC2 の同時 records は厳密に次となる。

```
r_h: actual q_h Application ↦ H≤Function(B,J)
u:   ExtrusionLink(r_h,B,C,+,1)
r_r: actual q_r Application ↦ o≤Function(Record(a:Y),R)
r_c: recursive completion ↦ Function(B,K)≤o
v:   ArgumentPort(Swap,Replay(r_c,r_r)) ↦ Record(a:Y)≤B
p:   Replay(lower=v,upper=u) ↦ Record(a:Y)≤C
z:   ExtrudeFresh(p,Record-field a,Y,+,1,M_p) ↦ T/Y
```

SC2 erasure は actual rule/endpoint/order/memo を保つ。AR1 は q_r の operand/entry/body/future evidenceを実際に供給し、AR2 は同一 source formal の future h-use family に payload を送る証拠を供給する。GC/PF により旧 SC4.2 の result/profile/recursive-member 欠落をここで再度前提にしていない。derived p の元下側 provenance e_r と上側 e_h はともに保存する。

**重要な sort の境界。** この annotated native record の erasure を証明することと、z の authoritative actual extrusion occurrence に AR2 の receiving incidence を写すことは同じではない。SC2 の `Extrusion fresh` case は source側に whole-interface checking obligation を残すと明記する。NR2 は operational event family、AR2 は actual source composition、SC2 は source-indexed *obligation* generation。これらだけでは ExtrudeFresh がその composition を actual occurrence record の receiver欄へ認証する rule をまだ出力していない。

最初の未閉鎖 field はここに限定できる：

```
RealizeExtrudeFresh(
  processing = Replay(v,u), polar-key=(Y,+), target=1,
  pair=(T,Y), complete source diagram=AR2,
  original occurrence=o_z
).receiving_incidence
```

要求する equality は、この field が **actual** o_z の receiving Value に一致すること。AR2 の結論 r_h を field の定義として代入すればこの equality は自明になるが、それは許可された既存規則からの証明ではない。direct q_h の receiving は Name h constructor で認証済み。後着 z は direct Call の seed ではなく static bound replay の extrusion であり、先行 u の receiverをそのまま継承することがまさに証明対象である。full dependent interface の充足や type endpoint の一致はこの actual occurrence equality を決めない。

これは保持情報消失という主張ではない。u の fresh-link route は e_h、v の swapped argument route は e_r に戻れる。全 DAG、pair、memo、processing comparison を上で照合した。問題はそれぞれの authentic routeを持つことから、選択済み occurrence semantics の receiving field を導出する **constructor correspondence**。SC の記録を付けることでこの field を新規に定義しない。

## 5. 親への実適用と不成立な近道

閉じた具体的成果は AR1/AR2：元 recursive source の actual returned-value→fresh binding→capture→future Name→h の full-interface bridge。これは単なる型 A の一致でも、未実現の Check origin でもない。旧 SC-REBIND/SC-REC/SC-FULL-CALL の本 monomorphic event-family instance に必要だった実 semantic evidence が揃った。NR2、GC、PF の元独立 kernel/arm premises は保持する。

同時に、元 finite native p/z の exact provenance と copyを上の source witness に対応する proof recordとして構成できる。しかし **actual z の receiving H、従ってその birth-induced SCC 資格はこの稿では未証明**。source future h の receiver H は証明済みであり、二つを混同しない。static definition origin F は元 q_h/q_r の所有定義、dynamic gκ′ root は runtime allocationであり、それらも等置しない。

次の三つでは残 field を埋められない。(i) source support に e_h がある、(ii)上側 boundary route が hへ戻る、(iii)実 future h が同じ record を受け取る。三つは本稿でいずれも具体化したが、actual extrusion occurrence と source diagram の correspondence constructor が必要。これは全 source theorem を否定する反例でも semantics の新しい選択要求でもない。次の in-scope owner は source/native ExtrusionFresh correspondence の producer。最小 proof TODO は上の一つの receiving_incidence equality を元 occurrence constructionから導出すること、falsifier は同じ actual processing/memo/pair の occurrenceが AR2 と異なる receiving incidenceを要求する case。

primary の別 native model は未読・未依存。GE6 の model が供給されても、それは上の source receiving field、publication strategy、F1/FK1、全原 A/B・主型性・停止性を代替しない。

## 6. 凍結 receipt

Contractと19 frozen direct inputsの actual SHA-256 を照合し全一致。直接参照：NR §§2,4–7 (特に114–147行)、GC §§2–5、PF §§2–4、SC §§3–4 (特にExtrusion fresh/SC2/SC3)、RD §§2–4、BRD §§2–4、reference Typer.scala constrain/extrude (89–156行)。author/dependency provenance は各 frozen input のheaderと契約に保持。NR author `/root/astra_scoped_join`、GC/SC/BRD author本worker（査読後の修正はprimary）、PF/RD author primary。今回の結果は独立査読未了。

Three stages: event-family construction; whole middle and native record alignment; exact boundary/application/freeze。190秒上限、更新なし。requested inherited Astra/medium; observed model/effort/elapsed UNKNOWN。静的 read/hash と唯一の本稿作成のみ。tests/build/probes/compiler/implementation/Git/network/scratch/descendantsゼロ。新規pathは本稿だけ。all writes STOPPED at freeze。artifact SHA は外部handoffへ返す。全 parent はOPEN、本packetはこの具体的成果とexact remaining fieldで終了する。

独立査読入力 SHA-256 `13990262597a14691547b0e78fef0d65664f5e1a8bf595381fbb4ef4b86c29ef`。査読後の変更は primary による status とこの receipt のみ。[outcome](../../tasks/agent-loop/sprints/actual-replay-model-20261024-outcome.md) に受理範囲を固定する。
