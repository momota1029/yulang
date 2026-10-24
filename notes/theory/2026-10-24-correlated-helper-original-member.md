# Correlated helper の original member/world 構成試行

Assignment ORIGINAL-MEMBER-BRIDGE-20261024/r1。Author `/root/astra_scoped_join`。分類: original 定義での部分構成と最初の未導出 judgment の特定。完全 witness、source-qualified 反例、親閉包ではない。
Contract `tasks/agent-loop/sprints/original-member-bridge-20261024.md` SHA-256 `fd397d1a1ed47688f5726ae3baa9fa288c52bf08269308838836e5f2cbee0221`。
Baseline `59057b660a5a46f448d4c6feda041cb3df3bb38f`。Requested Astra/medium、observed model/effort/duration UNKNOWN。

## 1. 親と変更しない source

```
let rec f = lambda x.
  let g = lambda y. (lambda z.y)(f y)
  in {a=succ(g 0), b=g true}
in f
```

目標候補は U=Int∨Bool、V={a:Int,b:Bool}、F:U→V、g:∀A<:U.A→A である。これらは raw value endpoints の見取り図であり、complete Function/whole-carrier contract の定義済み略記ではない。元の scope、同じ monomorphic f、同じ joint world、各本来の challenge/response/future、CompleteMem/KV、元の Generalize を満たして初めて original lawful witness になる。

native の G/F qualification、C/B と D/R、publication/use で shared C になる事実は固定入力として受け入れる。本稿はそれを再計算せず、C の新しい source binder、C_i の別配置、fresh f、別 world を導入しない。元の preservation/required coverage、A/B、主型性、停止性、F1/FK1 の量化を変更しない。

## 2. 実際に組み立てた constructor skeleton

元の source-Generalize §3.1 は Parameter、Lambda、Name、Result、Call、Bind、Record、Recursive reference/introduction を列挙する。§3.2 は structural union injection、同じ actual callable の checked-domain/observation inclusion を許す。captured-closure authority §2 は generic な完全 Value-entry `Strict(I,formal:A,R,IF)` を、receipt、designated Force、actual Return/rebind、body、invocation return と pending suffix から構成する。

従って試行の interface はまず

```
F*   = Strict(I_U, x:U, R_body, IF_f)
G_A* = Strict(I_A, y:A, R_discard(A), IF_g)
W_A* = Strict(I_V, z:V, PureReturn(A at captured y), IF_wrapper)
```

と書く。これは新しい意味の選択ではなく、既存 Strict constructor への必要 operands を露出した proof skeleton。I_U/I_A/I_V、R_body の full hard envelope、IF の registration/profile/scope guard は、矢印記号だけから得られない。各 entry は admitted whole carrier の全効果と pending developments を含む。

### wrapper の順序と all-prefix case

g の invocation event k で I_A の Force が actual y を返した世界を W_k とする。ここから `lambda z.y` はその同じ y/root と f を含む元環境を capture する。wrapper の引数 carrier は `f y` 全体であり、wrapper の Value entry はそれを Force する。

その Force 内部で f を Name から読むと同じ registered monomorphic root を使う。引数 carrier は actual y の Name/Return/Delay であり、A≤U の同じ値に対する structural inclusion をその complete carrier の元の scope に適用する必要がある。f の result が actual v:V を返した場合にだけ、wrapper が z=v を rebind し body の同じ y を Return する。v は返り値に含めないが、この Call とその世界・証拠を削除しない。

有限観測の case は次の通りである。

| prefix | 保持する義務 |
|---|---|
| g の入口・argument Force が未完了 | receipt、I_A の current world と全 pending response、g body の suffix |
| wrapper closure ができ、引数 `f y` を Force 中 | 同じ f/y/world、f の complete entry と invocation、wrapper の z-rebind/Return-y suffix |
| f 呼出しの argument Force が pending | f 自身の未完了 body/return に加え、外側 wrapper と g の ordered suffix |
| f の body がさらに再帰呼出しを開始 | 一つの f root、実際の新 event、同じ元の history の延長。別 f 証明を選ばない |
| f が正常 Return | actual V 値の再束縛後に同じ captured y:A を返す |
| request、response、再開、その他の admitted development | 各元の typed response と current configuration で未完了 suffix を継続。保存 snapshot や entry 再実行へ置換しない |

この有限 constructor decomposition は発散から安全性を推論しない。f が実際に Return しない場合でも、入口の zero-step guard、Force の pending observations、wrapper の全 suffix 契約が必要である。

**ここまでの局所帰結。** f の complete hereditary membership、元の carrier inclusion/action、capture/guard/world と future laws が実際に与えられた event では、上の Strict/Bind/Return composition が返す値は同じ y であり、返り値相関 A は失われない。これは required premises を明示した proof fragment であり、それらを本 source について成立させたという結論ではない。単に body を `Return y` へ書換えた証明でもない。

## 3. 同時有限観測 logical relation の試行

一つの actual recursive closure f とその immutable environment graph を固定し、同じ histories 上で次の sorts を同時に保持する案を検査した。

* V: f、各実 invocation 内で作る g、各 wrapper、返された literal/record とその同じ roots。
* W: f を設置した world、引数を actual return で rebind した world、各 closure capture/world。
* T: §2 の全 zero/admin/pending/Return observation と ordered suffix。
* Car: 各 original whole argument と Name/Delay carrier、全 designated demand。

n 個の実観測/step までの展開を調べると、Call の完了時だけでなく entry/Force/pending にも上の case を残せる。f の再帰 invocation は実 step を経た下位観測へ戻し、g の二利用は同じ f tuple を参照する。world と continuation を「穴」にせず同じ同時族へ入れる。原 source graph の recursion 以外に架空 step を足して index を消費しない。

この手法で解決できるのは recursive hereditary occurrence の circularity である。次の独立 predicate は n=0 でも残る。

```
actual registered provider decomposition Act(v_f,U_f,r_f)
original formation / role-entry / profile / scope / incidence guards at f
joint registry / current authority / cross-root incidence at W_f
original complete challenge domain D_F*(e) and ActualAdm(v_f,U_f,d)
full P_F* observation/hard envelope and each independent CompleteMem/KV atom
```

contextual-membership authority §2 はこれらの complete challenge を body safety や membership から形成することを禁じる。native-recursive authority §§2–3 は actual independent guard truth を要求し、raw source constructor portion `M_E^ctor` と完全 `M_E` を区別する。従って guardedness からこれらを真と結論する step はない。

さらに「各 n について別証明がある」だけでは、一つの original scoped strategy を全 challenge/future に使う結論を得ない。固定 domain と original existential witness の依存順序を持った一つの postfixed relation を構成する必要がある。有限 approximation の交差を greatest fixed point と同一視する continuity/compactness も与えられていない。本試行はその同一視を使わない。

### 最初の exact failed judgment

以下の `J_rec` は欠落を指す **本稿の metanotation** であり、新しい規則名ではない。

```
J_rec:
  元の Γ, B, xi=(nu,K,D), actual f closure/capture, one registered r_f
  ⊢ [ValueMem(F*,v_f,r_f,e) AND original installed-world/KV at W_f]
     together with every independent CompleteMem conjunct,
     uniformly over all originally admitted compatible events/challenges.
```

これを source-Generalize §3.1 の「Recursive reference / introduction」行で導入するには、同稿 §2 **L4** の actual joint original member/world constructor と全 original local conjuncts の genuine evidence が必要である。native-recursive authority §1 と §4 が選択する actual instance は `my f x=g; my g y=f` の二つの complete Value-entry roots である。本 source の f は nested generalized g、二回の Call、succ、record の body を持ち、その actual constructor と等しくない。その選択は general recursive initializers と CompleteMem/KV discharge を明示的に除外する。

captured-closure authority の Step theorem もこの欠落を埋めない。そこでは captured f の hereditary certificate は **完成した outer carrier Return から与えられる独立入力**。ここで f はまさに J_rec により同時導入しようとする active root なので、この証明を適用して J_rec の前提を得れば循環する。generic Strict は interface を組み立てる constructor であり、この元の independent guard truth を生む theorem ではない。

従って最初の失敗は J_rec の zero-prefix formation/registry/complete independent leaves を、この actual body に対して供給する L4 instance である。これは「不可能」「source が不正」という結論ではない。固定された authority がこの instance を導出する規則・完全 guard inventory を供給していない、という証拠付きの未導出 judgment である。n を増やす試行では変わらないため、次の owner は original recursive formation/CompleteMem-KV constructor である。

## 4. active capture と二つの g use への適用試行

J_rec を仮に得ても、元の Generalize の入力を省略できない。g publication p_g(h) は f の actual invocation h 内にあり、A の type scope は g の challenge k より前、h の下にある。A≤U から A の値を f に渡せるという source checking と、A を generalize できることは別判断である。

Parameter は g の ordinary Desc を導入できる。Name f は同じ active root を指す。しかし §5.1 の retain/fix walk に渡すには、その **complete captured relation edge** の typed record が必要となる。元の §3.3/§5.1 は `Internal(K_g,f)` なら同じ登録 component の全関係、`Mono/Established` なら完成済み環境の全依存を要求する。active f をどちらかに擬装しない。R35 の provisional `ApplyExtrusionScope` を採用せず、source binder が C にないことを拒否理由にもしない。

その後の exact judgment は

```
J_pub:
  original joint source relation for g at p_g(h), with actual active-f capture
  ⊢ Generalize_source(S,g) and two lawful frames i_Int,i_Bool
     sharing the same f/world/Shared strategy,
     whose g parameter/result instances are Int and Bool respectively.
```

A が F の **表示**に free でないことだけでは J_pub は出ない。fix walk は complete capture の admission、latent/future、dependent evidence fields まで辿る。そこに A が出ないこと、またはその field が正当に description-owned であることの証明が必要である。f/world の印刷型だけを固定した candidate ∀-intro から元の walk を復元しない。

J_pub と J_rec の実証拠が得られれば、二つの use の残りは具体的である。Int≤U と Bool≤U の structural checking、Int/Bool literals、同じ g の各 admitted whole argument、§2 の wrapper suffix により g 0 は Int、g true は Bool の complete checked results を持つ。succ は actual original Int primitive の L1 contract を必要とし、二 field の Record は同じ世界・依存を持つ逐次導出を結合する。各 recursive f は F* のままで、polymorphic recursion へ置換しない。これで V の body-result 部分に戻るが、J_rec/J_pub を先取りしない。

現在の成果は original lawful-use coverage の前提を二つの正確な judgment に止めたものであり、native shared-C failure へ適用できる完全 original counterexample はまだない。scalar reference の成功もこの空白を埋めない。

## 5. 新しい候補核定理との橋の検査

V/G/I の frozen 成果は、finite syntax/code、値 graph、Call の Force と全 adapters、pending continuation、current-world transitions、TABLE inclusion を構成する。これは本 source の typed execution skeleton を作るための有用な別レーンである。しかし次の predicate-by-predicate bridge はその結論にない。

| original predicate | candidate result が与えるもの | 未構成 bridge |
|---|---|---|
| Act/原 provider/capture incidence | 同じ graph reference と typed closure code | original complete decomposition と registration/profile/role guard |
| Original ValueMem/World/KV | 値型付き graph と有限 prefix preservation | same-root hereditary world、全 CompleteMem/KV inventory/action |
| D_F/ActualAdm/whole carrier | 構文的に型付いた input と Call/Force plan | 全 independent original punctured challenges と carrier license/admission の対応 |
| P_F/full hard envelope | value safety と candidate effect TABLE inclusion | original provider/future/authority/hard-bound observation の全対応 |
| Generalize eligible capture | free-variable 条件付き候補 ∀/evidence introduction | active-root complete field record と original retain/fix allocation |

primary から supplied candidate-core plan は、同じ f に対する A→U の direct evidence、wrapper、Int/Bool の二 instance を具体化する。これは別 artifact の未凍結本文を依存に追加したものではなく、上表の欠落を埋めない complementary construction の連絡として扱う。本稿はその存在を original CompleteMem の証明に数えない。

## 6. 次の具体的所有者 TODO と falsifier

* **OM-REC** — original recursive/member authority owner: J_rec の actual f body に対して、固定した全 independent guard/leaf の constructor inventory と同一原 tuple での証拠を供給する。出力は元の定義内の derivation または、必要なら Luna に戻す bounded definition proposal。f の成立を registry guard の前提にする循環、ある admitted challenge/future を落とすことが falsifier。
* **OM-PUB** — original active-root capture/Generalize owner: J_pub の actual typed capture edge と full dependent-field walk を構成する。f を新 root/別 world にする、native shared C を黙って C_i にする、未形成の f を Established にする、A の free occurrence を表示型だけで検査することが falsifier。
* **OM-BRIDGE** — primary の candidate/core lane: 上表の predicates ごとに実対応を与える。candidate safety から original membership 全体へ一度で飛ぶ implication は不可。元の domain に存在し候補の typed-input domain に対応しない一 challenge が domain bridge の falsifier。

これらは新 semantics/implementation の承認ではない。新定義、拡大 source domain、追加 lease は Luna に戻す。既知 native diagnosis や C-placement をもう一度証明する task にはしない。完全 witness がないので original required coverage の refutation/closure は **未成立**、親は OPEN。

## 7. 依存、帰属、凍結

契約の12入力の全 SHA-256 を実 bytes で照合し一致した。以下はその immutable dependency manifest。

| input basename | SHA-256 |
|---|---|
| native-recursive-interface-definition | `a9f833556a7e7c361c5b602c982de96b78663a77099999206bdb7bda6da67903` |
| contextual-function-membership-definition | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| captured-closure-constructor-definition | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| source-generalize-definition-and-proof | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| intrusion-source-preservation-proof | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| nested-live-root-generalization-derivation | `f72404c661736ee9e0b6226dfc471724795836510c7aa3a0582d209be47f8dd9` |
| scoped-apply-extrusion-r35 | `971fd22432c1f61373b2f2334d469ff8fa2dbca2f0ea04b2701ddc2189ba0f2d` |
| intrusion-value-type-association | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` |
| yulang-inference-top-level-principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| corrected-core-value-continuation | `4d8ffd63cbb65cd6917145fa31a4cb3f04656a19f7b71fd0e3fdd6cecaabfbeb` |
| source-core-action-coverage | `36672ef591f42a281a04f14fb7ddc4c5283c119de20fee15168e37cbbf13201a` |
| source-core-finite-interface | `d37a30f1f59ad327ebcba129db5b069f4eed1f839d1733230863fdb711a16488` |

governing authority が選択する original positive-operator/Step の premise 読解のため、そこから直接参照された `2026-10-08-simultaneous-immutable-root-introduction.md` と `2026-10-08-captured-call-closure-introduction.md` も read-only で確認した。新しい theorem adoption や依存拡大は行わず、上の authority 自体が明記する scope/guard 条件の確認に限定した。既存稿の author/独立査読は各 frozen input の帰属に従う。本稿は本 worker 単著、自己認証なし。

三段階: original constructor と有限観測族の試行、active capture/二use、親への適用と exact missing judgment。上限190秒/三段階、予約全額 charge、observed active duration UNKNOWN。静的 source/definition 読解、hash、fence/whitespace inspection のみ。tests/build/compiler/network/Git、descendants はゼロ。

新規・scratch path は本ファイル一つ、final message が唯一の handoff。r1 を凍結、全書込み終了、STOPPED。次は独立査読と OM-REC/OM-PUB の authority-owner intake。original theorem は OPEN。
