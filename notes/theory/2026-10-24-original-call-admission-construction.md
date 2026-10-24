# original Call の同一 carrier 入場操作と、再帰適用の残る一段

Assignment **ORIGINAL-CALL-ACTIVE-WALK-20261024/r1**。著者 `/root/astra_corrected_machine`、子なし。契約 SHA-256 `a714ec476cc13f64fca3ec7ed071ca96cc852a3019b23e37d71157d8b54e8fa6`。基準は primary 指定 `9cc452b357117e51161a74b94c756de364d6e3d7`。要求 Astra/medium、観測 model/effort/duration UNKNOWN。分類: 同一 carrier の構成的 refinement/action、original source application の部分導出、最初の未導出 original clause の特定。J_rec/J_pub の閉包・source-qualified 反例ではない。

## 1. 原命題と source

```
let rec f = lambda x.
  let g = lambda y. (lambda z.y)(f y)
  in {a=succ(g 0), b=g true}
in f
```

U=Int∨Bool、V={a:Int,b:Bool}、同じ r_f、同じ invocation 内の r_g(h)、同じ current world と元の scope を固定する。R は `2026-10-24-original-recursive-formation-construction.md`。R1–R3 の actual registry、R4 の positive simultaneous family S、R5 の ActiveCapture を再利用する。ここでの目的は R4 の q_fy 行の whole-carrier leaf と original complete Call を実際に埋めること。

元の `ValueMem_F` は全 actual decomposition、全 independently admitted checked challenge、zero/admin/pending/Return と全 response/resume/future を量化する。新しい外来 guard を追加しない。D_F、ActualAdm、P_F、CompleteMem/KV を「本 source で成功した場合」に制限しない。Simple-sub の生成・蓄積・伝播・level・extrusion・qualifying intrusion・generalization、native shared C、F1/FK1 は変更しない。

## 2. 入場の結果 refinement を具体的に作る

### 2.1 固定する full policy

I_U は actual f の original entry carrier interface である。その **全** policy record を Π_U と呼ぶ。Π_U には inert reify/view/root/license、source/capture fields、独立 demand domain、zero/admin guards、effect/guarantee/hard bounds、request/response/raw handle、現在 world、receipt precondition、result incidence、future-provider family、全 declared alternatives を入れる。Π_U は A によって選び直さない。

完全な結果 endpoint を持つ既存 whole-carrier descriptor に、次の refinement を構成する。

`I_A := I_U ∧ Ret_A(I_U)`。

`Ret_A` は次の既存 positive result/pending/future clauses の同時 refinement である。

- actual completed designated Force の結果 `(v,r,C,w,e)` に、同じ tuple の hereditary `ValueMem_A(v,r,e)` を追加する。
- pending observation では既存 request、response、raw handle、current world と未完了 suffix をそのまま持ち、その suffix の将来の actual completed result に同じ A 条件を課す。
- zero/admin/nonreturning prefix には未発生の result value を作らない。上の将来結果契約を未完了 obligation として保持する。
- future-use は同じ result/root/provider の元の hereditary restriction を使う。別 provider や別 response を選択しない。
- independent alternative は I_U の元の full witness を残し、結果を持つ場合だけその同じ result に A 条件を追加する。結果がない alternative は元の full fields と pending obligations を残す。

これは result に単なる scalar tag を塗る操作ではない。元の complete interface との同一 tuple 上の conjunction であり、raw carrier、scope、history、Π_U を変更しない。既に固定された別の I_A をこの定義で上書きする規則ではない。現在未構成の g inlet をこの refinement として選ぶ場合の明示構成である。別の既存 inlet と同一視するには original comparison が必要。

### 2.2 action

A≤U の実 same-value inclusion を j とする。量化順序は

`fixed Π_U,I_U; ∀A ∀j:VIncl(A,U); ∀e ∀t ∀w:I_A(t,e)`

である。I_A の証拠を I_U 側へ射影する写像 `k_A(w)=π_1(w)` を定義する。raw carrier/world/event/全証拠座標への作用は恒等。Return の A 証拠を U として明示的に読む必要がある位置では、同じ `(v,r,e)` に j を適用する。元から保持した I_U 証拠を別の U 証拠に置き換える必要はない。

**補題 CA1（full-carrier refinement action）。** k_A は全 original inert/admission/Force/pending/response/future fields を保つ whole-carrier action である。任意の independent compatible restriction σ について `k_A(w|σ)=k_A(w)|σ`。actual t を実行し直さず、receipt を前倒しせず、carrier が Return することを要求しない。

**証明。** conjunction の同じ tuple 上で第1成分を射影する。inert/guard/domain/current-world/receipt fields は第1成分に元のまま含まれる。Return は同じ value/root で j を適用するだけ。Request は同じ q,response,raw handle と current world を保持し、各 admitted development に同じ射影を適用する。zero/admin では未完了 obligation の第1成分を取り、result の存在を使わない。future は同じ hereditary family の各元に射影を適用する。restriction は全 record の同時 restriction なので射影と可換。これで全場合を尽くす。□

CA1 は `A≤U` だけから **任意の independently fixed I_A** の admission を I_U に写す定理ではない。この限定は消せない。例えば元の inlet が result 型とは別に receipt precondition を持てば、scalar inclusion はその証拠を作らない。本稿はそのような guard を追加したのではなく、既存の guard を全保持する構成によって問題を避けた。

### 2.3 この構成が埋める leaf と埋めない leaf

CA1 により R4 の「complete domain/observation inclusion action」を、上記 **構成した inlet family** について具体的な record map に置き換えられる。unknown guard の covariance を仮定しなくてよい。

ただし、これだけで source の NameDelay carrier が I_A に属するとは言えない。必要なのは

`Car(I_U, Delay(Name y), r_arg, e)`

とその全 completed-result/future A 証拠である。後者は actual y:A と selected Name/Return/Delay clauses から構成できる。前者を CA1 の結論から逆算すれば循環する。これを次節で正確に判定する。

## 3. q_fy の source diagonal を実際に導出する

q_fy は R1 の同じ r_f を読む callee と、actual Return 後に束縛された y を読む inert carrier `t_y=Delay(Name y)` を持つ。y は g の entry が pending の間には存在しない。

selected `call-semantic-input-realization` §4.2–4.3 により、actual current immutable environment の y の hereditary A certificate から次を構成する。

1. Name の lookup は同じ y/root と current world を返す。zero/admin prefix も同じ環境・incidence を保つ。
2. Delay は original reify license と capture/reference tuple を使う inert formation である。Force は demand の live world で Name を一層だけ実行する。
3. Force Return は同じ y:A。j によって同じ y:U。request を出さないのはこの Name code の constructor inversion による事実であり、他の admitted carrier の request を除く理由ではない。
4. future demand は同じ hereditary y certificate を restriction する。別 activation を復活させず、元の current authority を観測する。

従って source-owned NameDelay の **選択済み carrier view `Comp(empty,A)`** と、その U-result 版 `Comp(empty,U)` については、同じ原点の完全な inert/execution 証拠を実際に構成できる。証明は Return 型だけではなく、上の全 prefix/future case を持つ。

**補題 CA2（NameDelay の結果包含）。** selected NameDelay の元の policy を固定した family では、上記 source construction と j が同じ t_y の complete U-result evidence を与える。I_U がこの exact original interface である場合には、CA1 の I_A の両 conjunct を得て `k_A` を q_fy に適用できる。

**証明。** 1–4 を任意の compatible e と任意の designated demand で行う。pure Return の original clause は `JointWF ∧ ValueMem ∧ original incidences` なので、j は変更すべき唯一の result membership を写す。inert formation/license と全 restriction は固定。□

I_U に additional carrier-effect/receipt/authority/profile 条件がある場合、`Comp(empty,U)≤I_U` の full checking は CA2 の結論ではない。元の NameDelay 定理も `Theorem R` も、この checking を独立に要求している。Theorem R §5 は明記された whole-argument checking から checked admission を得ており、Name という構文だけから任意の inlet への admission を作らない。

**この時点での actual residual は一つの interface equation/checking である。**

```
ND-IU(q_fy):
  selected full NameDelay view at the actual r_arg/current e
  -> fixed actual I_U, with Π_U's original inert/receipt/demand/future fields.
```

I_U を選択済みの NameDelay U-result policy で構成するなら、この leaf は恒等で閉じる。その選択は effectful/nonreturning carrier を source diagonal に置き換える操作ではない: I_U が独立に受け入れる全 carrier はそのまま残る。しかし既に指定された広い actual I_U を pure source view と同一視してはならない。現在の R artifact は I_U を complete operand として残しており、この exact equation も全 guard 証拠もまだ記録していない。したがって本稿は恒等 case の成立を actual original J_rec の無条件成立と報告しない。

## 4. positive recursive relation への適用で循環させない

R4 の S は actual f、g、wrapper、world、carrier、observation の同時族である。q_fy の recursive use に必要な判断を二つに分ける。

- **参照の帰属:** `S.V(F*,v_f,r_f,e)` は R の f-family の同じ tuple であり、Name/capture が新しい f を作らないことは R1/R5 が与える。
- **constructor 一段の結論:** q_fy の全 actual invocation observation が `P_F*[S]` を満たすこと、すなわち現在証明中の `S⊆Phi(S)` の f/observation case。

前者から後者を通常の完成済み ValueMem の elimination として導いてはならない。任意の candidate set S の要素が、完成済み νPhi の Function realization certificate を持つわけではない。

ND-IU が与えられたとき、q_fy の source input 部分は CA2/CA1 で構成できる。actual f の `CarrierContract(U_f)=I_U` は stored Value-entry の constructor equality なので、同じ checked carrier proof と original receipt/context fields を組にして ActualAdm を構成する。これには f の最終 ValueMem certificate を使わない。

出力側は raw phase による一段の証明を必要とする。zero/admin はその actual phase/authority guards、Force Return は actual y:U の rebind、pending は同じ request/response/current world と残りの f-body suffix、body は R の登録済み plan の S.T obligation、final Return は同じ body-result V の original return clauseへ送る。wrapper はその後に初めて z を rebind し captured y:A を返す。この分解は recursive obligations を S.V/S.W/S.T/S.Car の **正の位置**へ戻し、独立 guard はそこから導かない。

これにより、ND-IU と actual phase/world guard の local evidence があるとき、R4 の recursive-call **入力**は新しい前提 J_rec を使わずに埋まる。残る observation one-step clauses を検証しないまま Theorem E を「f は S.V にあるから」と使う証明は拒否する。完成後に νPhi へ入った場合にだけ Theorem R/E の通常 elimination を使える。

本稿は S.T を「必要な全 observation は既に正しい」と定義し直さない。R4 の同時 family に戻す位置と、そこで実際に要求される fixed guard を保持する。

## 5. original complete Call と actual alternatives

complete Call の source structural C0 は、callee の pure Name prefix、同じ actual returned provider、whole argument admission、receipt、actual Force、dependent rebind、body/consumer/invocation return、全 pending suffix の順に合成する。この source branch の入力部分は §§3–4 で具体化した。Return は actual current world で Bind の suffix を実行し、Request は未完了 suffix だけを同じ raw continuation に追加する。完了済み receipt を再実行せず、wrapper の `f y` を消さない。

一方、unchanged `R_U_all` の全体はその structural branch と同じではない。凍結した original authority は complete operation の independently declared alternative と、その全 typed interface を保持する。ここで次の accounting construction を明示する。

各 actual declared clause α について、その original declaration key と whole dependent telescope `(P_α,T_α,Prim_α)` を使い、IF-Insert で宣言 root へ、IF-Use で q_fy の actual reference へ入れる。Call の結果 provider が α の output なら、future interface もその output-dependent field を使う。source branch の f/provider や wrapper result の latent interfaceへ cast しない。source execution anchor を持たない clause でもこの declaration/reference path は保持する。

この操作は actual α ごとの全 tuple と license/admission witness を恒等に運ぶ。source branch の C0 derivation があっても、opaque α の `Prim_α` の証拠を作らない。W の changed-domain action が必要なら元の domain certificateをそのまま要求する。全体 C0 は、actual source structural derivationと **すべての actual α の original local typing**を同じ complete operation の元の clause 結合で組み立てる。

重要な exact residue は「任意の foreign model が悪い guard を持つかもしれない」ではない。現在の actual registry R は source declaration/site/capture/port plan を登録するが、`R_U_all(q_fy)` の independently specified complete semantic clause list と各 arm の whole original evidence を供給していない。source tree に W/Z が書かれていないことは、全体 operation に W/Z がない証明ではない。逆に、未指定の W/Z をこちらから新設して障害にもしない。

`source-contracts-and-common-allowance` §3.7 の `H_G(R)` は明記された sufficient/conditional grammarであり、W/Z の具体意味は未選択である。これを実 original `R_U_all` の定義として採用して source branch を閉包し、「G があるから全 guard は真」とする方法は使わない。前稿の §3.7 への参照から得られるのは保持すべき full fields の一覧であり、actual clause inhabitance ではない。

従って actual complete C0 の次の未埋め judgment は

```
C0-DECL(q_fy):
  authenticate the unchanged complete operation's actual clause interface;
  for each actually declared nonstructural clause α,
  supply its original full local typing and domain/future action.
```

である。IF constructors はその入力からの placement を構成したが、この judgment 自体を生成しない。新しい source-owned data の定義権限でも、固定された independent clause の証拠を宣言 key の存在で置き換えられない。

## 6. 親への実適用と到達点

今回の改善は、曖昧な「whole-carrier covariance」を次の具体物に分解したことである。

1. actual I_U の full policy を保つ `I_A=I_U∧Ret_A` と、全 prefix/response/future を保つ CA1 の射影 actionを構成。
2. actual y の selected NameDelay に対し CA2 の同一 carrier/result refinement 証拠を構成。q_fy の新しい具体 leaf は ND-IU であり、scalar A≤U に戻さない。
3. S.V の recursive occurrence と νPhi の完成済み realization を区別し、ActualAdm は inlet constructor equality から作る。観測側は S⊆Phi(S) の一段 obligation として保持。
4. actual alternative を消さない IF accounting を構成し、full C0 の未埋め leaf を C0-DECL に特定。

CA1 は既存の任意の I_A の theorem ではなく、明示構成した family の theoremである。CA2 は selected NameDelay の exact view に対する theoremである。この二つを actual I_U の未提示 policy equationの代わりに使わない。これが本 packet の meaningful construction と、その実際の限界である。

R4 には CA1/CA2 と actual input derivationを戻せる。しかし ND-IU、actual zero/phase/world law と C0-DECL の未埋め部分が残るため、J_rec は未導出。primary の WalkActive 結果も本稿では仮定していない。J_pub と native shared-C failure を結合した original coverage の反駁は、これらを埋めた後にのみ成立する。現時点の判定は **OPEN**、PROVED/REFUTED のどちらでもない。

### mutual TODO

| ID / owner | 最小の次の入力・反証条件 |
|---|---|
| ND-IU / actual source inlet owner | I_U の exact full policyを示し、NameDelay U-result viewからの元 checkingを与える。恒等で選ぶならその original declarationを固定する。元の admitted carrier/receipt fieldを落とす写像が反証。 |
| C0-DECL / complete-operation owner | q_fy の actual SpecCall と complete declared-clause evidenceを供給。source registryだけをexhaustive semantic censusと呼ぶこと、W/Zを削除・捏造することが反証。 |
| REC-STEP / original Phi owner | §§3–4のActualAdmを使い、実 phase/world/observationの一段 clausesを証明。S.V を完成済み membership として eliminate する循環が反証。 |
| PUB-ACTIVE / primary | 同じ r_f と full relation の WalkActiveを使い、A の binder/fix を判定。本稿は表示Fだけから自由Aの不在を主張しない。 |

## 7. 依存・検査・停止

契約の23依存すべてと契約 hash を静的照合し一致。直接用いた主な hash は R=`f90b88e3e7759a457991f6186782bbd5c1c0236600ca03694527767e4ca49ba8`、semantic-input=`fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a`、captured-call=`0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f`、source-interface construction=`278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98`、simultaneous immutable=`a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6`。全manifestは上記契約の immutable表。R/前OM稿は `/root/astra_scoped_join`、candidate-coreは primary、旧 selected原稿は各ファイルの帰属。CA1/CA2と今回のapplicationの著者は本 worker。

三段階: carrier action、q_fy/source C0、R4への適用とexact残余。上限190秒・三段階、観測時間 UNKNOWN、予約を返却しない。最初の静的 hash command は `python` 不在で失敗し、`python3` で同じ read-only照合を完了。これはruntime probe/testではない。コード/テスト/build/compiler/Git/network/子/scratchなし。新規書込みは本稿一つのみ。

r1を最終SHA-256で凍結し書込み停止。自己認証なし、独立査読はprimaryの所有。STOPPED、descendantsゼロ。全体目標はprimaryが継続し、本workerが待機中も走っているとは記録しない。

## 8. 停止前の primary clarification による actual witness の選択

primary は、ここで未注釈の witness の lawful complete inlet を構成する権限を明示し、既存の固定 foreign inlet と取り違えないよう指示した。この選択では `I_U:=Comp(empty,U)` を selected NameDelay と同じ full source-owned carrier policyで置き、g の inletを §2 の complete result refinement とする。raw source/actual provider/entry は変わらない。Comp の意味は original whole-carrier interpretationであり、NameDelayのsource imageに制限しない。そこで independently admittedな全 zero/admin/pending/response/future を保持する。「emptyだからpendingなし」という推論をしない。

この **構成した witness** に対して ND-IU は CA2 の exact U-result viewと同じであり恒等になる。native unannotated introduction の full-protection/no-concrete-removalは R §4.1 と選択済み native-signature authorityが与える。追加の foreign guard は要求しない。したがって §§3/6 の ND-IU 残項は、既存の別 I_U へ埋め込む場合だけに限定し、今回の選択した inlet actionの残項とはしない。元の independently fixed inletをこの選択で上書きする主張でもない。

これで q_fy の source input の same-carrier証拠は構成済みとなる。一方、S⊆Phi(S) の全 observation/world one-step導出は本稿で完成していない。特に §4 に明記した「candidate S.V と completed realizationの区別」を満たす実導出は引き続き必要である。元の J_rec/J_pub の完全成立は結論しない。

また C0-DECL は **unchanged complete production operation R_U_all の全体**を使用する箇所の残項である。既に導出した NameDelay/actual source input 自体の不成立を意味せず、source-constructor imageだけに関する局所証明へ unrelated production alternativeを追加前提として押し付けない。ただし契約の full C0 / whole original CompleteMemを主張する箇所では、その実 actual clause evidenceを省略できない。源流のsource成立とproduction全体の保証を区別する。

primary の fixed `F_Int∧F_Bool` 提案は、同じ g の二つの完成した hereditary realizationを構成できれば既存 same-value intersectionで結合できる。しかし現時点の S⊆Phi(S) 一段証明の代用にはならず、同じ raw parameterへ二つの独立 assignmentを置くこともできない。停止境界のためこの別構成は未着手とする。現成果の同一 carrier actionとsource inputをprimaryへ渡し、全体の親はOPENに保つ。
