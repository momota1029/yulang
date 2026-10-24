# 捕捉した値を Record に返す完全 Value-entry 閉包

GENERATED-CALL-OPERATOR-20261024/r1。Author primary。Status: WR1–WR3 は記載した独立 kernel/full background 前提の下で独立査読により受理。全言語親は OPEN。
Baseline `5228829724182a87ae3aaf0bfcff68607557dbb1`。
査読対象 `00a37bef423b04e63ef3261a00b96a2489b215d1247362929d8d48b3cc730f27`。査読後の変更はこの status/receipt のみ。[outcome](../../tasks/agent-loop/sprints/generated-call-operator-20261024-outcome.md)に範囲を固定する。

## 1. 元 source と今回導く judgment

対象は、既存 result-replay source 内の実 lambda occurrence ℓ_w である。

```
let top = lambda h.
  let rec f = lambda x. (lambda z.{a=x}) (h (f x))
  in {a=succ((f 0).a), b=(f true).a}
in top
```

本稿は、実 f activation が実際に受け取った x の hereditary certificate から、同じ x を捕捉して新しく作る `lambda z.{a=x}` の complete Function membership と immutable root world を構成する。f の membership、`h(f x)` の typing、全プログラムの受理を入力に置いて完了を宣言することはしない。それらを得た後、この constructor を同じ actual x/world へ適用できる形まで導く。

固定済みの [complete captured closure definition](../design/2026-10-08-captured-closure-constructor-definition.md) §2 は、generic `Strict(I,formal:A,R,IF)` を選択している。これを、body が別の Call である既存 Step ではなく、元の Record/Name/Result constructor に適用する。`Strict` の意味、全 challenge domain、元の immediate guards、Option 2 alternatives は変えない。Record は [Source-Generalize の独立 source 規則](2026-10-08-source-generalize-definition-and-proof.md) §3.1 と §3.2 の普通の shared-tuple/field interpretation を用いる。

## 2. 実 input と descriptor の構成

e₀ の immutable environment E₀ に、既に解釈された実 binding

`x ↦ (v_x,r_x),  b_x : ValueMem_A(v_x,r_x,e₀)`

がある。これは今の actual x の certificate であり、将来の y や別の x の値で置換しない。A の表示が後に latent/computation の形に解けても、Name x の元の `Value(A)` port は変えず、Force を加えない。

ℓ_w の原 source entry は Value-entry。I_z はその原 port の independently typed whole-carrier interface、Z はその designated Force の result endpoint とする。I_z の全 bounds、request/response、pending、provider/future、receipt/path/context guards を保持する。unannotated z が未使用であることから I_z を Retained entry に変えない。原 source が選ぶ I_z の量化範囲のままであり、型付けされた純粋な発散 carrier も排除しない。

次の二つの descriptor を、実行や比較の成功を使わず先に形成する。

```
R_a(A) = 元の Record(a:Value(A)) descriptor
B_w    = PureReturn(R_a(A)) at ℓ_w の body/result ports
F_w    = Strict(I_z, z:Z, B_w, IF_w)
```

R_a(A) はこの特定 x だけを返す relation ではない。同じ field/root/provider の ordinary Record clause により、任意の合法な A の actual field を持つ record を解釈する。B_w も、その descriptor を満たす実 record の元 Return clause である。F_w はこの input/result を実現する全 Value-entry callable に対する既存 Strict descriptor。wrapper の成功した実行集合を新しい型の意味にしない。

IF_w は、実 ℓ_w の登録から [Theorem IF](2026-10-08-call-source-interface-construction.md) の Name/capture、producer/entry、Result/latent-return constructor を適用して作る。Record の field slot は元の field occurrence への依存 injection であり、capture x の field/provider/future を同じ tuple のまま入れる。formal z と result field a は別の port で、body の free capture は x のみ。z の binding は entry Return 後にだけ存在する。

全定理の環境前提は、選択済み Strict/Step と同じ independent context/history kernel、元の primitive/source constructor の immediate guard/transition laws、実際に宣言された独立 alternative の arm-local complete contracts である。それらに wrapper の membership や全 wrapper Call の typing は含めない。未知の State mutation や外国の sealed descriptor の解釈はこの immutable source constructor theorem の前提から生成しない。

## 3. 実 capture と body の導出

### WR1（creation-time capture）

実 Lambda constructor が e₀ で形成する

`v_w = Closure(Pure,ValueEntry(I_z), code({a=x}), {x↦r_x})`

は、元 allocator の新しい r_w、元 ClosureOrigin と capture edge を持つ。x の value/root/certificate を変えず、body を実行しない。

証明。Name resolution の free-binding 計算で body の唯一の free declaration は x。z は formal であり body に出現しない。元 Lambda constructor はこの参照を保持した inert closure を返す。IF の capture injection は既存 b_x の同じ全依存 tuple を source slot に入れ、新しい primitive license や body execution を作らない。後の compatible e₀→e では b_x の元 hereditary restriction を使う。captured value と、過去の maker activation の live grant を区別する。□

### WR2（actual entry Return 後の Record body）

wrapper の actual Value-entry が I_z に適合する carrier から

`Return(v_z,r_z,C₁,w₁)`

を得たとき、元 rebind に沿って fresh z@κ を追加した actual current world で、body `{a=x}` の source judgment と B_w の全 finite observation typing を構成できる。正常 Return は元の x の同じ actual field value/root を持つ。

証明。Return clause と Lemma W/[VB1](2026-10-24-fresh-valuebind-complete-call.md) により、実 `(v_z,r_z,C₁,w₁)` を fresh binding へ入れる。旧 captured x は e₁ へ restrict した同じ v_x/r_x/b_x。Name の独立 source read はその projection を返し、Value port なので latent interface を Force しない。

Record source rule に、この actual shared-world field certificate を入れる。実 record constructor の field map は `a ↦ (v_x,r_x)`、その latent/future interface は同じ field のもの。record identity、元 field path、元 Result/provider correspondence をその actual constructor から取る。普通の Record interpretation の introduction により、この record は R_a(A) を満たす。別の field/world/witness を組み合わせていない。

Result rule はその同じ record/provider/root を現在 world で返す。initial/administrative prefix は元 Name/Record/Return constructor の source-prefix laws、final Return は元 hereditary value/world certificates で B_w の各 clause を満たす。body は field を消費しないので、その潜在的な request を body の実 request にしない。future field demands は元 field certificate をその future event へ restrict して与える。□

ここでは actual typed entry Return は条件付き branch の入力である。後続 WR3 は Return が起こらない全 prefix も別に扱い、Return の存在を全 challenge に要求しない。

## 4. 全 invocation の constructor proof

### WR3（same actual wrapper の complete realization）

§2 の独立入力から、新しい actual v_w の `ValueMem_F_w` と r_w を含む immutable world を同時に構成できる。membership は original Strict の全 challenge、全 retained actual decomposition、pending/complete/zero-step/development/future に対するものである。

**Admission。** 独立 challenge d の carrier は I_z で checked-admitted であり、元の receipt/path/context preconditions を持つ。actual v_w を constructor inversion すると、stored entry はまさに ValueEntry(I_z)。従って同じ carrier/admission certificate をこの constructor equality で読み、同じ current event の guards と組にして ActualAdm を得る。まだ receipt や parameter binding は作らない。

**Observation。** 任意の actual finite invocation development を、元の ordered entry/Bind equation で場合分けする。

| actual phase | F_w の同じ complete clause への証拠 |
| --- | --- |
| zero-step/receipt 前 | WR1 の actual registered closure/capture、現在の independent world/path/authority guards、未実行の I_z/B_w/return/future interfaces。carrier Return を仮定しない。 |
| actual receipt/Force entry | 元 transition law と同じ challenge/carrier。receipt は一度だけ生成し、その証拠を保持する。 |
| Force の administrative prefix/request | I_z の全 designated-execution evidence。raw handle/typed response/current world を保持し、未完了 `rebind z; body; invocation-return` だけを continuation に付ける。 |
| Force の Return | actual Return 後に W で新しい z@κ を作り、WR2 の body proof を適用する。z の値を x の代わりに使わない。 |
| body prefix/Return | WR2 の B_w evidence と同じ current world/record。 |
| invocation return/future | 元 return transition に沿う同じ actual result/provider。wrapper の当該 occurrence だけを終了し、latent field を Force しない。future はその現在 event の元 certificate へ送る。 |
| 宣言済みの独立 alternative | 当該 arm の元 complete law と変更先 admission/provider/future evidence。IF のその arm の injection を使う。上の source phase へ擬装しない。 |

finite development の長さへの帰納により、request/resume が何度あっても同じ suffix と current-world clause を保存する。Force が発散する場合は各 finite prefix が Force の行に入り、body の Return は不要。B_w が pure であることから invocation の effect が empty とは結論しない。

**新しい root と world の同時導入。** 背景の world/carrier が新しい wrapper hole を参照する場合、完成済みの own-world を仮定しない。選択済み captured-closure introduction §5 の singleton declared-hole construction に、H を「この actual `(F_w,v_w,r_w)` の元 scope と compatible-event restrictions」だけとして渡す。H に world/carrier/authority/captured x を入れない。background の non-hole case は同じ positive operator の unfold と monotonicity で移す。唯一の H case は上の admission/全 phase proof で置換する。captured x は元 b_x、返る record は WR2 の shared field clause、parameter は actual I_z Return、pending continuation は上表であり、他の H 仮定は生まれない。全 V/W/T/Car components の一段条件を満たすので、同じ relative-coinduction lemma が wrapper membership と root world を結論する。

**独立性。** D、raw development、ActualAdm の immediate preconditions は先に固定されたまま。candidate membership を challenge admission の条件に入れない。source profile/authority/guard は以下の元局所 laws から供給し、H の要素であることをその証拠にしない。これで全 complete clause が閉じる。□

## 5. profile/guard と field correspondence の供給元

| field | original constructor からの実供給 |
| --- | --- |
| declaration/root/role/entry | ℓ_w の registered Lambda/ClosureOrigin、実 fresh allocator、ValueEntry(I_z)。typed source role を後の solved shape で変えない。 |
| capture/scope/alias | 実 Resolve(x) と WR1、同じ E₀ と future restriction。z は元 formal scope で fresh rebind。 |
| entry admission/receipt/typed path | I_z の independent challenge と元 entry/return transition law。raw source label から権限を推論しない。 |
| record/body result | WR2 の fieldwise same-world rule、元 record/result injection、同じ x の provider/future。 |
| native Op の local typing law | Record の law は各原 field の complete certificate から上の同一 tuple introduction を行う関数。Return law はその同じ value/world を元 Return clause に包む関数。これらは wrapper membership を前提としない。 |
| signature support/licensing | native signature §3.4 の operand/local-origin constructor を上の local law に適用。schema だけを license evidence としない。opaque primitive の元 license はその primitive law の入力。 |
| source-owned unannotated policy | genuinely local Lambda/Record/Result introduction の licensed projections にだけ元の full-protection/no-concrete-removal policy。capture x の inherited partition/policy は元のものを輸送する。 |
| dynamic authority/history | 元 independent compatible event、actual receipt/rebind/return/resume の law。maker が終了したことを現在の live permission に読み替えない。 |
| whole independent alternatives | 実際の arm declaration とその complete original proof。存在しない arm を追加せず、存在する arm は全部 IF_w に残す。 |

この表の primitive/history/arm laws は、選択済み Strict/Step と Source-Generalize が明示する独立 semantic kernel の入力である。これらを元の rule schema より弱い条件へ定義し直してはいない。WR1–WR3 が新しく構成するものは、**この source wrapper の** full composite introduction であり、全 composite validity を一つの入力に隠していない。外国の guard または未指定 State law の証明が得られたという主張ではない。

## 6. 元 source への適用と未完了親

原 source の各 actual f activation κ が x:A を同じ world で保持するとき、WR3 はそこで評価される ℓ_w の complete membership を与える。A=Int と A=Bool の場合も同じ proof function をそれぞれの実 input certificate に適用する。異なる activation の x、wrapper root、current world を同じにしない。原 schema の同じ x-result dependency を保持しているので、正常 body Return の a field は必ずその invocation が捕捉した x である。

内側の `h(f x)` を遅延した実 argument carrier t が I_z を満たすことが後に証明できれば、WR3 の admission と complete elimination をその同じ t へ適用できる。t が pending/divergent なら body は未実行のままであり、上の proof はそれも含む。現在は f/h の full Call certificate とその carrier proof を構成したことにはしない。

この結果は元 result-replay に現れる wrapper の **actual source closure/body** の typed supplier になる。native の `Record(B)≤R` という発行 origin だけからこの証明を逆に取り出すことはしない。原 recursive f の simultaneous construction、そこから全 actual entry の型付け、native receiving occurrence と publication/use の対応、元 A/B と全体停止性は残る。

## 7. 凍結入力・査読境界

契約 `tasks/agent-loop/sprints/generated-call-operator-20261024.md` SHA-256 `cbff651522318a4949e6c12de5b4357ab320d8c55c2242d80cd8271b2951fdb5` の19入力を使用する。以下は constructor を具体化する際に追加して読んだ既存の選択済み依存であり、契約の凍結 hash を変更していない。

| 追加入力 | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` |
| `notes/design/2026-10-08-pure-read-call-result-constructor.md` | `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488` |

primary 単著。test/build/probe/compiler/implementation は作成・実行していない。独立査読では、WR3 が Strict の full hard envelope と genuine guards を保持していること、singleton replacement に wrapper 自身の完成済み証拠が混入しないこと、Record field が latent なときに勝手に Force しないことを特に確認する。
