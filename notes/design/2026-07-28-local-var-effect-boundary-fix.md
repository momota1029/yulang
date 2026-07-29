# local mutable state の effect boundary 修正設計

日付: 2026-07-28

状態: **未承認・ユーザレビュー待ち（改訂あり）**

調査基準は `fb2fbbea`。既知の症状と6回の試行・調査は
`notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md` を正本とし、本書では
設計判断に必要な差分だけを扱う。

## 改訂履歴

### 2026-07-29: v4 から v5 — local callback parameter の concrete ref 接続を遅延

v4 §4.2 は、local binding の `prepare` で callback lambda parameter を
`ref [F(P)] P` へ接続してから callback body を lower するとしていた。この順序は誤りだった。
21回目で正しい block-aggregate 経路へ直しても複数文 callback body から family が漏れ、
22回目の8地点 instrumentation（bug note `4311f845`、比較 test `23459b3b`）により、
body lowering 前の concrete local-ref 接続が漏れの必要十分条件だと確定した。

wrapper、block aggregate、callback `Fun.ret_eff`、callback evaluation effect、TypeLevel を
同じに保ち、parameter への reference structure 接続だけを helper resolution まで遅らせると、
二段目 application result と enclosing finalized scheme の両方から family が消えた。
TypeLevel だけを parsed lowering に揃えた対照では漏れが残ったため、修正対象は body level
ではなく parameter type を concrete 化する時点である。

v5 では、local callback parameter を ordinary lambda と同じ fresh type variable として
scope へ入れ、そのまま body を lower する。body lowering 後、その variable を
`Fun.arg` に持つ callback value を組み立て、resolved helper へ `init` と callback value を
二段 apply する。helper scheme が期待する `ref [F(P)] P` との接続は、二段目 application の
ordinary subtyping が helper instantiation 時に初めて作る。

helper の target scheme、real `run` を唯一の subtraction owner とする機構、
exact local-ref capability、runtime `ArgEffectContract` は変えない。この訂正は explicit family
contractを再導入せず、「既存 scheme の instantiation と application に制約を供給させ、
lowering が手置きしない」という v4 の原則を callback argument type の接続時点にも適用する。
LVB-A3 / LVB-A4 が示した helper scheme と application transport は反証されていないが、
body lowering前のeager connectionが安全だというproduction lifecycleの十分性までは
示していなかった。v5では22回目のdeferred-reference対照をその不足分のgateとする。

この訂正により、承認状態は引き続き
「未承認・ユーザレビュー待ち（改訂あり）」とする。

### 2026-07-29: v3 から v4 — subtraction owner を既存 `run` へ一本化

v3 は、compiler-private helper の callback `ret_eff` に
`push(Set(F, [P]))` を明示的に置き、同じ helper の本体を

```text
with_ref init callback =
    run init (callback var_ref())
```

とする設計だった。LVB-A は、この手置きした negative `ret_eff` の stack evidence が
`compact_neg_stack_effect` により concrete row prefix `F(P)` へ materialize され、helper
result と ordinary residual `ρ` を共有できることを isolated witness で示した。

しかし LVB-B の最初の production call site で、helper 本体が適用する**既存 `run` の scheme
自身**も同じ local family の subtraction boundary を持つことが判明した。LVB-A は real
`run` scheme の instantiation と application を一度も作らず、callback contractだけを手で
組んでいたため、この二重所有を観測できなかった。実機では helper 側の独立 contract と
`run` 側の既存 boundary が同じ effect chain に入り、一つの `SubtractId` に
`Empty` と `Set(F, [P])` が合流して `merge_same_id_family` の
one-ID-one-family invariant に違反した。

v3 の誤りは negative-side materialization という機構の理解ではなく、**その機構を起動する
source の所有権**にあった。`run init (callback var_ref())` では、callback application の
fresh return effect が `run` の computation argument effectへ通常の function subtypingで
接続される。既存 `run` scheme はすでに

```text
input computation: [F(P); ρ] R
handler result:    [ρ] R
```

の対応を持つため、helper lowering が callback `ret_eff` へ同じ family annotationをもう一度
置く必要はない。v4 は `run` の scheme instantiationを唯一の型レベル subtraction sourceとし、
callback callと helper resultには ordinary fresh effect slotだけを置く。compiler-owned callを
generic unannotated-call用の `Empty` stack pairへ流すこともせず、helper-localな
`SubtractId` を一つも作らない。

`compact_neg_stack_effect` の知見は残るが、production graphで familyを materializeする正しい
negative boundaryは、まず既存 `run` schemeを作る側にある。helper側は、その finalized schemeを
instantiateし、application subtypingで concrete familyと同じ `ρ` をcallback `ret_eff`へ運ぶ。
したがって LVB-A は primitive の isolated characterizationとして残る一方、production wiringの
十分条件ではない。v4 は real `run` の scheme instantiationと二段 applicationを含む LVB-A2を
新しい production gateにする。

runtime hygieneについては別責務として残す。callback-originの `F(P)` を内側の `run` handlerへ
見せる `ArgEffectContract` markerは必要だが、これは path / depthを運ぶ runtime certificateで
あり、stack factや `SubtractId` を作ってはならない。markerも synthetic `run` が処理する family
から導出し、型 annotationを再導入する入口にはしない。

この訂正により、承認状態は引き続き
「未承認・ユーザレビュー待ち（改訂あり）」とする。

### 2026-07-29: v2 から v3 — target invariant と carrier の再設計

v2 は、compiler-generated ref を引数に取る scoped lambda を作り、ref の invariant な
effect argument 内へ `push(Set(local-family, payload))` を置けば、body の実使用を通じて

```text
argument ref effect: [local-family(payload); ρ]
body/result effect:  [ρ]
```

という concrete row correspondence が残る、とした。

5回目の read-only investigation により、この前提は反証された。区別すべき軸は
parameterized family の引数の有無ではなく、family が**独立した concrete row item**として
存在するか、`StackWeight` の push / pop evidence 内だけに存在するかである。

- `StackWeight::push_pops` は、arity や payload を見ずに matching push 全体を消す
- positive `Pos::Stack` が invariant constructor argument の中へ入ると、
  `compact_neu_id` は family を row prefix にせず `CompactVar` の weight へ畳む
- `Fun.arg` の反変性の下にあるその weight は covariantly live と数えられず、prune される
- act method の `Set(owner)` も同じく消える。act method を成立させるのは family metadata
  ではなく、receiver の実使用が作る通常の `receiver_effect` correspondence である

したがって v2 が目標にした追加の concrete row item は、push-only scoped carrier からは
一度もその形で生まれない。誤りは scoped lambda の組み方だけではなく、target invariant を
`ref` の invariant effect argument へ置いたことにもある。local ref 自身の operation effect
と、callback body 全体の ambient residual `ρ` は別の責務であり、後者を
`ref [local-family; ρ] payload` へ詰める根拠はなかった。

v3 は target を、ref value ではなく実際の callback computation boundary へ移す。
compiler-private な callback-form helper を使い、概念上

```text
(ref [local-family(payload)] payload
    -> [local-family(payload); ρ] result)
-> [ρ] result
```

を一つの function scheme として表す。callback が helper の argument になるため、その
return effect は negative-side effect slot を通る。ここでは既存の
`compact_neg_stack_effect` が active family を concrete row prefix へ materialize できる。
v2 の push-only ref carrier は廃止し、LVB-A もこの negative-side contract を production
lowering 変更前に証明する characterization へ置き換える。

この訂正により、承認状態は引き続き
「未承認・ユーザレビュー待ち（改訂あり）」とする。

### 2026-07-28: v1 から v2 — raw `SubtractId` 生存モデルの訂正

承認済みだった v1 は、act method の push / pop が raw `SubtractId` のまま
generalization を越え、stack binder として alpha-renaming される、と説明していた。
LVB-A characterization と production act-method の直接 trace により、この説明は誤りだと
判明した。

実際には、body が receiver を使うことで通常の effect type variable が argument side から
return side へ流れ、その chain 上で push と pop が相殺される。使用済み
`SubtractId` は scheme から消え、production act-method の
`stack_quantifiers: []` は正常形である。v2 は raw ID の生存ではなく ordinary variable
correspondence を target にしたが、family が push evidence から concrete row item に変わると
いう別の誤った前提を残した。

## 0. 決定の要約

local mutable state boundary を、compiler-private な callback-form helper として表す。
ただし v3 と異なり、helper 自身は callback effectに `F(P)` を宣言しない。synthetic
`var.run` の既存 schemeを唯一の subtraction ownerとする。

一つの synthetic local-var familyを `F`、payloadを `P` と書く。helper loweringを開始した
時点では、callback return effect `ε` と helper result effect `δ` は ordinary fresh slotである。

```text
local ref capability:
    ref [F(P)] P

callback before run application:
    ref [F(P)] P -> [ε] R

helper result before run application:
    [δ] R
```

ここで `ref [F(P)] P` は helper definition 側の expected callback shape であり、local binding
側の callback lambda parameter を body lowering 前に concrete 化する指示ではない。
local callback は body lowering 中、ordinary fresh variable `α` を argument に持つ。

```text
local callback during body lowering:
    α -> [κ] R
```

`α` は body 内の実使用から通常の制約を受けうるが、この時点では exact
`ref [F(P)] P` structureへ先回りして接続しない。body lowering 後に callback valueを
helperへapplyし、resolved helper schemeをinstantiateした二段目applicationのsubtypingが
`α` と expected callback argumentを接続する。

compiler-private helper の意味は次である。

```text
with_ref init callback =
    run init (callback var_ref())
```

`run` referenceを通常どおり resolve / instantiateし、`init` と
`callback var_ref()` へ二段 applyする。function argument effectの反変 subtypingにより、
callback applicationの `ε` が instantiated `run` の input computation effectへ接続される。
同じ `run` instanceの return effectが `δ` へ接続されるため、helperをgeneralizeした最終形は
次になる。

```text
with_ref:
    P
    -> (ref [F(P)] P -> [F(P); ρ] R)
    -> [ρ] R
```

この形は helper signatureへの入力 annotationではなく、既存 `run` schemeから導かれる
principal resultである。`F(P)` は callback の実際の return effectにある独立した concrete row
item、`ρ` はcallback effectとhandler resultに現れる同じ ordinary type variableであり、
raw `SubtractId`ではない。local refの effect argumentは、そのref operationが実際に起こす
exact family `[F(P)]` のままとし、body全体の ambient residual `ρ` を混ぜない。

callback applicationは既存 `run` の handled computation内で起動する。callback valueを
helperへ渡す時点ではbodyを評価しない。`var_ref()` のconstructionと `&x` のbare lookupは
pureのままであり、runtime state handlerは引き続き synthetic `var.run`だけが所有する。

helperのcallback parameterはfunction typeなので、helperの正のfunction rootから見ると
negative positionにある。最終的なcallback `ret_eff` のconcrete rowは、real `run` schemeを
作るnegative effect boundaryでmaterializeされたものを通常のapplication constraintが運ぶ。
helper loweringは独立した `Neg::Stack` を作らない。使用済みstack IDは `run` schemeの
generalizationで消えてよく、helperのfinal schemeも `stack_quantifiers` は空でよい。

この設計では次を行わない。

- callback `ret_eff` へ helper-owned `push(Set(F, [P]))` を置かない
- callback callへ helper-owned `push(Empty)` / `pop` pairを置かない
- `run` boundaryとcallback boundaryを別々の `SubtractId` に分けない
- invariant な `ref` effect argument の中へ push-only carrier を再導入しない
- local ref effect を `[F(P); ρ]` に広げて ambient residual を持たせない
- constructor variance または stack liveness を local-var のために変更しない
- v3 の初期 slice で `Pos` / `Neg` / `Neu` に computation 専用 variant を追加しない
- `Scheme` に第2 predicateや raw computation pair を追加しない
- generalize / instantiate の binder 規則を変更しない
- 異なる scheme 間で一つの `SubtractId` を共有しない
- `directed_weight` の family invariant を緩めない

## 1. 問題

bug note の repro では、local ref、synthetic `run`、ref を中継する値が別々の
generalization root になる。local ref の scheme には exact local family が見えても、
callback computation の

```text
[F(P); ρ]
```

と handler result の

```text
[ρ]
```

を結ぶ subtraction contract が同じ scheme として運ばれない。specialize は、その失われた
対応を復元できず、local-family を含む候補と含まない候補を衝突として報告する。

post-body の `wrap_var_binding_run` で同じ `SubtractId` を ref scheme と handler resultへ
配る attempt 1 は generalization で identity を失った。body lowering 後に push を
retrofit する attempt 2 は、既存 lower と同じ slot へ `Empty` / `Set(F, [P])` を重ね、
one-ID-one-family invariant に違反した。

v1 / v2 はこの gap を、ref と body を一つの `Fun` root に入れることで埋めようとした。
しかし ref の invariant effect argument 内にある positive push は concrete row prefix に
ならない。修正すべきものは compaction の arity 分岐でも pruning の保護規則でもない。
実際に handler が受け取る callback computation を function boundary として表し、callback
effect と handler result を一つの helper scheme に置く必要がある。

v3 はここでさらに一歩誤り、helperの callback `ret_eff` へ family-bearing contractを独立に
置いた。productionの helper bodyは同時に existing `run` をapplyするため、local familyの
subtraction ownerが二つになった。`merge_same_id_family` は同じ `SubtractId` に二つの
`Some(Subtractability)` が合流したとき、完全一致だけを許す。ここへ `Empty` と
`Set(F, [P])` が来たpanicはsolverを緩めるべき症状ではなく、「一つのsemantic handlerへ
二つの独立boundaryを割り当てた」ことを検出した正しいstop conditionである。

v4では helperの形は維持するが、subtraction relationをhelper signatureへ手置きしない。
既存 `run` のfinalized schemeをinstantiateし、ordinary application/unificationでcallback
return effectとhelper resultへ運ぶ。これにより一つのruntime handler、一つの型レベルowner、
一つのresidual correspondenceを一致させる。

## 2. 調査結果

### 2.1 5回目の調査で確定した消失機構

`crates/infer/src/constraints/machine/propagate.rs` の
`pos_is_effect_marker_row_item` は、`Pos::Con(path, args)` の `args` を見ず、登録済み
family path かどうかだけで row item を分類する。同じ path の payload と row tail は
`enqueue_derived_row_item_neu_args` と
`enqueue_derived_upper_tail_to_lower_row_tail` の別々の辺として処理される。
したがって payload-bearing family の row-tail transport が arity 分岐で落ちる、という
v2 までの作業仮説は誤りである。

独立した `Pos::Row` / `Pos::Con(F, [P])` は `compact_pos_row` と
`merge_row_items_with_sink` を通り、path と payload を保ったまま compact row に残る。
一方、`crates/poly/src/types.rs` の `StackWeight::push_pops` は matching pop の数だけ
`entry.stack` を truncate する。`Subtractability::Set(path, args)` の path、arity、payload は
一切見ないため、push 内だけにある family は丸ごと消える。

positive `Pos::Stack` は `compact_pos_id` で inner へ weight を畳み込む。local ref の effect
argument は `Neu::Bounds` の invariant constructor argument なので、`compact_neu_id` は
その weight を `CompactVar` occurrence へ運ぶだけで、concrete prefix を作らない。
concrete stack prefix を作る既存経路は、effect slot 専用の
`compact_neg_stack_effect` である。

`collect_live_stack_ids_in_type` は root を covariant に開始し、`Fun.arg` /
`Fun.arg_eff` で polarity を反転する。ref constructor argument はその負の位置を引き継ぐ
ため、active push があっても covariantly live と数えられない。
`cleanup_stack_weights_in_root_and_roles` と
`prune_dead_subtract_weights_in_type` はその ID を除去する。

act method の `Set(owner)` も同じ経路で除去される。act method の正常形を支えるのは
owner family の生存ではなく、body が receiver を実際に使うことで
`receiver_effect` が argument から result へ流れる ordinary correspondence である。
local-var に act-method の push placement を移植しても、追加の concrete row item は得られない。

### 2.2 `ref` の invariance が意味するもの

`std::control::var::ref 'e 'a` の `'e` は、lowering で
`invariant_var_arg(effect)` により `Neu::Bounds(lower, upper)` へ入る。同じ nominal
constructor 同士の subtype は `enqueue_derived_invariant_neu_args` が両方向の制約を作る。
現在の invariance は、この generic nominal-constructor 表現に由来する。

`lib/std/control/var.yu` の surface declaration では、

```text
get:           () -> ['e] 'a
update_effect: () -> [ref_update 'a; 'e] ()
```

のどちらも `'e` を operation の output effect として使う。片方が effect を読み、片方が
effect を書くために `'e` が意味論上 invariant、という証拠はない。payload `'a` は
`get` の output と `ref_update` / update function の input の両方へ現れるため invariance の
根拠があるが、`'e` と同一視してはならない。

ただし、ここから直ちに `'e` を contravariant / covariant pair に分けてよいとはならない。
現行 `CompactBounds::Con` の liveness traversal は constructor ごとの variance を持たず、
outer `Fun.arg` の負極性を argument 全体へ伝える。local-var ID を live にするためだけに
反変 facet を追加すると、surface API に存在しない「ref が effect を入力として消費する」
経路を捏造する。constructor variance を一般化するなら別 project として型宣言、subtyping、
compact、role / cache compatibility まで設計する必要がある。

### 2.3 v2 target invariant の訂正

local ref capability と callback body effect を分ける。

```text
ref capability       = [F(P)]
body ambient effects = [ρ]
callback effect      = [F(P); ρ]
handled result       = [ρ]
```

`ref [F(P); ρ] P` とすると、ref の `get` 一回にも body の他の operation `ρ` を課す。
これは ref が起こす effect と、ref を使う computation が別途起こす effect を混同する。
v2 の target は push-only carrier で到達不能だっただけでなく、この責務分離も証明して
いなかった。

v3 が scheme に残したい concrete item は callback の `ret_eff` にある `F(P)` である。
ref argument 内には exact capability `F(P)` が既存の concrete row として残るが、そこへ
residual correspondence の責務を負わせない。

### 2.4 negative-side effect slot は既存の materialization boundary である

`compact_neg_id` が `Neg::Fun` を読むと、function の `ret_eff` を
`compact_neg_effect_id` へ渡す。そこに `Neg::Stack` があれば
`compact_neg_stack_effect` は active `Set(path, args)` を concrete row prefix に変え、
inner effect を tail として残す。

これは generic `Neg::Stack` を constructor argument 内へ置く経路とは異なる。
`Fun.arg` の data type や `Neu::Bounds` の upper を `compact_neg_id` で読むだけでは
prefix materialization は起きない。computationの実際のnegative effect slotへ置くことが
必要である。

既存の compact characterization
`compact_neg_stack_effect_surfaces_concrete_push_as_row_prefix` は、payload のない family で
この性質を固定している。
`negative_filter_stack_effect_projects_set_as_row_prefix` は `Neg::Fun.ret_eff` 経由を固定する。
LVB-A はこの形を payload-bearing synthetic family と shared residual まで拡張した。この
primitiveの理解はv4でも正しい。

誤っていたのは、helper callbackの `ret_eff` に新しいstackを置く必要がある、とした点である。
productionではsynthetic `run` 自身のcomputation argumentがすでにnegative effect slotであり、
そのschemeをgeneralizeする過程で同じmaterialization規則を通る。helperがresolveする時点の
`run` は、その結果であるconcrete `F(P)` prefixとordinary `ρ` correspondenceを持つfinalized
schemeである。helper側はこれをinstantiateして運べばよく、同じprimitiveをもう一度
helper-owned stackで起動してはならない。

### 2.5 real `run` application が作る single-source flow

`wrap_var_binding_run` のproduction shapeは、

```text
run_ref = lower_var_act_member(act, "run")
run_with_init = make_internal_app(run_ref, init)
result = make_internal_app(run_with_init, body)
```

である。`lower_var_act_member` はresolved `DefId` を使うrefを作り、analysisの
`ApplyRefResolution` がそのdefinitionのfinalized schemeをuse siteへinstantiateする。
`make_internal_app` はargument computationのvalueとeffectを
`Neg::Fun { arg, arg_eff, ... }` のexpected sideへ置く。

`Pos::Fun <: Neg::Fun` のpropagationはfunction argument effectを反変に接続する。したがって
helper bodyを

```text
run init (callback var_ref())
```

とlowerすると、次の同じapplication chainができる。

```text
callback ret_eff ε
    -> callback application effect ε
    -> instantiated run input computation effect [F(P); ρ]

instantiated run result effect [ρ]
    -> helper body effect δ
    -> helper ret_eff
```

ここで`ε` / `δ`はhelperが作るordinary variableであり、helper-owned stack IDではない。
`F(P)` と `ρ` の関係は一つの`run` instanceから来る。callbackのnegative positionをcompact
すると、run側から伝播したconcrete rowがcallback `ret_eff` に見える。productionで
`compact_neg_stack_effect` が正確にどのrootでmaterializeしたかはLVB-A2で構造的に固定するが、
helper自身が第二のfamily-bearing stack sourceを持たないことは設計上の必須条件とする。

ordinary callback parameterを既存のgeneric unannotated-call lifecycleへそのまま流すと、
`unannotated_local_callee_return_effect` が `Subtractability::Empty` のpush/pop pairを作る。
これはfamily annotationを消した後にも独立sourceを残すため、v4のsingle-source設計では使わない。
compiler-private helperはcallbackをcallableだと既知のparameterとして作り、call return effectを
bare fresh variableへ接続する。現行の区分で表すなら
`LocalCallReturnEffect::Annotated` 相当だが、`F(P)` のtype annotationを置くという意味ではない。

### 2.6 型 subtraction と runtime contract metadata を分離する

`poly::expr::ArgEffectContract` は、「多くのinferred callback effectはruntime contractでは
ないため、mono type shapeから後段が再構成してはならない」という明示的certificateである。
`PreserveMatchingPath` markerは、callback call siteですでに見えるmatching handlerが
callback-origin requestを処理できるようにする。`with_ref` のcallbackは外側で作られ、内側の
`run` handlerで実行されるため、このcertificateは必要である。

一方、markerはpath / depth / resume policyだけを持ち、型solverのstack factではない。
v3は一つのsurface-like annotationからtype-level stackとruntime markerの両方を生成し、
二つの責務を結び付けた。v4では次を分ける。

- type relationはexisting `run` schemeだけからapplication subtypingで導く
- runtime markerはsynthetic `run` が処理するfamily pathからcompiler certificateとして導く
- markerの生成は`Neg::Stack`、declared subtract fact、`SubtractId`を一切作らない
- markerを作れない場合、type annotationを復活させずstopする

## 3. 候補方向の比較

| 方向 | soundness risk | blast radius | production 前 characterization | 判断 |
| --- | --- | --- | --- | --- |
| A. existing `run` を唯一のownerにし、applicationでcallback contractを導く | 低〜中。ordinary subtypingと既存handler schemeを使う。generic `Empty` pairを避け、runtime markerを非subtractiveに分離する必要がある | 中。private helperとlocal-var loweringが中心 | real `run` schemeのinstantiate＋二段applicationをLVB-A2でproduction未変更のまま固定できる | **推奨** |
| B. callback boundaryと`run` boundaryを異なる`SubtractId`へ分ける | 高い。一つのsemantic handlerに二つの消去順序を与え、over-subtractionまたは順序依存を作る | 中〜高。helper、stack composition、generalizeの新しいownership規則が要る | two-ID witnessは作れるが、runtime一handlerとの意味対応を別途証明する必要がある | 採らない |
| C. helper自身を唯一のhandlerにし、既存`run` applicationを除く | 中〜高。ownerは一つになるが、実績のあるrecursive handler実装とruntime orderを置き換える | 高い。synthetic act body、runtime handler、cache / specializationへ波及 | standalone helper handlerのcharacterizationは可能 | Aが失敗した場合の別設計 |
| D. 新しいcomputation-polarity IRを作る | 意味論は明示できるが実装回帰リスクが高い | 非常に高い。全type walker、compact、generalize、cache、specializeへ波及 | isolated IR testは可能だが導入自体が別project | A/Cが失敗した場合のscope decision |

### 3.1 A: `run`-derived single source

existing `run` はsurface上

```text
my run(v: P, x: [_] R): R = catch x:
    ...
```

と宣言され、そのcatch loweringとscheme generalizationがlocal familyをinput computationだけ
から引き、resultへordinary residualを返す関係をすでに作る。helper bodyがそのreal definitionを
通常どおりinstantiateしてapplyする以上、同じ関係をcallback signatureへ再宣言する理由はない。

この案はcallback-form helperの目的を保つ。ref capabilityとbody computationを一つのfunction
schemeへ入れる一方、subtractionのsemantic ownerは実際にhandlerを実装する`run`だけにする。
LVB-A2で`run`からcallbackまでのconstraint routeを固定できるため、production変更前の
反証可能性も最も高い。

### 3.2 B: 二つの pair を異なるIDへ分離

別IDなら`merge_same_id_family`の直接panicは避けられる。しかしpanicを避けることと型の意味が
正しいことは別である。callback側pairと`run`側pairはどちらも同じ`F(P)`をsubtractすると主張し、
runtimeにはhandlerが一つしかない。二つのpairのnesting順で、一方がfamilyをmaterializeした後に
他方がもう一度消す、または片方の`ρ`だけがresultへ残る可能性がある。

この案を正当化するには二つのIDが異なるsemantic boundaryだと説明する必要があるが、
`with_ref init callback = run init (callback var_ref())` にはその第二handlerが存在しない。
residual correspondenceのownerも二重になる。ID分離はone-ID invariantを迂回するだけで、
根因に最も近い修正ではないため採らない。

### 3.3 C: helperへhandler実装を移す

`with_ref` 自身が`catch`を実装し、既存`run`を呼ばない形ならsubtraction ownerを一つにできる。
これは方向Aと同じsingle-owner原則には従う。しかし現在の`run`は再帰的なget/set handler、
continuation resume、rollback semanticsをすでに担っている。その実装をhelperへ複製または移動
すると、runtime orderとhygieneの再検証範囲が大きい。

Aのreal-run applicationがstructural correspondenceを作れないとLVB-A2で判明した場合に限り、
「`run`をcallback-form APIへ置き換える」別設計として比較し直す。Aと同時に実装しない。

### 3.4 act-method比較

`connect_act_method_receiver_effect` はfreshな一つの`SubtractId`を作り、
`push(Set(owner))`を`receiver_effect`へ置く。`lower_act_method_body_expr` は同じIDのpopを
lambda output predicateへ置く。bodyのreceiver実使用が同じordinary `receiver_effect`を
argument側からreturn側へ流し、この一つのpairがfunction boundary内で相殺される。

act methodはそのbody内で、同じownerを処理する別handler schemeをapplyしない。receiver
boundaryそのものが唯一のownerなので、explicit pairとexisting handler machineryの競合がない。
local helperは逆に`run`へhandler処理を委譲する。したがってact-methodのpairをhelperへ複製する
のではなく、`run`を唯一のownerに残すことが同じ構造的回避になる。

### 3.5 D: computation-polarity IR

callback-form helperとexisting `run` applicationは、既存の本物のfunction / effect polarityを
使える。まずLVB-A2でこれを検証する。single-source routeがstructural contractを作れない、
またはnon-subtractive runtime markerではhandler visibilityを保てないと判明した場合は、
two-ID patchやliveness patchへ戻らず停止する。その時点でCまたは新IRのblast radiusを
受け入れるか、ユーザのscope decisionを得る別設計へ移る。

## 4. 選んだ設計: compiler-private callback boundary

### 4.1 helper contract

一つの synthetic local-var act copy につき、既存 private `var_ref` / `run` と同じ owner に
compiler-private helper を持たせる。以下では仮に `with_ref` と呼ぶが、実装名は builtin
kind または resolved `DefId` として構造化し、inference 中の文字列 special case にはしない。

generalize後に要求する概念型は次である。

```text
with_ref:
    P
    -> (ref [F(P)] P -> [F(P); ρ] R)
    -> [ρ] R
```

概念実装は次である。

```text
with_ref init callback =
    run init (callback var_ref())
```

この概念型をhelper parameterへannotationとしてlowerしない。helper構築時は次のordinary
slotから始める。

```text
callback ret_eff = ε
helper body eff  = δ
```

`ε` にはhelper-owned `Neg::Stack`を置かない。callback callにもgeneric unannotated-callの
`push(Empty)`を置かない。real `run` definitionを通常のresolved refとしてinstantiateし、
二段applicationが作るsubtypingだけで`ε = [F(P); ρ]`、`δ = [ρ]`の構造へ到達させる。
helper resultの`ρ`は同じrun instanceに由来するordinary type variableであり、
generalize / instantiateの通常経路でfreshenされる。

helper を public `std::control::var` API にはしない。synthetic act copy の private member、
または同じ型構造を作る compiler-owned resolved definition とする。どちらを選んでも
family path と payload は通常の act-copy substitution / symbol resolution から得て、
path 文字列比較で推論しない。

helper callback parameterにはruntime用`ArgEffectContract` markerを付ける。markerは
synthetic act copyのstructured ownerから`F`を得るが、type annotation loweringを通さず、
stack weightやsubtract factを作らない。type relationとruntime visibility certificateを
同じbuilderから二重生成しない。

このhelper-side expected typeと、caller-side callback lambda parameterのlowering lifecycleを
区別する。helperのfinal schemeは引き続きcallback argumentへexact `ref [F(P)] P`を要求するが、
callerはその構造をannotationや`constrain_local_ref_value`で先に置かない。resolved helperの
scheme instantiationと二段目applicationが作るordinary subtypingだけを接続元とする。

### 4.2 lowering lifecycle

#### private helper definition

1. synthetic act copyのstructured owner、payload `P`、existing private `var_ref` / `run`の
   resolved `DefId`を確定する
2. `init: P` と callable `callback` parameterを作る。helper definition側のexpected callback
   argumentはexact `ref [F(P)] P`、return effectはordinary fresh `ε`、resultはfresh `R`
   とする。このexpected shapeをlocal binding側のcallback lambda parameterへ先置きしない
3. callback localはcallable skeletonを既知とし、call return effectをbare `ε`へ接続する。
   generic unannotated-call用の`Empty` pairは作らない
4. callback parameterへnon-subtractiveな`ArgEffectContract(F, depth=1)`を登録する
5. existing `var_ref()`を通常のresolved refとしてlowerし、`callback var_ref()`をapplyする
6. existing `run`を通常のresolved refとしてlowerし、`init`、
   `callback var_ref()`の順にapplyする
7. callback application effectをinstantiated `run` のcomputation argumentへ、run result
   effectをhelper body effectへ接続する
8. bodyからhelperをgeneralizeし、target final schemeをannotationではなくderived resultとして
   得る

#### local binding prepare（callback body lowering前）

1. synthetic act copy、init binding、payload `P` を確定する
2. ordinary lambda parameterと同じく、callback lambdaのparameter value `α` をordinary
   fresh type variableとして作る。この時点ではexisting `var_ref()` のexact value type
   `ref [F(P)] P`へ接続しない
3. `α` を持つ`&x`をpureな`Def::Arg`としてlocal scopeへbindする
4. `&x` がscopeにある状態で`<rest>`を通常のblock-aggregate経路からlowerする。body内の
   `&x`の実使用は`α`へ通常の制約を加えてよいが、prepareはconcrete ref structureを
   pre-bindしない

callback lambdaの`Fun.arg_eff`は`Never`のままにする。ref constructionとbare lookupはpureで
あり、local operation effectは`$x`の`get`、`&x`の`update_effect` / `RefSet`、その他ref
methodの実使用からcallback body effectへ入る。

#### local binding finish（callback body lowering後）

1. prepareで作ったfresh parameter `α`を`Fun.arg`、exact pureな`Never`を`Fun.arg_eff`、
   block aggregateのbody effect / valueを`Fun.ret_eff` / `Fun.ret`とするlambda valueを作る。
   lambda value自身のevaluation effectもexact pureとする
2. private `with_ref`のresolved referenceをinit valueへ`make_internal_app`でapplyする
3. その結果へcallback lambda **value** を二段目の`make_internal_app`でapplyする。この
   application edgeへhelper schemeがresolve / instantiateされたとき、そのexpected
   `ref [F(P)] P` argumentと`α`がordinary application subtypingで初めて接続される
4. callback bodyのapplicationはhelper内のexisting `run` computation argumentとして
   評価される
5. callback lambda parameter scopeを終了する

local lowering は ref argument の中へ独自 push / pop を組み立てない。
private helperもcallback `ret_eff`へ独自push / popを組み立てない。
subtraction contractはexisting `run` schemeが所有し、private helperのschemeはその
applicationから導かれる。
local callback parameterへbody lowering前のexact ref lower / upper boundも置かない。
standalone local ref `Let` scheme と handler result scheme の間で raw ID を共有しない。

### 4.3 v2 scoped lambda との違い

v2 は次を local lowering 内で作った。

```text
run init ((\&x -> body) var_ref())
```

さらに ref effect argument 内へ push を置き、callback body output の pop と相殺して
concrete family が残ると期待した。v3 はtargetをcallback computationへ正しく移したが、
callback `Neg::Fun.ret_eff`へ第二のfamily-bearing stackを手置きした。v4はそのownershipを
訂正する。

- family contract はinvariant ref argument内の`Pos::Stack`にも、helper-owned callback
  `Neg::Stack`にも置かない
- concrete prefixはexisting `run` schemeのnegative computation boundaryでmaterializeされ、
  helper applicationがcallback `ret_eff`へ運ぶ
- ref argument は exact `[F(P)]` のままで、ambient `ρ` を持たない
- subtraction ownerはexisting `run`だけ、residual correspondenceのtransport unitは
  derived private helper schemeである
- local lowering は family-bearing `SubtractId` の owner にならない

同じ syntax tree の形に見えても、type evidence の owner と polarity が異なる。

### 4.4 callback hygiene と runtime order

callback-origin effect を内側 handler が捕捉できるかは、単なる path 一致ではなく callback
effect contract metadataに依存する。private helperのcallback parameterにはstructured
synthetic act ownerから導いた`F` markerを持たせ、このsynthetic state handlerだけがfamilyを
処理できるruntime certificateとする。type-level `F(P)` annotationは置かない。ambient `ρ` は
markerに入れず、local handlerへ許可しない。

characterization と implementation test では次を固定する。

- callback value の作成は pure であり、body は helper 呼び出し前に実行されない
- `callback var_ref()` は `run init` の handled computation 内で起動する
- callback contract markerは`F` pathとdepthを持つが、stack fact / `SubtractId`を作らない
- payload `P` のcorrespondenceはtype relationの`F(P)`とexact ref capabilityで保ち、
  path-only runtime markerへ型payloadの責務を持たせない
- unrelated outer / inner handler が callback-origin residual `ρ` を捕捉しない
- shallow / deep handler と continuation resume の可視性が従来から変わらない

### 4.5 複数 binding と対象 lowering path

複数の local var は現在の handler nesting を維持する。`run_inputs = [a, b]` なら概念上、

```text
with_ref_a init_a (\&a ->
    with_ref_b init_b (\&b ->
        body
    )
)
```

prepare は source order、finish は逆順とする。

同じ sugar を一部の構文だけ旧方式で残さない。少なくとも次を同じ helper lifecycleへ通す。

- ordinary block の `my $x = ...`
- tuple / record 等の var pattern binding
- lambda parameter の `$x`
- case value pattern の `$x`
- catch value / effect payload / continuation pattern の `$x`
- protocol lambda / protocol do continuation が作る local ref
- nested / multiple local var scopes

親 module には prepare / lower body / finish の orchestration を残し、構文別 call site が
独自に callback contract や push / pop を作らない。

## 5. 変更しないもの

- `650fec0b` の parameterized effect-family classification を revert、限定、迂回しない。
  `Pos::Con(path, args)` は args の有無にかかわらず、登録済み family なら row item である。
- `step_subtype` / `process_subtype` の fixed concrete-head matrix と
  `notes/design/2026-07-28-subtype-fallthrough-closure.md` の決定を変更しない。
- `directed_weight.rs` の one-stack-ID-one-family invariant を変更しない。
- `StackWeight::push_pops` の cancellation を payload-bearing family だけ止めない。
- co-occurrence analysis / polarity elimination に rigid、blocked pair、protected variable set
  を追加しない。
- stack liveness に local-var path、constructor kind、fixture 名の special case を追加しない。
- nominal constructor argument の invariance を今回の修正で変更しない。
- generalization boundary level、quantifier selection、instantiate の freshening を変更しない。
- helper scheme に non-empty `stack_quantifiers` を要求しない。
- helper callbackへtype-level explicit `F(P)` annotationを置かない。
- helper callback callへgeneric unannotated-callの`Empty` stack pairを置かない。
- callback boundaryと`run` boundaryを異なるIDへ分けて併存させない。
- runtime `ArgEffectContract` markerからstack factまたはrow constraintを再構成しない。
- synthetic act path、source path、function 名の文字列 special case を inference に追加しない。
- specialize の `ConflictingTypeCandidates` 比較を緩めない。
- current wrong output に合わせて正しい expected result を変更しない。
- public `std::control::var` API と runtime state semantics を変更しない。
- LVB-A2 が失敗した場合、承認なしに新しい computation IR を追加しない。

## 6. 実装 slicing plan

### LVB-A: negative callback boundary primitive（完了、production十分条件ではない）

LVB-Aはproduction loweringを変更せず、手で作ったcallback `Neg::Fun.ret_eff` の
`push(Set(F, [P]))` が次を満たすことを証明した。

- payload-bearing `F(P)` がindependent concrete row prefixへmaterializeされる
- callback tailとhelper resultが同じordinary `ρ`を共有する
- generalize / finalize後にraw IDが残らず、`stack_quantifiers`が空になる
- instantiateごとに`ρ` / `P`が正しくfreshenされる
- argument-less familyも同じpathを通る
- old invariant ref carrierだけではcorrespondenceを作れない

この結果は`compact_neg_stack_effect` primitiveのcharacterizationとして残す。ただしwitnessは
real synthetic `run` schemeをinstantiateせず、`run init (callback var_ref())` の二段applicationも
作らなかった。したがって「helperが同じstack sourceをproductionへ置いてよい」ことは証明して
いない。explicit callback contract metadataのtestも、type annotationとruntime markerを
一つのsurface annotationから作るv3形を固定しており、v4 production contractには使わない。

### LVB-A2: real `run` single-source transport characterization

このsliceもproduction lowering codeを変更しない。direct-call primitiveを固定し、
separate definition boundaryを検証するLVB-A3の前提とする。

変更:

- payload-bearing synthetic local-var act copyのreal `var_ref` / `run` definitionを通常のbody
  loweringでgeneralizeし、`run` のfinalized schemeがinput computationに`F(P)` prefixと
  residual `ρ`、resultに同じordinary `ρ`を持つことを構造で固定する
- helper-shaped witnessは`run` typeを手で複製せず、resolved definitionのschemeを実際に
  instantiateする
- callback parameterの`Fun.ret_eff`をordinary fresh variable`ε`として作り、
  explicit `F(P)` row、`Neg::Stack`、declared subtract factを置かない
- callback applicationをgeneric unannotated-call `Empty` pairへ流さず、bare `ε`を使う
- instantiated `run`を`init`へapplyし、その結果を`callback var_ref()` computationへapplyする
  productionと同じ二段application constraintを作る
- pre-compact graphでhelper-owned family-bearing IDもhelper-owned `Empty` IDも存在せず、
  one-ID-one-family invariantへ異なるfamily claimが合流しないことを固定する
- constraint provenanceまたは構造traceにより、callback effect上の`F(P)` requirementと
  helper resultの`ρ`が同じ`run` instanceから到達したことを固定する
- compact / generalize後、callback `ret_eff`からconcrete `F(P)` prefixとtail `ρ`を取り出し、
  helper result effectが同じordinary `ρ`を持つことを固定する
- family materializationが`run` scheme generalization時に完了しているか、helper root compact
  時に伝播したnegative boundから再構成されるかを構造で記録する。どちらでも
  `compact_neg_stack_effect`の既存規則だけを使い、helper-owned second sourceがないことを
  必須とする
- final helper schemeの`stack_quantifiers`が空で、instantiateを二回行った各instance内では
  callback / resultが同じfresh `ρ`を共有し、instance間ではfreshenされることを固定する
- exact ref capability `ref [F(P)] P`とcallback row item `F(P)`が同じinvariant payload `P`を
  保つことを固定する
- runtime markerをstructured synthetic familyから直接作るtest seamを用意し、
  `ArgEffectContract(F, depth=1, PreserveMatchingPath)`が存在する一方、marker登録の前後で
  stack fact数、`SubtractId`、type boundsが変わらないことを固定する
- negative controlsとして、(1) v3のexplicit callback stackをrun applicationと併置した形、
  (2) generic unannotated-call `Empty` pairを併置した形がsingle-source条件を満たさないことを
  production panicを起こさないinspectionで固定する
- arity controlとしてpayloadなしownerでも同じsingle-source transportを通し、
  argument-less / payload-bearingをfailure axisに戻さない

ordinary correspondenceの判定はdump上の変数名だけに依存させない。同じ`TypeVar`への正規化、
両方向のordinary subtype connection、またはscheme instantiation provenanceを構造から確認する。

check:

- targeted real-run lowering / compact / generalize / instantiate characterization
- targeted application-subtyping route witness
- targeted non-subtractive runtime-marker witness
- `timeout 180s cargo test -p infer`

LVB-A2のdirect-call primitiveが成立するまでLVB-A3へ進まない。

### LVB-A3: separately-resolved private helper transport characterization（完了、production gate）

このsliceもproduction lowering codeを変更しない。LVB-A2が固定したdirect-call primitiveを、
§4.1 / §4.2のproduction IR形状まで一般化し、LVB-B再開前の必須gateをLVB-A2から
LVB-A3へ置き換える。LVB-A2は成立済みのprimitive characterizationとして残すが、
separate definition boundaryを持たないためproduction十分条件とはしない。

変更:

- LVB-A2と同じpayload-bearing synthetic local-var act copyを作り、そのcopyのreal
  `var_ref` / `run`を通常のdefinition / symbol resolutionで参照するprivate-helper-shapedな
  **別定義**を置く。helper自身のbodyを正確に
  `run init (callback var_ref())` とし、callerへ展開しない
- witness初版はhelper bodyの記述に`my $x` sugarを使っていたため、LVB-B後にはhelper構築が
  general local-var loweringへ自己参照する欠陥があった。これを訂正し、`with_ref`と二つの
  callerを`var_ref` / `run`と同じsynthetic companionの`CopiedSourceInternal` memberとして
  直接lowerする。synthetic copyを起動するtop-level triggerだけをhelper定義から分離し、
  helper自身は`my $x`も別のsynthetic local-var act copyも持たない
- helperのcallerは`run` / `var_ref`を直接書かず、通常のresolved definition refとして
  helperをresolve / instantiateし、`init`、`callback`の順にapplyする
- helper自身をgeneralizeしたschemeが
  `P -> (ref [F(P)] P -> [F(P); ρ] R) -> [ρ] R`の構造を持つことを固定する
- helper callbackの`ret_eff`はapplication chainだけから制約され、explicit
  `Neg::Stack` / family-bearing push / generic unannotated-callの`Empty` pairを持たないことを
  pre-compact graphとresolved application traceで固定する
- helper自身とcallerそれぞれのgeneralization boundaryで`stack_quantifiers`が空であり、
  callback row tailとhelper / caller resultが同じordinary `ρ`を共有することを固定する
- helper definition内のreal `run` applicationだけがsubtraction ownerであり、helper resolve /
  instantiateとcaller applicationを越えてduplicate `SubtractId` ownershipが生じないことを
  固定する
- 同じresolved helper definitionを二つの別call siteからapplyするcontrolを置く。各caller内では
  payload `P`とresidual `ρ`が正しく共有され、helper schemeおよび他方のcallerとはfreshenされる
  ことを構造で固定する
- 本sliceの成立を受け、§7.2のproduction gateをLVB-A3へ更新する

check:

- targeted separate-helper definition generalize / resolve / instantiate characterization
- targeted helper-internal real-run二段application trace
- targeted two-call-site freshening control
- full `local_var_effect_boundary_characterization` test suite

characterization
`separately_resolved_helper_preserves_single_source_transport_across_two_call_sites`は成立した。
上記の自己参照を除いたcorrected witnessでも同じ結果となり、helper内bodyは二つのlocal-var
`Block`を介さないflatな`run init (callback var_ref())`として固定された。
helper自身のschemeと二つのcaller schemeはいずれもtarget構造と空の`stack_quantifiers`を持ち、
callback / resultのordinary `ρ`を共有した。helper内callback callのreturn effectはbare
variableから始まり、pre-compact graphにhelper-owned family stack sourceはなかった。二つの
callerは同じresolved helper `DefId`を二段applyし、各schemeの`P` / `ρ`はhelperおよび他方の
callerからfreshenされた。check listとproduction gateの結論は変わらず、LVB-A3をLVB-Bの
production gateとする。

### LVB-A4: concrete callback application and enclosing generalization characterization

このsliceもproduction lowering codeを変更しない。LVB-A3が証明したseparate helper definitionの
producer-side schemeを、concrete callback applicationとそのcaller自身のgeneralizationまで
追跡する。LVB-A3と合わせて、LVB-B再開前のcorrected production gateとする。

変更:

- LVB-A3のcorrected witnessと同じく、payload-bearing synthetic local-var act copyの
  `var_ref` / `run` / `with_ref`を`CopiedSourceInternal` memberとしてprimitive layerで直接作る。
  helper自身に`my $x` sugarや別のsynthetic local-var act copyを含めない
- bare applicationではなく、通常のdefinition boundaryを持つenclosing functionを作る。
  enclosing bodyはresolved `with_ref`へ`init`とconcrete callback lambdaを順にapplyし、
  enclosing definition自身を通常のlowering / generalize / finalize経路へ通す
- callbackはopaqueなgeneric parameterをforwardしない。受け取ったrefの`get`相当と
  `update_effect`相当を実際に呼ぶnon-trivial bodyを持ち、その操作結果からordinary result
  valueを作る
- helper自身やapplication直後のlocal typeだけでなく、enclosing definitionのfinalized schemeを
  検査する。`stack_quantifiers`が空で、local familyのconcrete row item `F(P)`がschemeの
  effect structureのどこにも残らず、callback内のlocal operation以外のordinary residual
  effectだけが正しい形で残ることを固定する
- 可能なら、外側のlocal familyを扱うcallback bodyが、concrete callbackと固有のlocal familyを
  持つ第二のgeneralized functionを呼ぶnested-boundary controlも置く。元の症状の
  `run` / `text_with_mock`形状に対応し、enclosing schemeから内外両方のlocal familyが消える
  ことを固定する
- 本sliceが成立した場合、LVB-A3とLVB-A4を合わせてLVB-Bのcorrected production gateとする。
  反証された場合は「helper schemeは正しいがconcrete callerがfamilyをdischargeできない」
  deeper mechanism gapとして記録し、追加設計なしにLVB-Bを再開しない

check:

- targeted concrete-callback `get` / `update_effect` application characterization
- targeted enclosing-definition generalize / finalize characterization
- targeted finalized-scheme family absence and ordinary residual-effect shape
- possible nested two-boundary enclosing-generalization characterization
- full `local_var_effect_boundary_characterization` test suite

characterization
`concrete_callback_application_discharge_reaches_enclosing_generalized_scheme`は成立した。
corrected LVB-A3と同じprimitive-layer synthetic act copyに`with_ref`とenclosing definitionを
置き、enclosing bodyからresolved helperへinitとconcrete callback lambdaを二段applyした。
callbackはrefの`get`と`update`を実際に使い、local operationとは別のordinary `observe(P)` effectを
発生させた。enclosing definitionのfinalized schemeは`P -> [observe(P)] P`となり、
`stack_quantifiers`は空、local family `F(P)`はeffect structureへ残らなかった。

`nested_concrete_callback_boundaries_discharge_both_families_from_outer_scheme`も成立した。
外側callbackが自分のrefをread / updateした後、別のlocal familyを同じprimitive helper mechanismで
処理するgeneralized inner functionを呼ぶ。inner / outer definitionのfinalized schemeはいずれも
ordinary `observe(P)`だけを残し、異なる二つのlocal familyは外側schemeへ漏れなかった。これは元の
症状の`run`から`text_with_mock`を呼ぶ二境界形状をcharacterization layerで直接固定する。

したがって、10回目で不足していた「concrete callback application後のenclosing generalization」
は当時のv4 helper mechanismで成立した。ただし22回目により、このcharacterizationは
callback body lowering前のconcrete ref接続が安全だとは示していなかったことが判明した。
LVB-A3 / LVB-A4はhelper schemeとapplication transportのcharacterizationとして保持し、
production lifecycleのgateにはdeferred-reference対照も加える。

### LVB-B: private helper と全 local-var lowering path

変更:

- synthetic var act copyへ compiler-private callback-form helperを追加し、通常の
  definition / symbol resolution経路で参照する
- helper callback parameterのreturn effectはordinary fresh slotとし、explicit `F(P)` stack
  contractを置かない
- helper内ではreal `run` definitionを通常どおりresolve / instantiateし、
  `run init (callback var_ref())`のapplication constraintからfinal helper schemeをderiveする
- compiler-owned callback callをgeneric unannotated-call `Empty` pairへ流さない
- callbackのruntime `ArgEffectContract` markerはstructured synthetic familyから
  non-subtractive certificateとして登録し、type annotation lowererを通さない
- `wrap_var_binding_run(..., body: Computation)` をprepare / finish lifecycleへ置き換える。
  prepareはcallback parameterをordinary fresh type variableのpure `Def::Arg`としてscopeへ
  入れるだけで、exact `ref [F(P)] P`をpre-bindしない
- finishはblock aggregateを`Fun.ret_eff`に持つexact-pure callback valueを作り、resolved
  helperへinit / callbackの順で`make_internal_app`する。二段目applicationのordinary
  subtypingだけがfresh parameterをhelper schemeのconcrete ref shapeへ接続する
- `local_var_effect_value` の exact `[F(P)]` construction は維持し、ambient tailを追加しない
- standalone reference `Let` schemeを作らず、callbackの pure `Def::Arg` localを使う
- ordinary block、var pattern、lambda、case、catch、protocol / do の全 call siteを
  同じ helperへ切り替える
- runtime expressionが必ず helper 内で
  `run init (callback var_ref())` を評価することを固定する
- callback runtime markerがsynthetic familyだけをhandlerへ見せ、型solverへstack sourceを
  追加しないことを固定する
- 22回目の8地点比較をregression contractとして残し、複数文callback bodyでも二段目
  application resultとenclosing finalized schemeにlocal familyが残らないことを固定する
- bug note の最小 repro を regression testに追加する

check:

- ordinary read / update、single / nested / pattern local-var lowering tests
- callback hygiene、shallow/deep handler、continuation resume controls
- intermediate functionを介する最小 reproの check / specialize / run
- `timeout 180s cargo test -p infer`
- `timeout 180s cargo test -p specialize`
- 対象 yulang runtime cases

### LVB-C: contract 反転と closeout

変更:

- `file_mock_text_with_rollback_on_error` を known-gap failure から正しい success contractへ戻す
- `expect_success = false` と current conflict stderrを外し、次を復元する

```text
run roots [(result::err(edit_err::abort), "start")]
```

- ordinary local-var controls、nested local state、function commit、protocol / pattern formsを
  regression corpusとして明示する
- parameterized familyの既存 acceptance witnessを変更なしで通す

check:

- `parameterized_effect_items_keep_row_tail_residuals_and_payload_invariance`
- `file_mock_text_with_rollback_on_error`
- `file_mock_text_with_function_commit`
- `file_text_with_nested_state_var`
- lowering の dollar / var-pattern test 群
- `timeout 240s cargo test -p yulang`
- `timeout 300s cargo test --workspace`
- repository の release gate 相当 command

## 7. stop / rollback conditions

### 7.1 stop conditions

次のいずれかが判明した時点で semantic slice を止め、design reviewへ戻す。

1. real `run` schemeのinstantiate＋applicationだけでは、payload-bearing `F(P)` がcallback
   parameterのnegative `ret_eff`へindependent concrete row prefixとして届かない。
2. callback `ret_eff` の tailと helper result effectが、generalize / instantiate後に同じ
   ordinary `ρ` を共有しない、または別々のrun instanceに由来する。
3. contract成立のために ref effect argumentを `[F(P); ρ]` へ広げる必要がある。
4. contract成立のために nominal constructor variance、stack liveness、
   `compact_neu_id` の global ruleを変更する必要がある。
5. non-empty `stack_quantifiers`、使用済み raw `SubtractId` の scheme内生存、または
   callback schemeと result schemeの間での ID共有が必要になる。
6. 同じ ID に `Empty` と `Set(F, [P])` が現れる。この場合
   `merge_same_id_family` を緩めず、helper-local sourceが残っていると判断する。
7. helper callback `ret_eff`、callback call、helper outputのいずれかに、existing `run`
   instance由来ではないfamily-bearing stackまたはgeneric `Empty` stack pairが現れる。
8. callback runtime markerを付けるためにtype-level `F(P)` annotation、stack fact、
   `SubtractId`の生成が必要になる。
9. callback contract metadataでsynthetic `F`だけをlocal handlerへ見せられず、ambient `ρ`
   またはunrelated callback-origin effectまで捕捉される。
10. callback bodyが `run` の外で先に評価される、shallow/deep delimiterが一段増減する、
   continuation resumeの handler visibilityが変わる。
11. escaping ref、nested local vars、pattern local varsの lexical scopeまたは handler nestingが
   従来と一致しない。
12. callback helperが specializationで消えず、local mutationの hot pathへ avoidable な
    per-scope closure allocationまたは有意な回帰を加える。
13. Aを成立させるにはexisting `run`を置き換えるか新しいcomputation-polarity IRが必要だと
    判明する。この場合C / Dを既定路線にせず、blast radiusを受け入れるかユーザ判断を求める
    別設計へ止める。
14. `650fec0b` の classification、subtype matrix、specialize候補比較を緩めなければ testが
    通らない。
15. ordinary `my $x` controlの型、runtime output、handler rollback semanticsが変わる。

### 7.2 rollback unit

- LVB-Aはprimitive characterizationとして保持するが、それだけを根拠にproduction wiringを
  再開しない。LVB-A2が成立してもLVB-A3が成立しなければLVB-Bを始めない。
- LVB-A3でseparate helper definitionを越えるsingle-source routeが成立しなければ、explicit
  callback contractまたはtwo-ID案を試さず、design reviewへ戻す。
- LVB-B の一経路で stop conditionに当たった場合、旧方式と新方式を syntaxごとに混在させず、
  LVB-B 全体を戻す。
- LVB-C の full gateで unrelated failureが出た場合、正しい success expectationを再び
  wrong failureへ書き換えず、LVB-B を原因単位で戻す。
- performance gateだけが不合格なら semantic contractと runtime representationを混ぜて
  partial landingせず、runtime-free callback representationまたは新 IR の design reviewへ戻る。

## 8. completion contract

本 project は次をすべて満たしたときだけ完了する。

1. bug note の original reproが `SpecializeError::ConflictingTypeCandidates` を出さず、
   `run roots [(result::err(edit_err::abort), "start")]` を返す。
2. `file_mock_text_with_rollback_on_error` が known-gap ではなく success contractになる。
3. private helperの final schemeが構造上
   `(ref [F(P)] P -> [F(P); ρ] R) -> [ρ] R` の対応を持つ。
4. その対応がhelper-owned explicit callback annotationではなく、real `run` schemeの
   instantiationと二段applicationから導かれたことをLVB-A2の構造traceで示す。
5. local ref effectは exact `[F(P)]` のままで、ambient `ρ` を含まない。
6. callback argument側の `F(P)` は independent concrete row itemであり、pathと payloadを
   保つ。callback tailと helper resultは同じ ordinary quantifier `ρ` を共有する。
7. final schemeの `stack_quantifiers` は空で、instantiate後も instance内の `ρ` correspondence
   と payload invarianceが保たれる。
8. helper callback `ret_eff`とcallback callにhelper-owned `Set(F, [P])`も`Empty`もなく、
   existing `run`以外のsubtraction sourceがない。
9. standalone local ref schemeと handler result boundaryの間で `SubtractId` を共有しない。
10. callback runtime markerはsynthetic `F`だけをlocal handlerへ見せ、ambient residualと
    unrelated callback-origin effectを捕捉しない。marker登録はstack fact、`SubtractId`、
    type boundを増やさない。
11. callback bodyは既存 `run` の handled computation内でだけ評価される。
12. ordinary direct read / write、function commit、nested local state、tuple / lambda / case /
    catch / protocol patternの local-var controlsが通る。
13. local callback parameterはbody lowering中ordinary fresh placeholderのままであり、
    resolved helperへの二段目applicationだけがconcrete ref structureへ接続する。multiple
    local varsのprepare / finish順序とruntime handler nestingは従来と一致する。
14. `parameterized_effect_items_keep_row_tail_residuals_and_payload_invariance` が変更なしで通り、
    `650fec0b` の effect-family acceptanceが維持される。
15. `step_subtype` / `process_subtype` の matrix testと subtype-fallthrough closureの contractが
    変更なしで通る。
16. constructor variance、stack liveness、`StackWeight::push_pops`、
    generalize / instantiateの global ruleに local-var patchがない。
17. `merge_same_id_family`のone-ID-one-family invariantを緩めず、directed weight invariant
    violation、new fallback、fixture / path special caseがない。
18. private callback carrierが handler visibilityと performance gateを満たす。
19. implementation diffが local-var boundary、private synthetic helper、その testsに限られ、
    無関係な refactorを含まない。

---
著者: Claude (Sol xhigh, via Codex MCP, supervised by Claude Sonnet 5)
状態: 未承認・ユーザレビュー待ち（改訂あり）
