# local mutable state の effect boundary 修正設計

日付: 2026-07-28

状態: **未承認・ユーザレビュー待ち（改訂あり）**

調査基準は `fb2fbbea`。既知の症状と5回の試行・調査は
`notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md` を正本とし、本書では
設計判断に必要な差分だけを扱う。

## 改訂履歴

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
一つの synthetic local-var family を `F`、payload を `P` と書くと、target contract は
次である。

```text
local ref capability:
    ref [F(P)] P

callback:
    ref [F(P)] P -> [F(P); ρ] R

scoped handler result:
    [ρ] R
```

`F(P)` は callback の実際の return effect にある独立した concrete row item である。
`ρ` は callback effect と handler result に現れる同じ ordinary type variable であり、
raw `SubtractId` ではない。local ref の effect argument は、その ref operation が実際に
起こす exact family `[F(P)]` のままとし、body 全体の ambient residual `ρ` を混ぜない。

概念上、現在の

```text
let &x = var_ref()
run init <rest>
```

を次へ変える。

```text
with_ref init (\&x -> <rest>)
```

compiler-private helper の意味は次である。

```text
with_ref init callback =
    run init (callback var_ref())
```

callback application は既存 `run` の handled computation 内で起動する。callback value を
helper へ渡す時点では body を評価しない。`var_ref()` の construction と `&x` の bare lookup
は pure のままであり、runtime state handler は引き続き synthetic `var.run` が所有する。

helper の callback parameter は function type なので、helper の正の function root から見ると
negative position にある。その callback の `ret_eff` は
`compact_neg_effect_id` / `compact_neg_stack_effect` を通り、contravariant concrete
annotation が作った active `Set(F, [P])` を `[F(P); ρ]` という row prefix と tail に変える。
materialize 後は使用済み stack ID が消えてよく、最終 scheme の
`stack_quantifiers` は空でよい。

この設計では次を行わない。

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
実際に handler が受け取る callback computation を function boundary として表し、その
negative-side effect contract と handler result を一つの helper scheme に置く必要がある。

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
prefix materialization は起きない。callback の**実際の return effect slot**へ置くことが
必要である。

既存の compact characterization
`compact_neg_stack_effect_surfaces_concrete_push_as_row_prefix` は、payload のない family で
この性質を固定している。
`negative_filter_stack_effect_projects_set_as_row_prefix` は `Neg::Fun.ret_eff` 経由を固定する。
LVB-A はこの形を payload-bearing synthetic family と shared residual まで拡張する。

## 3. 候補方向の比較

| 方向 | soundness risk | blast radius | production 前 characterization | 判断 |
| --- | --- | --- | --- | --- |
| A. `ref` effect argument を variance-aware pair に分解 | 高い。liveness のための反変 facet が surface semantics にない | 高い。nominal subtyping、compact、liveness、cache へ波及 | pair の polarity trace 自体は可能 | 採らない |
| B. `ref` effect argument へ `[F(P); ρ]` を direct row として埋める | 中〜高。compact は生存するが ref capability と body ambient effect を混同 | 中。local lowering は狭いが全 ref use の inferred effect が変わる | direct `Pos::Row` の生存と過剰 effect を対照化できる | 採らない |
| C. callback-form helper の negative `ret_eff` で `[F(P); ρ]` を表す | 中。既存 callback hygiene と evaluation order の確認が要る | 中。synthetic var helper と local-var lowering が中心 | production 未変更で helper scheme、compact、instantiate を固定できる | **推奨** |
| D. 新しい computation-polarity IR を作る | 意味論は明示できるが実装回帰リスクが高い | 非常に高い。全 type walker、compact、generalize、cache、specialize へ波及 | isolated IR test は可能だが、導入自体が別 project | C が失敗した場合の scope decision |

### 3.1 A: invariance の分解

constructor argument の lower / upper を別の polarity path に置き、outer `Fun.arg` の反変性と
組み合わせて片側を covariantly live にすることは、表現上は可能である。しかし現行
`ref` surface に effect を入力として受け取る operation はない。stack ID を残すためだけの
contravariant occurrence は型の利用可能性を実態より狭め、subtyping の意味を変える。

将来 constructor variance を declaration signature から導出する project はあり得る。
その場合 `'e` はむしろ covariant と判定される可能性が高く、outer callback argument の下では
依然 negative になる。今回の residual transport を解く直接の根拠にはならない。

### 3.2 B: invariant ref argument への direct row

independent `Pos::Row([Con(F, [P]), Var(ρ)])` と対応する negative row を
`Neu::Bounds` へ直接入れれば、`compact_pos_row` は `F(P)` を保持する。この点では
push-only carrier と異なり、v2 の構造的消失を回避できる。

しかし現在の `local_var_effect_value` はすでに exact `[F(P)]` を concrete row として
ref effect argument へ置いている。欠けているのは `F(P)` の存在そのものではなく、
callback ambient `ρ` と handler result `ρ` の対応である。ref argument を
`[F(P); ρ]` に広げると、全 ref method call が ambient `ρ` まで起こす型になり、
correspondence を得る代わりに別の過剰 effect を導入する。この案は採らない。

### 3.3 C: callback-form helper

callback は local ref value を引数に取り、body computation を return effect として持つ。
helper の argument typeにある callback `ret_eff` は negative-side effect slot であり、
contravariant concrete contract `F(P)` を既存規則どおり active push として受け取る。
compact はそれを `[F(P); ρ]` へ materialize し、helper resultには ordinary tail `ρ` を残す。

この形は local ref の exact capabilityを変えない。handler が処理する対象も、実際に
callback が実行する computation effect である。v2 の ref-data carrier ではなく、
handler API が本来扱う computation boundary に責務を戻すため、この案を推奨する。

### 3.4 D: computation-polarity IR

v1 は `Pos::ComputationBoundary` のような新 node を、既存 `Fun` で十分だとして拒否した。
5回目の調査により「invariant ref argument 内の既存 `Fun` で concrete family を運べる」
という根拠は失われた。したがって新 IR を永久に除外する理由はもうない。

ただし、callback-form helper は既存の本物の function / effect polarity を使える。
まず LVB-A でこれを検証する。C が structural contract を作れない、または callback hygiene
上 local handler に family を見せられないと判明した場合は、B や liveness patch へ戻らず
停止する。その時点で新 IR の blast radius を受け入れるか、ユーザの scope decision を
得る別設計へ移る。

## 4. 選んだ設計: compiler-private callback boundary

### 4.1 helper contract

一つの synthetic local-var act copy につき、既存 private `var_ref` / `run` と同じ owner に
compiler-private helper を持たせる。以下では仮に `with_ref` と呼ぶが、実装名は builtin
kind または resolved `DefId` として構造化し、inference 中の文字列 special case にはしない。

概念型は次である。

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

callback parameter の effect contract は `F(P)` を明示し、残りを `ρ` とする。この
contravariant concrete annotation が、negative `ret_eff` の active
`Set(F, [P])` と residual tail を作る。helper result の `ρ` は同じ ordinary type variable
であり、generalize / instantiate の通常経路で freshen される。

helper を public `std::control::var` API にはしない。synthetic act copy の private member、
または同じ型構造を作る compiler-owned resolved definition とする。どちらを選んでも
family path と payload は通常の act-copy substitution / symbol resolution から得て、
path 文字列比較で推論しない。

### 4.2 lowering lifecycle

#### prepare（body lowering 前）

1. synthetic act copy、init binding、payload `P` を確定する
2. existing `var_ref()` の exact value type `ref [F(P)] P` を使う
3. callback の parameter value を同じ ref typeへ接続する
4. `&x` を pure な `Def::Arg` として local scopeへ bind する
5. callback parameter が scope にある状態で `<rest>` を lower する

`Fun.arg_eff` は `Never` のままにする。ref construction と bare lookup は pure であり、
local operation effect は `$x` の `get`、`&x` の `update_effect` / `RefSet`、その他
ref method の実使用から callback body effect へ入る。

#### finish（body lowering 後）

1. callback parameterを `Fun.arg`、pure lookup を `Fun.arg_eff`、body effect / value を
   `Fun.ret_eff` / `Fun.ret` とする lambda value を作る
2. private `with_ref` を init valueへ apply する
3. その結果へ callback lambda **value** を apply する
4. callback body の application は helper 内の既存 `run` computation argumentとして
   評価される
5. callback parameter scopeを終了する

local lowering は ref argument の中へ独自 push / pop を組み立てない。
subtraction contract は private helper の function scheme が所有する。
standalone local ref `Let` scheme と handler result scheme の間で raw ID を共有しない。

### 4.3 v2 scoped lambda との違い

v2 は次を local lowering 内で作った。

```text
run init ((\&x -> body) var_ref())
```

さらに ref effect argument 内へ push を置き、callback body output の pop と相殺して
concrete family が残ると期待した。v3 は lambda applicationを helper 実装の内側へ移すだけの
表面的 rewriteではない。

- family contract は invariant ref argument 内の `Pos::Stack` ではなく、helper parameter の
  callback `Neg::Fun.ret_eff` にある
- concrete prefix は positive push cancellation の副産物ではなく、
  `compact_neg_stack_effect` の定義済み projection で作る
- ref argument は exact `[F(P)]` のままで、ambient `ρ` を持たない
- subtraction と residual correspondence は private helper の一つの scheme に属する
- local lowering は family-bearing `SubtractId` の owner にならない

同じ syntax tree の形に見えても、type evidence の owner と polarity が異なる。

### 4.4 callback hygiene と runtime order

callback-origin effect を内側 handler が捕捉できるかは、単なる path 一致ではなく callback
effect contract に依存する。private helper の callback parameterには `F(P)` を明示し、
この synthetic state handlerだけが family を処理できる contract metadataを持たせる。
ambient `ρ` は同じ contractで local handlerに許可しない。

characterization と implementation test では次を固定する。

- callback value の作成は pure であり、body は helper 呼び出し前に実行されない
- `callback var_ref()` は `run init` の handled computation 内で起動する
- callback contract marker は `F(P)` と payload correspondence を持つ
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
- synthetic act path、source path、function 名の文字列 special case を inference に追加しない。
- specialize の `ConflictingTypeCandidates` 比較を緩めない。
- current wrong output に合わせて正しい expected result を変更しない。
- public `std::control::var` API と runtime state semantics を変更しない。
- LVB-A が失敗した場合、承認なしに新しい computation IR を追加しない。

## 6. 実装 slicing plan

### LVB-A: negative callback boundary characterization

この slice は production lowering code を変更しない。

変更:

- payload-bearing family `F(P)`、exact ref `ref [F(P)] P`、callback ambient tail `ρ` を持つ
  private-helper-shaped constraint witness を作る
- helper の callback parameterを実際の `Neg::Fun` とし、その `ret_eff` に
  contravariant `[F(P); ρ]` contractを置く
- helper result effectを同じ ordinary `ρ` に接続する
- pre-compact では callback `ret_eff` の `Neg::Stack` が active
  `Set(F, [P])` を持ち、family push が ref constructor argument の
  `Neu::Bounds` 内にはないことを固定する
- compact 後は callback `ret_eff` から独立した concrete row prefix `F(P)` と tail `ρ` を
  構造的に取り出し、helper result effectの `ρ` と同じ `TypeVar` correspondenceであることを
  固定する
- generalize / finalize 後は使用済み raw ID が predicate に残らず、
  `scheme.stack_quantifiers.is_empty()` であることを固定する
- instantiate を二回行い、各 instance 内では callback / result が同じ fresh `ρ` を共有し、
  instance 間では別に freshen されること、payload `P` の invariant relationが保たれることを
  固定する
- arity control として payload なし `Set(owner)` でも同じ materialization pathを通ることを
  確認し、argument-less / payload-bearing を failure axis に戻さない
- direct-row control として invariant ref argument 内の exact `[F(P)]` 自体は compactを
  生き残るが、そこへ push-only evidenceを置いても callback/result `ρ` correspondenceは
  作られないことを固定する
- callback parameterの explicit effect contract metadataが `F(P)` を許可し、ambient `ρ` を
  local handlerへ許可しない形を確認する

ordinary correspondence の判定は dump 上の変数名だけに依存させない。同じ `TypeVar` への
正規化、または両方向の ordinary subtype connection を構造から確認する。

check:

- targeted compact / lowering / generalize unit tests
- targeted generalize / instantiate witness
- `timeout 180s cargo test -p infer`

LVB-A が成立するまで production `wrap_var_binding_run` と call siteを変更しない。

### LVB-B: private helper と全 local-var lowering path

変更:

- synthetic var act copyへ compiler-private callback-form helperを追加し、通常の
  definition / symbol resolution経路で参照する
- helper callback parameterの explicit `F(P)` contractと result residual `ρ` を、一つの
  schemeとして generalizeする
- `wrap_var_binding_run(..., body: Computation)` を、callback parameterを先に scopeへ入れられる
  prepare / finish lifecycleへ置き換える
- `local_var_effect_value` の exact `[F(P)]` construction は維持し、ambient tailを追加しない
- standalone reference `Let` schemeを作らず、callbackの pure `Def::Arg` localを使う
- ordinary block、var pattern、lambda、case、catch、protocol / do の全 call siteを
  同じ helperへ切り替える
- runtime expressionが必ず helper 内で
  `run init (callback var_ref())` を評価することを固定する
- callback contract metadata / runtime markerが synthetic familyだけを handlerへ見せることを
  固定する
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

1. payload-bearing `F(P)` が callback parameterの negative `ret_eff` から independent
   concrete row prefixへ materializeされない。
2. callback `ret_eff` の tailと helper result effectが、generalize / instantiate後に同じ
   ordinary `ρ` を共有しない。
3. contract成立のために ref effect argumentを `[F(P); ρ]` へ広げる必要がある。
4. contract成立のために nominal constructor variance、stack liveness、
   `compact_neu_id` の global ruleを変更する必要がある。
5. non-empty `stack_quantifiers`、使用済み raw `SubtractId` の scheme内生存、または
   callback schemeと result schemeの間での ID共有が必要になる。
6. 同じ ID に `Empty` と `Set(F, [P])` が現れる。この場合
   `merge_same_id_family` を緩めず、helper contractの重複と判断する。
7. callback contract metadataで `F(P)` だけを local handlerへ見せられず、ambient `ρ` または
   unrelated callback-origin effectまで捕捉される。
8. callback bodyが `run` の外で先に評価される、shallow/deep delimiterが一段増減する、
   continuation resumeの handler visibilityが変わる。
9. escaping ref、nested local vars、pattern local varsの lexical scopeまたは handler nestingが
   従来と一致しない。
10. callback helperが specializationで消えず、local mutationの hot pathへ avoidable な
    per-scope closure allocationまたは有意な回帰を加える。
11. C を成立させるには新しい computation-polarity IRが必要だと判明する。この場合 v1 の
    rejectionを既定路線にせず、blast radiusを受け入れるかユーザ判断を求める別設計へ止める。
12. `650fec0b` の classification、subtype matrix、specialize候補比較を緩めなければ testが
    通らない。
13. ordinary `my $x` controlの型、runtime output、handler rollback semanticsが変わる。

### 7.2 rollback unit

- LVB-A の witnessが成立しなければ production wiringを始めない。
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
4. local ref effectは exact `[F(P)]` のままで、ambient `ρ` を含まない。
5. callback argument側の `F(P)` は independent concrete row itemであり、pathと payloadを
   保つ。callback tailと helper resultは同じ ordinary quantifier `ρ` を共有する。
6. final schemeの `stack_quantifiers` は空で、instantiate後も instance内の `ρ` correspondence
   と payload invarianceが保たれる。
7. standalone local ref schemeと handler result boundaryの間で `SubtractId` を共有しない。
8. callback effect contract / runtime markerは synthetic `F(P)` だけを local handlerへ見せ、
   ambient residualと unrelated callback-origin effectを捕捉しない。
9. callback bodyは既存 `run` の handled computation内でだけ評価される。
10. ordinary direct read / write、function commit、nested local state、tuple / lambda / case /
    catch / protocol patternの local-var controlsが通る。
11. multiple local varsの prepare / finish順序と runtime handler nestingが従来と一致する。
12. `parameterized_effect_items_keep_row_tail_residuals_and_payload_invariance` が変更なしで通り、
    `650fec0b` の effect-family acceptanceが維持される。
13. `step_subtype` / `process_subtype` の matrix testと subtype-fallthrough closureの contractが
    変更なしで通る。
14. constructor variance、stack liveness、`StackWeight::push_pops`、
    generalize / instantiateの global ruleに local-var patchがない。
15. directed weight invariant violation、new fallback、fixture / path special caseがない。
16. private callback carrierが handler visibilityと performance gateを満たす。
17. implementation diffが local-var boundary、private synthetic helper、その testsに限られ、
    無関係な refactorを含まない。

---
著者: Claude (Sol xhigh, via Codex MCP, supervised by Claude Sonnet 5)
状態: 未承認・ユーザレビュー待ち（改訂あり）
