# local mutable state の effect boundary 修正設計

日付: 2026-07-28

状態: **未承認・ユーザレビュー待ち（改訂あり）**。実装認可をリセットする。

調査基準は `fb2fbbea`。既知の症状、根因、二つの失敗案は
`notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md` を正本とし、本書では
再掲しない。

## 改訂履歴

### 2026-07-28: LVB-A 調査による semantic model の訂正

承認済みだった初版は、act method の push / pop が raw `SubtractId` のまま
generalization を越え、stack binder として一単位で alpha-renaming される、と説明していた。
未コミットの LVB-A characterization と production act-method の直接 trace により、この説明は
誤りだと判明した。

実際には、body が receiver を使うことで同じ effect type variable が argument side から
return side へ流れ、その chain 上で `push.union(pop)` が compact 中に合成される。
`StackWeight::push_pops` は push を pop で相殺し、使用済み `SubtractId` は scheme から消える。
最終 scheme の `stack_quantifiers: []` は act method の正常形であり、対応を運ぶのは通常の
type quantifier である。

初版 LVB-A は、effect-bearing ref を `Fun.arg` の data type 内へ置く一方、body effect /
body value を独立に freshen し、ref を実際に使う body constraint を作っていなかった。
したがって三箇所の raw ID が残るという期待は production の成立条件を測っていなかった。
本改訂は §0、§2.1、§3、§6〜§8 をこの調査結果に合わせて訂正し、承認状態を
「未承認・ユーザレビュー待ち（改訂あり）」へ戻す。

## 0. 決定の要約

local mutable state の残りの block を、compiler-generated ref を引数に取る内部 lambda
として lower する。ref の data type に入る `reference_effect` には、lambda body の
lowering 前に `push(Set(local-family, payload))` を持つ inner effect を接続する。同じ
`SubtractId` の `pop` は lambda の `Fun.ret_eff` と `Fun.ret` に置くが、この ID を
generalization 後まで残すことは目的にしない。

概念上、現在の

```text
let &x = var_ref()
run init <rest>
```

を次の scoped carrier へ変える。

```text
run init ((\&x -> <rest>) var_ref())
```

`var_ref()` は値を作るだけの pure computation であり、lambda application 全体は従来の
`run` の第2 computation 引数に置く。したがって local effect を実際に処理する runtime
handler は引き続き synthetic `var.run` が所有する。内部 lambda は新しい handler ではなく、
ref effect の入力側と handled computation の出力側を、一つの ordinary type-variable
correspondence に載せる type carrier である。

local ref は act-method receiver と異なり、`get` / `update_effect` を持つ first-class value
である。したがって内部 lambda では、

```text
Fun.arg     = std::control::var::ref reference_effect payload
Fun.arg_eff = Never
```

とする。ref lookup や `var_ref()` の評価自体は pure のままにし、`$x` の read、
`&x` の update、ref method call が ref type の invariant `reference_effect` argument を
実際の `body.effect` へ流す。

正しい body use があると、return 側の pop は同じ type-variable chain 上の push と compact
中に相殺される。最終 scheme に残すべき不変条件は、raw `SubtractId` ではなく次である。

```text
argument ref effect: [local-family(payload); ρ]
body/result effect:  [ρ]
```

両辺の `ρ` と payload の invariant relation は通常の type variable として共有される。
generalize / instantiate は `ρ` を ordinary polymorphism として freshen し、
`stack_quantifiers` は空でよい。

この設計では次を行わない。

- `Pos` / `Neg` / `Neu` に computation 専用 variant を追加しない
- `Scheme` に第2 predicate や computation pair を追加しない
- generalize / instantiate の binder 規則を変更しない
- 異なる scheme 間で一つの `SubtractId` を共有しない
- `directed_weight` の family invariant を緩めない

## 1. 問題

bug note の repro では、local ref、synthetic `run`、ref を中継する値が別々の
generalization root になり、callback effect

```text
[local-family; ρ]
```

と handler result effect

```text
[ρ]
```

の対応が specialize まで届かない。

post-body の `wrap_var_binding_run` で新しい push を body effect へ足す案は、body lowering
が既に作った lower と同じ slot で合流する。このとき同じ `SubtractId` に
`Subtractability::Empty` と `Subtractability::Set(local-family, payload)` が載り、
`crates/infer/src/constraints/directed_weight.rs` の invariant に違反する。

修正すべきものは solver の候補比較でも family 分類でもない。local ref が body へ入る
極性と、body computation が scope から出る極性を、body lowering より前に一つの構造へ
収める必要がある。

## 2. 調査結果

### 2.1 act method の実際の成立条件（訂正）

`crates/infer/src/lowering/expr/method_body.rs` の act method は次の順で処理する。

1. `receiver_value` / `receiver_effect` を freshen する
2. fresh `SubtractId` と inner effect を作り、inner に
   `Subtractability::Set(owner)` の declared fact を置く
3. `Stack(inner, push(id, Set(owner))) <: receiver_effect` を置く
4. `receiver_effect` を `Fun.arg_eff` に使い、receiver を
   `Def::Arg` + `LocalEffect::Var(receiver_effect)` として local scope へ bind する
5. receiver が scope にある状態で method body を実際に lower する
6. matching `pop(id)` を predicate subtract として `Fun.ret_eff` / `Fun.ret` へ置く
7. 一つの `Pos::Fun` を method value の lower にする

identity-shaped body `our x.flip = x` では、`Def::Arg` の local lookup が scheme
instantiation を挟まず、`body.value == receiver_value` かつ
`body.effect == receiver_effect` になる。一般の body でも、receiver の実使用が通常の
subtype constraint を通じて同じ receiver-side variable chain を body output へ流す。

compact が return 側の `pop` から `receiver_effect` の lower bound を展開すると、
`compact_lower_bounds` は lower-bound weight を outer weight より先に
`left_weight.union(outer_weight)` で合成する。したがって同じ chain 上で

```text
push(id, Set(owner)).union(pop(id))
```

となり、`StackWeight::push_pops` が active push を取り除く。これは
`collect_composes_lower_bound_weight_before_outer_weight` が固定している合成順序である。

相殺後に active push は残らない。`collect_live_stack_ids_in_type` が covariant position で
live とみなすのは `entry.stack` が non-empty の ID だけであり、pop-only entry は
`cleanup_stack_weights_in_root_and_roles` で除かれる。よって production act-method の
final scheme が `stack_quantifiers: []` になるのは正常である。`instantiate` も stack-level
freshening を行わない。freshen される必要がある correspondence は、argument effect と
body/result effect に現れる通常の type variable が運ぶ。

初版が述べた「同じ `Fun` に push / pop があるため stack binder が一単位で生存する」は
因果を取り違えていた。同じ `Fun` に置くことは compact が一つの root から両側を見られる
構造を作るが、正しさを決めるのは body が receiver を本当に使い、push を持つ effect
variable 自体が return-side pop の下へ流れることである。body が receiver を使わず、
return slot を独立 fresh にしたなら、この correspondence は存在せず、保存されないのが
正しい。

未コミットの LVB-A はさらに二点で production と異なる。

- act method は receiver effect を `Fun.arg_eff` に置くが、LVB-A は effect-bearing ref
  value を `Fun.arg` の data type 内に置いた
- LVB-A の `body_effect` / `body_value` は ref-side variable から独立しており、body が
  ref を使う constraint がなかった

第一の差は local ref 固有の意味論として §3 で解決する必要がある。第二の差は単なる
characterization error であり、raw `SubtractId` の生存を期待する根拠にはならない。

### 2.2 `Computation` は永続する polarity structure ではない

`crates/infer/src/typing.rs` の `Computation` は expression lowering 中だけの
`(expr, value, effect, evaluation)` である。型 node でも scheme root でもない。

関連する既存構造も今回の carrier にはならない。

- `AnnComputationTarget` / `AnnComputationConnection` は annotation lowering の API であり、
  subtract weight を `FunctionPredicateFrame` へ返す。永続化されるのは最終的に
  `Fun.ret_eff` / `Fun.ret` へ入った場合である。
- `EffectViewId` / `LocalEffect::Stack` は local name を `catch` の scrutinee として読む
  ときの一時 view であり、scheme に freeze / instantiate されない。
- `Pos::Stack` / `Neg::Stack` / `Pos::NonSubtract` は weight wrapper である。bare な
  `(value, effect)` pair に入力の負極性を新設する container ではない。
- `notes/design/handler-row-subtraction.md` の `HandlerMatchEdge` は未実装の設計案であり、
  現行 code に再利用できる construct はない。
- constraint provenance / subtype explanation の boundary ID は説明の identity である。
  semantic な `SubtractId` の寿命を運ぶものではない。

### 2.3 directed weight invariant は維持する

`LeftStackWeightEntry` は一つの `SubtractId` について次だけを持つ。

```text
(leading_pops, one family, push count)
```

同じ ID の `take(H); pop` を相殺し、残った active push の family から row split の
`Common(L)` を計算するため、同じ ID に複数 family を載せる表現力はない。
`merge_same_id_family` の equality assertion を緩めて一方を選ぶと、subtraction の対象が
constraint の到達順に依存する。intersection に変えると、一つの static boundary の replay
と、異なる boundary の誤合流を区別できない。

したがってこの assertion は単なる実装制限ではない。同じ ID は同じ static boundary と
family を表す、という directed normal form の意味論上の invariant である。attempt 2 の
`Empty` / `Set` 衝突は invariant が厳しすぎる証拠ではなく、post-body retrofit が二つの
boundary を同じ ID に重ねた証拠である。

## 3. 選んだ設計: scoped ref lambda

### 3.1 boundary の形

一つの local var scope につき、lowering-only の `LocalVarScopeBoundary` を作る。
概念上、次の情報を持つ。

```text
LocalVarScopeBoundary {
    subtract,
    family,
    reference_inner_effect,
    reference_effect,
    reference_value,
    reference_pattern,
    reference_expr,
    locals_start,
}
```

実際の field 名と分割は実装時に既存 module の責務へ合わせてよい。ただし次の lifecycle は
変えない。

#### prepare（body lowering 前）

1. synthetic act path と payload の invariant argument から
   `Subtractability::Set(path, [payload])` を作る
2. fresh `SubtractId`、inner effect、public reference effect を作る
3. act method と同じ向きで
   `Stack(inner, push(id, family)) <: reference_effect` を置く
4. `var_ref()` の value を
   `std::control::var::ref reference_effect payload` へ接続する
5. `&x` を `Def::Arg` の value parameter として bind する。bare lookup は pure なので
   `LocalEffect::Var(reference_effect)` は付けない
6. この parameter が local scope に存在する状態で `<rest>` を lower し、`$x` の
   `get`、`&x` の `update_effect` / `RefSet`、その他 ref method が ref type の
   `reference_effect` argument を body computation へ流す

`local_var_effect_value` が行っている synthetic family / operation 登録と payload invariant
connection は残す。ただし boundary 用 effect を返せる形へ責務を分け、同じ ref value に
独立な effect slot を繰り返し作らない。

#### finish（body lowering 後）

1. body effect と body value を正側 node にする
2. matching `StackWeight::pop(id)` で両方を `Pos::NonSubtract` に包む
3. `std::control::var::ref reference_effect payload` へ接続された parameter value を
   `Fun.arg`、`Neg::Bot` を `Fun.arg_eff`、wrapped body slots を
   `Fun.ret_eff` / `Fun.ret` にした内部 lambda を作る
4. prepare 済みの `var_ref()` をその lambda へ internal application する
5. 現行どおり `run init <scoped-lambda-application>` を作る
6. local parameter scope を終了する

push と二つの pop は generalization 前の同じ内部 `Fun` construction に属する。ただし
correctness witness は ID の生存ではない。body が ref を実際に使うと、
`reference_effect` から body output までの ordinary constraint chain 上で push と pop が
相殺され、`reference_inner_effect` に対応する残差 `ρ` が argument ref effect と
body/result effect の両方に残る。local ref 自身を `Def::Let` として別に generalize
しないため、attempt 1 の scheme 間 transport も不要になる。

### 3.2 `Fun.arg` と `Fun.arg_eff` の配置

local ref carrier は act method の field assignment をそのまま複製しない。

act-method receiver は value type の外にある computation effect を
`LocalEffect::Var(receiver_effect)` と `Fun.arg_eff` で表す。identity body が receiver
name を読むだけで、その同じ effect variable が body effect になる。

一方、`std::control::var::ref 'e 'a` は `get` と `update_effect` を持つ first-class
value である。`lib/std/control/var.yu` では、

```text
get:           () -> ['e] 'a
update_effect: () -> [ref_update 'a; 'e] ()
```

となり、`make_ref_set` も ref value の invariant effect argument を result effect へ
接続する。したがって local-var の `reference_effect` は
`std::control::var::ref reference_effect payload` の data argument として
`Fun.arg` に置く必要がある。`var_ref()` の construction と `&x` の bare lookup は pure
なので、`Fun.arg_eff` は `Neg::Bot` のままにする。

`reference_effect` を `Fun.arg_eff` にも置いたり、`&x` を
`LocalEffect::Var(reference_effect)` として bind したりすると、ref を渡すだけの program
にも local operation effect を課し、method が data argument から effect を取り出す
既存 semantics と二重になる。この案は採らない。

正しい flow は次である。

```text
Fun.arg の ref effect argument
    -> body 内の get / update_effect / RefSet
    -> body.effect の ordinary subtype chain
    -> Fun.ret_eff の pop
```

body が ref を使わなければこの chain は作られず、argument-side `ρ` と result-side effect
に correspondence が残らない。それは ref operation を実行していない program の正しい
結果であり、boundary failure ではない。

### 3.3 effect を処理する場所は変えない

内部 lambda の push/pop は effect family を実行時に処理する handler ではない。
実際の `catch` と state threading は引き続き `lib/std/control/var.yu` から作られた
synthetic act copy の `run` が行う。

従来の第2引数 `<rest>` が、内部 lambda applicationへ置き換わるだけである。

```text
before: run init <rest>
after:  run init ((\&x -> <rest>) var_ref())
```

`var_ref()` が pure であることと、lambda application 全体が `run` の computation 引数の
内側に残ることを implementation test で固定する。lambda application を `run` の外で先に
評価する rewrite は禁止する。

### 3.4 複数 binding の順序

pattern が複数の local var を導入する場合、現在の handler nesting を維持する。
`run_inputs = [a, b]` なら概念上の形は次である。

```text
run_a init_a (
    (\&a ->
        run_b init_b (
            (\&b -> body) ref_b
        )
    ) ref_a
)
```

prepare は source order で local parameter を scope に入れ、finish は逆順に閉じる。
`ActiveVarPatternBindings` は reference statements と post-body run inputs の組ではなく、
prepare 済み scope boundary の stack を持つ形へ変える。

### 3.5 対象となる lowering path

同じ sugar を別経路だけ旧方式で残さない。少なくとも次を同じ helper に通す。

- ordinary block の `my $x = ...`
- tuple / record 等の var pattern binding
- lambda parameter の `$x`
- case value pattern の `$x`
- catch value / effect payload / continuation pattern の `$x`
- protocol lambda / protocol do continuation が作る local ref
- nested / multiple local var scopes

親 module には prepare / lower body / finish の順序が読める orchestration を残し、構文別
call site が独自に push/pop を組み立てない。

### 3.6 lowering API の変更

`wrap_var_binding_run(..., body: Computation)` のように、既に lower 済みの body だけを受け取る
API では正しい順序を表せない。これを概念上、次の二段階へ分ける。

```text
boundary = prepare_var_binding_scope(act, reference_name, payload)
body = lower_body_with_reference_parameter_in_scope(...)
result = finish_var_binding_scope(boundary, init_name, init_value, body)
```

`prepare_var_binding_scope` は ref expression、`Def::Arg` pattern、reference effect の push を
所有する。`finish_var_binding_scope` は matching pop を持つ lambda、lambda への ref
application、従来の `run init` application を所有する。Rust の closure に `&mut
ExprLowerer` を保持させず、owned な prepared descriptor を返すことで borrow と error cleanup
を局所化する。

`lower_var_ref_constructor` / `constrain_local_ref_value` には、呼び出すたびに独立な effect を
作る経路とは別に、prepare 済み `reference_effect` を接続する入口を持たせる。
`ActiveVarPatternBindings` はこの owned descriptor を複数保持する。途中で body lowering が
失敗した場合も、各 call site は `locals_start` まで truncate し、parameter scope を残さない。

## 4. なぜ新しい Computation polarity node を作らないか

`Pos::ComputationBoundary` のような node を追加すれば、bare computation pair に負極性と
正極性を持たせることはできる。しかし最低でも次を同時に変更する必要がある。

- `poly::types` と全 type walker
- compact collect / merge / simplify / finalize
- generalize / instantiate と stack binder liveness
- interface oracle / alpha equivalence
- compiled typed/cache import
- specialize の type graph
- dump / diagnostics

これは local-var lowering の transport gap に対して広すぎる。さらに local mutable scope は
すでに「ref を scope へ導入して body computation を返す」という関数的な境界を持つ。
既存 `Fun` で ref data argument と body output を同じ generalization root に置き、通常の
type-variable correspondence を表せるため、新しい型構造を正当化する不足はない。

scoped lambda 案が stop condition に当たった場合も、直ちに新 variant を追加しない。
その時点で runtime-free な internal scope IR が必要か、private `var.run` を callback form
へ変えるかを別 design review で決める。

## 5. 変更しないもの

- `650fec0b` の parameterized effect-family classification を revert、限定、迂回しない。
  `Pos::Con(path, args)` は args の有無にかかわらず、登録済み family なら row item である。
- `step_subtype` / `process_subtype` の fixed concrete-head matrix と
  `notes/design/2026-07-28-subtype-fallthrough-closure.md` の決定を変更しない。
- `directed_weight.rs` の「one stack id, one family」invariant を変更しない。
- co-occurrence analysis / polarity elimination に rigid、blocked pair、protected variable set
  を追加しない。
- generalization boundary level、quantifier selection、instantiate の freshening を変更しない。
- act-method / local-var scheme に non-empty `stack_quantifiers` を要求しない。
- local ref の `reference_effect` を `Fun.arg_eff` に複製せず、ref value の invariant data
  argument だけに置く。
- synthetic act path、source path、fixture 名の文字列 special case を inference に追加しない。
- specialize の `ConflictingTypeCandidates` 比較を緩めない。
- current wrong output に合わせて正しい expected result を変更しない。
- public `std::control::var` API と runtime state semantics を変更しない。

## 6. 実装 slicing plan

### LVB-A: boundary characterization と scoped carrier

変更:

- 現在の、effect-bearing ref を `Fun.arg` に置きながら body slots を独立 fresh にした
  hand-built test を、production-shaped characterization へ置き換える
- parameter value は
  `std::control::var::ref reference_effect payload` として `Fun.arg` に置き、
  `Fun.arg_eff` は `Neg::Bot` にする
- parameter を pure な `Def::Arg` として scope に入れ、独立な `body_effect` を直接作らず、
  実際の `$x` read または `&x` update / ref method call を lower して、
  ref type の `reference_effect` が body computation へ流れる constraint を作る
- pre-compact の構造確認では、prepared push と `Fun.ret_eff` / `Fun.ret` の matching pop が
  同じ ID を使うことだけを固定する。これは local construction の balance witness であり、
  scheme での ID 生存 witness ではない
- generalize / finalize 後は `scheme.stack_quantifiers.is_empty()` であり、使用済み ID が
  predicate に残らないことを固定する
- final scheme から、argument ref effect が `[local-family(payload); ρ]`、body/result effect
  が `[ρ]` となり、両方の `ρ` が同じ ordinary quantifier、family payload と ref payload が
  同じ invariant variable であることを構造的に取り出す
- instantiate を少なくとも二回行い、各 instance 内では argument-side / result-side が同じ
  fresh `ρ` を共有し、二つの instance 間では `ρ` が別に freshen されることを固定する。
  raw `SubtractId` の freshening は期待しない
- control として、body が ref を使わず独立 fresh effect を返す construction、または
  argument/result effect を意図的に別 fresh variable にした construction を置く。この
  control では shared-`ρ` witness が得られないことを assert し、正例が variable name や
  単独 quantifier の存在だけで vacuously pass していないことを固定する

ordinary correspondence の判定は dump 上の変数名だけに依存させない。同じ `TypeVar` への
正規化、または両方向の ordinary subtype connection を構造から確認する。この slice では
production call site を切り替えず、corrected semantic contract だけを確認する。

check:

- targeted `crates/infer/src/lowering/tests` unit tests
- targeted generalize / instantiate witness
- `timeout 180s cargo test -p infer`

### LVB-B: 全 local-var lowering path を scoped carrier へ切り替える

変更:

- act-method precedent と同じ push-before-body / pop-on-return の lifecycle を持つ
  `LocalVarScopeBoundary` helper を追加する。ただし effect placement は §3.2 に従い、
  ref type を `Fun.arg`、pure computation を `Fun.arg_eff` に置く
- `local_var_effect_value` の family 登録、effect slot 構築、ref type connection を分け、
  一つの prepared boundary effect を ref parameter に使う
- `lower_local_var_binding` を init、prepare、body lowering、finish の順へ変える
- `install_var_pattern_bindings` / `wrap_var_pattern_bindings` を prepared boundary stack に変える
- protocol lambda / do、lambda pattern、case、catch の既存 call site を同じ lifecycle へ移す
- standalone reference `Let` scheme を作らず、内部 lambda の `Arg` local を使う
- runtime expression が必ず `run init (scoped application)` の nesting になることを固定する
- bug note の最小 repro を regression test に追加する

check:

- ordinary read / update、single / nested / pattern local-var lowering tests
- intermediate function を介する最小 repro の check / specialize / run
- `timeout 180s cargo test -p infer`
- `timeout 180s cargo test -p specialize`
- 対象 yulang runtime cases

### LVB-C: contract 反転と closeout

変更:

- `file_mock_text_with_rollback_on_error` を known-gap failure から正しい success contract へ戻す
- `expect_success = false` と current conflict stderr を外し、次を復元する

```text
run roots [(result::err(edit_err::abort), "start")]
```

- ordinary local-var controls、nested local state、function commit、protocol/pattern forms を
  regression corpus として明示する
- parameterized family の既存 acceptance witness を変更なしで通す

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

次のいずれかが判明した時点で semantic slice を止め、design review へ戻す。

1. ref を実際に read / update する internal lambda で、argument ref effect と
   body/result effect の shared ordinary `ρ` が generalize / instantiate 後に成立しない。
   または ref を使わない broken control でも同じ witness が成立する。
2. 修正に non-empty `stack_quantifiers`、使用済み raw `SubtractId` の scheme 内生存、
   または local ref scheme と handler result scheme の間での ID 共有が必要になる。
3. 同じ ID に `Empty` と `Set(local-family, payload)` が再び現れる。この場合
   `merge_same_id_family` を緩めず、boundary の重複または誤った placement と判断する。
4. internal lambda application が `run` の外で評価され、local operation が handler から
   見えなくなる、または従来見えなかった operation が見える。
5. shallow handler / thunk delimiter の runtime evidence が一段増減し、ordinary local-var
   program の effect capture semantics が変わる。
6. escaping ref、nested local vars、pattern local vars の lexical scope または handler nesting
   が従来と一致しない。
7. internal lambda が既存 specialization で消えず、local mutation の hot path に
   avoidable な per-scope closure allocation または有意な回帰を加える。この場合は
   source helper を場当たり的に inline せず、runtime-free internal scope IR と
   private callback-form `run`
   のどちらを採るかを別設計にする。
8. fix のために generalize / instantiate、co-occurrence、polarity elimination、cache format
   の変更が必要になる。
9. `650fec0b` の classification または subtype matrix を緩めなければ test が通らない。
10. ordinary `my $x` control の型、runtime output、handler rollback semantics が変わる。

### 7.2 rollback unit

rollback は slice 単位とする。

- LVB-A の helper / witness が成立しなければ production wiring を始めない。
- LVB-B の一経路で stop condition に当たった場合、旧方式と新方式を syntax ごとに混在
  させず、LVB-B 全体を戻す。
- LVB-C の full gate で unrelated failure が出た場合、正しい success expectation を再び
  wrong failure に書き換えず、LVB-B を原因単位で戻す。
- performance gate だけが不合格なら semantic fix と runtime representation を混ぜて
  partial landing せず、scoped carrier の representation decision へ戻る。

## 8. completion contract

本 project は次をすべて満たしたときだけ完了する。

1. bug note の original repro が `SpecializeError::ConflictingTypeCandidates` を出さず、
   `run roots [(result::err(edit_err::abort), "start")]` を返す。
2. `file_mock_text_with_rollback_on_error` が known-gap ではなく success contract になる。
3. pre-compact では ref effect の push と scoped lambda の `ret_eff` / `ret` pop が同じ
   local ID を持ち、final scheme ではそれらが相殺・cleanup される。
4. final scheme の `stack_quantifiers` が空で、argument ref effect
   `[local-family(payload); ρ]` と body/result effect `[ρ]` が同じ ordinary quantifier を
   共有する。instantiate 後も instance 内の対応と payload invariance が保たれる。
5. standalone local ref `Let` scheme と result boundary の間で `SubtractId` を共有しない。
6. ordinary direct read / write、function commit、nested local state、tuple / lambda / case /
   catch / protocol pattern の local-var controls が通る。
7. multiple local vars の prepare / finish 順序と runtime handler nesting が従来と一致する。
8. `parameterized_effect_items_keep_row_tail_residuals_and_payload_invariance` が変更なしで通り、
   `650fec0b` の effect-family acceptance が維持される。
9. `step_subtype` / `process_subtype` の matrix test と subtype-fallthrough closure の contract
   が変更なしで通る。
10. directed weight invariant violation、new fallback、fixture/path special case がない。
11. internal scoped carrier が handler visibility と performance gate を満たす。
12. implementation diff が local-var boundary とその tests に限られ、無関係な refactor を
    含まない。

---
著者: Claude (Sol xhigh, via Codex MCP, supervised by Claude Sonnet 5)
状態: 未承認・ユーザレビュー待ち（改訂あり）
