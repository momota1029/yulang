# local mutable state の effect boundary 修正設計

日付: 2026-07-28

状態: **ユーザ承認済み（2026-07-28）**。実装を認可する。

調査基準は `fb2fbbea`。既知の症状、根因、二つの失敗案は
`notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md` を正本とし、本書では
再掲しない。

## 0. 決定の要約

local mutable state の残りの block を、compiler-generated ref を引数に取る内部 lambda
として lower する。ref effect の `push(Set(local-family, payload))` は lambda body の
lowering 前に置き、同じ `SubtractId` の `pop` は lambda の `Fun.ret_eff` と `Fun.ret`
に置く。

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
ref effect の入力側と handled computation の出力側を同じ polarity structure に載せる
type carrier である。

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

### 2.1 act method の成立条件

`crates/infer/src/lowering/expr/method_body.rs` の act method は次の順で処理する。

1. receiver value / effect slot を作る
2. fresh `SubtractId` を作る
3. receiver effect の内側へ `push(Set(owner))` を置く
4. receiver を local parameter として bind する
5. method body を lower する
6. matching `pop` を `Fun.ret_eff` と `Fun.ret` へ置く
7. 一つの `Pos::Fun` を method value の lower にする

push の入力と pop の出力は同じ `Fun` に含まれる。scheme が generalize / instantiate
されても、stack binder はこの一単位の中で alpha-renaming される。

重要なのは、`Pos::Fun` node を作るコード行そのものが body lowering より前にあることでは
ない。push を持つ parameter slot が body lowering 前に local scope へ入り、body lowering
後に同じ `SubtractId` の pop を return polarity へ閉じることである。

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
5. `&x` を `Def::Arg` の local parameter として bind する
6. この parameter が local scope に存在する状態で `<rest>` を lower する

`local_var_effect_value` が行っている synthetic family / operation 登録と payload invariant
connection は残す。ただし boundary 用 effect を返せる形へ責務を分け、同じ ref value に
独立な effect slot を繰り返し作らない。

#### finish（body lowering 後）

1. body effect と body value を正側 node にする
2. matching `StackWeight::pop(id)` で両方を `Pos::NonSubtract` に包む
3. parameter value を `Fun.arg`、pure parameter evaluation を `Fun.arg_eff`、
   wrapped body slots を `Fun.ret_eff` / `Fun.ret` にした内部 lambda を作る
4. prepare 済みの `var_ref()` をその lambda へ internal application する
5. 現行どおり `run init <scoped-lambda-application>` を作る
6. local parameter scope を終了する

push と二つの pop は同じ内部 `Fun` にあり、lambda body の local binding が generalize
されるより前から reference side の boundary が存在する。local ref 自身を `Def::Let`
として generalize しないため、attempt 1 の独立 binder duplication も起きない。

### 3.2 effect を処理する場所は変えない

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

### 3.3 複数 binding の順序

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

### 3.4 対象となる lowering path

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

### 3.5 lowering API の変更

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
既存 `Fun` でその境界を明示できるため、新しい型構造を正当化する不足はない。

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
- synthetic act path、source path、fixture 名の文字列 special case を inference に追加しない。
- specialize の `ConflictingTypeCandidates` 比較を緩めない。
- current wrong output に合わせて正しい expected result を変更しない。
- public `std::control::var` API と runtime state semantics を変更しない。

## 6. 実装 slicing plan

### LVB-A: boundary characterization と scoped carrier

変更:

- production call site を変える前に、既存の constraint primitive だけで scoped `Fun` を
  組む characterization harness を lowering test に置く
- lowering unit test で、同じ `SubtractId` の `Set(local-family, payload)` push が内部
  `Fun.arg` 側から到達でき、matching pop が `Fun.ret_eff` と `Fun.ret` にあることを固定する
- generalize / instantiate 後も三箇所の ID が一緒に alpha-renaming される witness を置く

この slice では production call site を切り替えず、構造 contract だけを確認する。

check:

- targeted `crates/infer/src/lowering/tests` unit tests
- targeted generalize / instantiate witness
- `timeout 180s cargo test -p infer`

### LVB-B: 全 local-var lowering path を scoped carrier へ切り替える

変更:

- act-method precedent と同じ push-before-body / pop-on-return を作る
  `LocalVarScopeBoundary` helper を追加する
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

1. internal lambda の ref-side push と `ret_eff` / `ret` の pop が、一つの `Fun` の
   generalize / instantiate witness として残らない。
2. 修正に local ref scheme と handler result scheme の間で raw `SubtractId` を共有する
   必要が出る。
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
3. ref effect の push と scoped lambda の `ret_eff` / `ret` pop が同じ ID を持ち、
   generalize / instantiate で一単位として freshen される。
4. standalone local ref `Let` scheme と result boundary の間で `SubtractId` を共有しない。
5. ordinary direct read / write、function commit、nested local state、tuple / lambda / case /
   catch / protocol pattern の local-var controls が通る。
6. multiple local vars の prepare / finish 順序と runtime handler nesting が従来と一致する。
7. `parameterized_effect_items_keep_row_tail_residuals_and_payload_invariance` が変更なしで通り、
   `650fec0b` の effect-family acceptance が維持される。
8. `step_subtype` / `process_subtype` の matrix test と subtype-fallthrough closure の contract
   が変更なしで通る。
9. directed weight invariant violation、new fallback、fixture/path special case がない。
10. internal scoped carrier が handler visibility と performance gate を満たす。
11. implementation diff が local-var boundary とその tests に限られ、無関係な refactor を
    含まない。

---
著者: Claude (Sol xhigh, via Codex MCP, supervised by Claude Sonnet 5)
状態: ユーザ承認済み（2026-07-28）
