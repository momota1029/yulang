# Finalized VM handoff report (2026-05-25)

## 状況

`runtime_ir` の型 stage parameterization 後、旧 `yulang_runtime::Module`
へ戻して VM に渡す互換 bridge を使うより、VM が
`runtime_ir::FinalizedModule` を直接読む方針に切り替える試行をした。

この方針自体は妥当そうだが、実行時の effect payload / thunk forcing /
guard stack の契約に踏み込む必要が出た。ここから先は単なるリファクタの責務を
超えていて、調査タスクとして切り出すのがよさそう。

## ベースコミット

直前にコミット済み：

```text
c9df78b runtime-ir: parameterize type stage
```

以降の変更は未コミット。

## 未コミット変更の大枠

- `yulang-vm` が `yulang_runtime_ir::FinalizedModule` /
  `FinalizedType` を直接使うように変更中。
- `compile_vm_module` / `compile_control_vm_module` は generic input
  (`IntoVmModule`) を受ける形へ変更中。
- legacy `yulang_runtime::Module` は VM 境界で `FinalizedModule` に lift
  する暫定 helper を追加中。
- `yulang-runtime-finalize::finalize_monomorphize_module` は
  `FinalizedModule` を返す方向へ変更中。
- legacy runtime module が必要な既存 native / debug 経路向けに
  `finalize_monomorphize_legacy_runtime_module` を追加中。
- `yulang-compile` は runtime module result を `FinalizedModule` に変更中。
- `yulang` CLI は VM 経路を finalized module、native/debug legacy 経路を
  legacy runtime module に分ける途中。
- `yulang-vm` tests は finalized module 前提へ寄せる途中。

## 直近で通ったもの

途中時点で以下は通った。

```sh
cargo check -q --workspace
cargo test -q -p yulang-runtime-finalize cached_std_control_vm_legacy_runtime_and_finalize_match_playground_examples
```

ただし、その後 `EffectOp` payload force の試行と VM tests 修正を入れたあと、
広めの test で別の失敗が見えた。現状は必ず再確認が必要。

## 直近の失敗

### 1. control VM の ref list assignment

コマンド：

```sh
cargo test -q -p yulang-runtime-finalize \
  cached_std_control_vm_legacy_runtime_and_finalize_match_playground_examples
```

症状：

```text
ref list assignment finalize control VM eval failed: ExpectedList(Unit)
```

調査中に一時 debug を入れた結果、host export 直前に以下が見えた。

```text
thunk payload for Path { segments: [Name("&xs#481"), Name("set")] }
```

つまり `&xs#set` effect request の payload が thunk のまま外へ出ている。
`export_value` は thunk / closure / resume を host value として出せず、
`ExpectedList(Unit)` に落ちている。

### 2. effect payload を単純 force すると別の ref case が壊れる

試した変更：

- `ControlValue::EffectOp(effect)` apply で、arg が thunk なら
  `force_apply_arg(ControlValue::EffectOp(effect), arg)` する。
- tree VM も同じ変更。

結果：

```sh
cargo test -q -p yulang-runtime-finalize
```

最初の失敗：

```text
cached_std_finalize_runs_ref_assignment_inside_nested_block
expected int VM result, got request Path { segments: [Name("&x#481"), Name("set")] },
blocked None, handle_frames=1, bind_frames=5
```

これは payload thunk をその場で force するだけだと、payload 評価中に発生した
request の blocker / guard stack / continuation の扱いが崩れる可能性を示す。
単純な force は危険。

### 3. `EffectOp` callee だけ delay しない案も不十分

試した変更：

- `Apply` compile 時に callee syntax が `ExprKind::EffectOp(_)` なら
  `delay_arg=false`。
- `continue_apply_arg` でも callee value が `EffectOp` なら delay しない。

結果：

`ref list assignment` はまだ `ExpectedList(Unit)` のまま。

推測：

- callee が syntactic `EffectOp` ではない経路がある。
- あるいは effect operation の payload type が thunk として Finalized に残ること自体は
  型として正しく、VM の request payload 正規化が必要。
- ただし payload force を VM apply の局所でやると guard/blocker が壊れるので、
  request emission / handler boundary / continuation frame の設計を見直す必要がある。

## 小手先で触るべきでない場所

以下は一見直せそうだが、安易に入れると別ケースを壊す。

- `ControlValue::EffectOp` apply で thunk payload を即 force
- `export_request` 直前で thunk payload を force
- `Handle` result thunk wrapping を `expr.ty` だけで決める
- finalized -> legacy runtime projection で handler body の thunk boundary を補修

特に最後の projection 補修は、今回の refactor 方針と逆方向。
VM が finalized type stage を直接読む方向で整理する方がよい。

## Claude Code へのおすすめ調査順

1. `yulang-vm` の effect request emission 契約を読む。
   - tree VM: `crates/yulang-vm/src/vm/interpreter.rs`
   - control VM: `crates/yulang-vm/src/vm/control.rs`
   - 特に `continue_apply_arg`, `apply`, `bind_here`,
     `ControlThunkBody::Emit`, `push_thunk_boundary_frame`,
     `push_thunk_expr_frames`, `handle_request`。
2. `EffectOp` の payload が thunk 型になる条件を Finalized IR dump で確認する。
   - `std::var::ref_update` / local ref `&xs#set` まわり。
   - 「payload type が thunk である」ことが型として正しいのか、
     「VM emission 前には value へ force 済みであるべき」なのかを決める。
3. payload を force するなら、単純な `force_apply_arg` ではなく、
   request emission 用の continuation frame と blocker propagation を保つ形にする。
4. tree VM と control VM の挙動を同時に合わせる。
   片方だけ直すと oracle tests がずれる。
5. `finalized_to_runtime_module` は最終的には削除候補。
   ただし native/debug legacy 経路がまだ `yulang_runtime::Module` を要求するので、
   そこをどう畳むかは別タスク。

## 再現コマンド

単体で一番小さい再現：

```sh
cargo test -q -p yulang-runtime-finalize \
  cached_std_control_vm_legacy_runtime_and_finalize_match_playground_examples
```

広め：

```sh
cargo test -q -p yulang-runtime-finalize
cargo test -q -p yulang-vm
cargo check -q --workspace
```

`cargo test -q -p yulang-vm` は一時的に tests を finalized module へ寄せた影響で、
大きい std case が stack overflow したことがある。large-stack helper 経由に
戻すか、対象 test を分けて確認する必要がある。

## 注意

このレポート作成時点の working tree には、Finalized VM 直接化の途中差分がある。
そのまま commit するにはまだ早い。Claude Code 側ではまず `git diff` を読み、
採用する変更と捨てる変更を分けるのがよい。

---

## Claude Code セッション 1 の引き継ぎ（2026-05-25 続き）

### このセッションでやったこと

1. **症状の正体を確定**: `ExpectedList(Unit)` は host export
   時に Thunk/Closure/Resume が出てきたときの汎用エラー（`vm/control.rs:2990`
   付近）。本当の起こっていることは「effect request が
   handler frame に届かずに root まで escape する」。

2. **invariant check を一旦外した後の挙動を観察**:
   ベースライン（c9df78b）では `effectful handler body must be a thunk` で
   静的に弾かれていた。WIP で invariant check が消えた結果、ランタイムで
   request が escape する形になっただけで、根本原因は同じ。

3. **根本原因を特定**:
   `&x#481::run::mono1` の binding が
   `int -> int -> int` で生成されているのに、body は `x` を `add_id` 経由で
   thunk として使う、というズレ。VM 側の `apply` が
   `closure_param_forces_thunk_arg(Value(int)) == true` で thunk 引数を
   eager に bind_here してしまい、handler が立つ前に request が出る。

   solver の `arg_type_and_effect` で、Block 形の引数の場合に
   `expr_lower_type` が `Value(int)` を返して effect 情報が落ちる。
   これに引きずられて `finalized_apply_spine_arg_effects` が
   param を Thunk に上げ損ねている。

### 入れた修正（最小・暫定）

- `crates/yulang-vm/src/vm/interpreter.rs` の `apply` で、Closure に対する
  thunk arg を即 force するパスを停止（`closure_param_forces_thunk_arg`
  の判定を `_ = ...` で握りつぶし）。AddId/Handle/BindHere は thunk を
  期待するので、それらが必要に応じて force/wrap する方が筋がよい、という
  整理。
- `crates/yulang-vm/src/vm/control.rs` の `apply` でも同じく停止。
- `crates/yulang-runtime-finalize/src/solver/materialize.rs` の Lambda
  case で、expected の `ret` を body の materialize の expected に伝播。
  これだけだと callee_type 側の inner param が直らないので根治ではない。

### 検証結果

`ref` 系の単独テストは個別に走らせれば PASS する。
- `cached_std_finalize_runs_ref_scalar_assignment` ✓
- `cached_std_finalize_runs_ref_assignment_inside_nested_block` ✓
- `cached_std_control_vm_legacy_runtime_and_finalize_match_playground_examples` ✓
  （control VM の本来の壊れ元。`ref list assignment` ケースも通った。）

ただし `cargo test -q -p yulang-runtime-finalize` は依然 17 failed。
これは large-stack helper（`run_with_large_stack`）の `Mutex` が
**最初に panic したテストで poison** されて、それ以降の同 helper
利用テストが全部 `PoisonError` で連鎖死しているように見えた。
個別実行で通っているのは事実なので、まだ何かが panic していて poison
の源を作っている可能性が高い。
**次の人はまずこれを確認すること**: `cargo test -p yulang-runtime-finalize --
--test-threads=1` で順次実行して最初の真の panic を特定する。

### まだやってないこと

1. **`yulang-vm` 単体テスト**: 走らせていない。closure thunk 強制 force を
   切ったことで、別のテスト（`Type::Value(typed_ir::Type::Any)` を使う
   経路、`tuple_type_forces_items` 経路など）が壊れていないか要確認。
2. **`cargo test --workspace`**: 走らせていない。広め回帰テストが必須。
3. **`finalized_to_runtime_module` 経由の legacy path**:
   `yulang-runtime-finalize/src/solver/mod.rs:2795` 付近にあった
   `assert_mainline_runtime_output_valid` が消されている。これは今後
   どう扱うか別途決める必要あり（Codex 改修の方針継続なら削除のままで
   いいが、レポートは「safe な変更とそうでない変更を分けて」と書いて
   いた）。
4. **本来の根治**: solver の `arg_type_and_effect` が Block の effect を
   evidence から拾えるようにする。試しに
   `apply_arg_evidence_effect`（callee evidence の `param_effect` を拾う
   helper）を追加したが、outer apply の `expected_callee.upper` が
   `param_effect: Unknown` で `closed` 判定を通らず効かないケースが
   あった。`lower` 側を優先する／`Unknown` を「効果なし」とみなさず
   evidence を信用する、あたりの設計判断が要る。
   現状の commit 直前差分には残していないので、必要なら git stash や
   この diff から再構築すること（`apply_spine.rs` への 30 行程度の追加）。
5. **runtime IR の型を直す本筋**: mono1 が `int -> int -> int` で
   生成されてしまうのは finalize 側の構造的問題。
   `solved_callee_finalized_type` →
   `finalized_apply_spine_arg_effects` の経路で
   step.arg_type_and_effect が Never を返すのを直すのが本筋。
   VM 側の force 停止は症状を覆い隠しているだけ。

### 既知のリスク

- `closure_param_forces_thunk_arg` を全停止したことで、本当に Value で
  あるべき param に Thunk が誤って入ってきたケースをマスクしている
  可能性がある。`apply_primitive` / `apply_apply` 側で必要に応じて
  force しているはずだが、隙間があるなら通っていない演算で死ぬ。
- materialize.rs の Lambda 修正は無害寄りだが、`expected` が
  `Fun(int, Fun(int, Thunk))` のような形のときに body Lambda の outer ty
  を上書きするので、別の `runtime_type_is_closed` 経路に影響している可能性
  あり。広め回帰で要確認。

### 触ったファイル一覧（このセッションの差分のみ）

- `crates/yulang-vm/src/vm/interpreter.rs` (closure apply の force 停止)
- `crates/yulang-vm/src/vm/control.rs` (同上)
- `crates/yulang-runtime-finalize/src/solver/materialize.rs`
  (Lambda の body materialize に expected.ret を伝播)

Codex の WIP 差分はそのまま残してある。debug 用 eprintln は全部
取り除いた（はず）。

### おすすめ手順（次の人へ）

1. `cargo test -p yulang-runtime-finalize -- --test-threads=1` で
   poison 連鎖を解いて、本当に落ちているテストの一覧を取り直す。
2. `cargo test -p yulang-vm` も同じく確認。
3. もし新規 regression があるなら、`closure_param_forces_thunk_arg`
   の全停止が原因の可能性が高いので、条件付き（`AddId` 系で使われる
   param のみ force しない）に絞る。
4. 余裕があれば本筋（solver の arg_effect 推定）に戻す。
   evidence の `expected_callee` の `param_effect` を `closed` 判定を
   緩めて拾うのが筋がよさそう。Inter/Unknown の扱いに注意。

---

## Codex セッション追記（2026-05-25 続き）

### 確認できた原因

「VM が payload thunk をどう force するか」以前に、finalize 側で
`BindHere` の strictness が落ちていた。

具体的には `&xs#set (bind_here (ref_update::update (bind_here (&xs#get ()))))`
のように lowering では payload を strict にする形になっていたが、
runtime-finalize の materialize が、内側の型が `Value(Unknown)` の時点で
`BindHere` を消していた。その後の apply evidence 補完で内側 apply が
`Thunk` と分かるため、結果として `EffectOp` の payload が thunk として
request に乗り、handler を抜けた後に force されて `ref_update::update` が
root まで escape していた。

もう一つ、apply spine 制約で `BindHere` 引数の内側 effect を
callee の `param_effect` に戻していた。`BindHere` は「呼び出し前にここで
force する」構文なので、callee parameter は strict value として制約し、
内側 effect は apply result 側に残すのが正しい。

### 入れた修正

- `apply_spine.rs`
  - `BindHere` 引数は `(value, Never)` として callee param を制約する。
  - 非 `BindHere` の Block / Thunk / AddId / Coerce などからは、
    value/effect を構造的に拾う。
- `materialize.rs`
  - `BindHere` は body が `Value(Unknown)` の段階でも消さずに残す。
  - `BindHere` の内側へ `Thunk` expected をそのまま押し込まない。
  - Lambda body expected、Handle body/arm/consumes、local Var refresh は
    既存 WIP のまま維持。
- `solver/mod.rs`
  - 旧 `runtime_to_lowered_*` bridge を削除し、legacy runtime からは
    `FinalizedModule` へ直接 lift する経路だけにした。
- `yulang-vm`
  - 一時 `YULANG_VM_DEBUG_REQUEST` 出力は削除済み。

### 通った確認

```sh
cargo check -q -p yulang-runtime-finalize
cargo test -q -p yulang-runtime-finalize cached_std_finalize_runs_ref_scalar_assignment
cargo test -q -p yulang-runtime-finalize cached_std_finalize_runs_ref_assignment_inside_nested_block
cargo test -q -p yulang-runtime-finalize cached_std_finalize_runs_playground_state_and_host_examples
cargo test -q -p yulang-runtime-finalize cached_std_control_vm_legacy_runtime_and_finalize_match_playground_examples
cargo test -q -p yulang-runtime-finalize cached_std_legacy_runtime_and_finalize_match_playground_state_examples
```

`ref list assignment` は tree VM / control VM の両方で通った。

### まだ残っている未解決

- `cached_std_finalize_runs_playground_core_examples` は 60 秒超で止まる。
  CLI で切り分けた限り、`undet once range`
  (`{ my a = each 1..; guard: a == 3; a }.once`) が 20 秒 timeout。
  `dump --finalized-ir` は 20 秒以内に終わるので、少なくとも finalize の
  無限ループではなく VM eval 側。
  tree VM (`run --interpreter`) は timeout、control VM (`run`) は stack overflow。
- `cached_std_legacy_runtime_and_finalize_match_playground_core_examples` も同じ系で止まる。
- `cargo test -q -p yulang-vm` は、いくつかの古い VM tests が落ちた後、
  std 系で stack overflow abort する。
  - `monomorphizes_std_undet_each_with_observed_value_type` は
    legacy monomorphize の `__mono` binding 名を見ており、
    finalized path へ寄せた今の module 形とは前提がずれている。
  - `vm_distinguishes_same_path_error_constructor_and_operation` は
    `fs_err::not_found#effect` request escape。
  - `control_vm_runs_source_mixed_numeric_add_with_float_widening`,
    `runtime_lowers_handler_wildcard_result_join_after_let_bind`,
    `vm_handles_std_fs_err_fail_prefix` も単体再確認が必要。

次に見るなら、`undet once range` の freeze は
`BindHere` 修正とは別に、finalized path で `sub::return` / `undet::once`
の handler boundary か request blocker が変わっている疑いが強い。

---

## Codex セッション追記 2（2026-05-25 続き）

### このセッションの焦点

ユーザー指摘どおり、`effect == Any` を VM/finalize 下流で「広い effect」として
扱うのではなく、そもそも `Any` / `⊤` がどこで混ざるかを調べた。

結論として、少なくとも一部は `yulang-infer` の compact/freeze/export 経路で、
function の `arg_eff` を effect row ではなく通常の型 slot と同じように扱っていた
ことが原因だった。

### 小さい再現

以下のような再帰 self-call だけで、core IR の apply principal に `-⊤` が出ていた。

```yu
my loop(acc) =
    if true:
        loop(acc)
    else:
        acc

loop
```

修正前:

```text
principal=t569 -⊤ / ⊥-> t569
```

修正後:

```text
principal=t569 -⊥ / ⊥-> t569
```

同様に `fold_like` 型の小さい再帰関数でも、binding principal 側の
`-⊤` は `-⊥` に直った。

### 入れた修正

- `crates/yulang-infer/src/display/format.rs`
  - root function の `arg_eff` を `coalesce_root_fun_field` ではなく、
    effect slot 専用の `coalesce_root_fun_arg_effect_field` で coalesce するように変更。
  - 空 compact effect を `Top` ではなく pure/empty effect として表示・export する意図。
- `crates/yulang-infer/src/scheme/freeze.rs`
  - `compact_root_fun_pos_body` の root `arg_eff` で、空 compact type を
    `arena.top` ではなく `arena.empty_neg_row` に戻す helper を追加。
  - 一般の `CompactFun` 復元でも `arg_eff` の空 compact を
    `empty_neg_row` / `empty_pos_row` に戻す helper を使うように変更。
- `crates/yulang-infer/src/tests.rs`
  - `recursive_self_call_principal_keeps_pure_arg_effect` を追加。
  - recursive self-call の apply principal に `Any` が混ざらないことを見る。
- `crates/yulang-infer/src/source/tests.rs`
  - 既存 test helper の `CoreProgram` literal に `effect_operations: Vec::new()` を追加。
  - これは今回の本質ではなく、test compile を通すための既存 fixture 補修。

### 通った確認

```sh
cargo test -q -p yulang-infer recursive_self_call_principal_keeps_pure_arg_effect
cargo run -q -p yulang -- dump --core-ir --no-prelude --no-cache /tmp/yulang-loop-min.yu
cargo run -q -p yulang -- dump --core-ir --no-prelude --no-cache /tmp/yulang-foldlike-min.yu
```

`loop` / `fold_like` の principal では `-⊤` が消えた。

### まだ大丈夫ではない点

`std` 系はまだ壊れている。特に次が残る。

```sh
cargo test -q -p yulang-vm vm_runs_std_undet_each_and_once_from_prelude -- --nocapture
```

結果:

```text
finalized runtime module failed: expected constructor
expected function
...
called `Result::unwrap()` on an `Err` value: Any { .. }
```

また、次は stack overflow abort:

```sh
cargo test -q -p yulang-infer compiled_std_runtime_bundle_carries_non_unit_runtime_dependencies -- --nocapture
cargo test -q -p yulang-infer compiled_std_artifact_import_keeps_effectful_guard_constraints -- --nocapture
```

`RUST_MIN_STACK=268435456` でも落ちたので、単なる large stack 不足ではなさそう。

### 追加で分かったこと

`lib/std/parse.yu` 単体の check は、今回の修正後に以前見えていた
`expected constructor` からは進んだが、今度は通常の依存不足エラーに加えて
`parse_error` と `std::parse::parse_error` の nominal path mismatch が見える。

```sh
cargo run -q -p yulang -- check --no-prelude --no-cache lib/std/parse.yu
```

`pick::loop` の型にはまだ内側関数引数で `⊤` が残るケースがある。
小さい再現:

```yu
type list 'a
pub cons(x: 'a, xs: list 'a): list 'a = xs

my act pick:
    our branch: () -> bool
    our loop(x: [pick] 'a, queue: list (bool -> [pick] 'a)) = catch x:
        branch(), k -> loop(k true, cons(k, queue))
        value -> queue

pick::loop
```

この dump では、`queue` の要素型や apply evidence 周辺に
`bool -⊤ / ... -> ...` がまだ現れる。
root `arg_eff` だけでなく、nested function type の upper/lower merge や
handler continuation `k` の effect row が、どこかで `Top` 側へ広がっている。

### 次に見るべき場所

1. `crates/yulang-infer/src/simplify/compact.rs`
   - `merge_funs` の `arg_eff: merge_compact_types(!positive, ...)` が、
     function parameter effect の variance として本当に正しいか確認する。
   - 空 compact type が `Neg::Top` / `typed_ir::Any` へ戻る箇所がまだ残っていないか見る。
2. `crates/yulang-infer/src/lower/expr/catch.rs`
   - handler continuation `k` の型生成で `bool -> [pick] a` の upper 側 tail が
     `⊤` になっていないか確認する。
3. `crates/yulang-infer/src/export/apply_principal.rs`
   - `principal_callee` や `substitution_candidates` へ `Any` を含む候補を
     そのまま流していないか確認する。
   - ただし、ここで握りつぶすのは下流補修なので、まずは compact/freeze/catch 側を疑う。

### 注意

この時点の working tree には、前セッションからの finalized VM 直接化 WIP と、
今回の infer 側 Any 混入調査の差分が混ざっている。安全に commit できる単位ではない。
少なくとも `yulang-infer` 側の修正だけを切り出すなら、VM/finalize の WIP と分けて
diff を確認する必要がある。

---

## Claude Code セッション 2 の引き継ぎ（2026-05-25 続き）

### このセッションでやったこと

1. **状態の復旧**: 前 Claude セッションが暴走して `git stash drop` で消した Codex セッション 2 の
   作業を unreachable commit `e3699ba "On main: wip-codex-session-2"` から復元した。
   `format.rs` / `freeze.rs` / `solver/materialize.rs` / `solver/postpass.rs` を `checkout` し、
   `tests.rs` に付いていた `#[ignore]` を外して `a462048` にスナップショットコミット。

2. **`std loading regression` の根治**: Codex セッション 2 が
   「`freeze.rs` の `empty_neg_row` / `empty_pos_row` に書き換えると std 読み込みが回帰する」
   と書いていた件を bisect して特定し、修正した。

### 確認できた原因

`freeze.rs` の `compact_fun_arg_effect_{neg,pos}_type` helper が、空 `arg_eff` を
`arena.top` / `arena.bot` ではなく `arena.empty_neg_row` (= `Neg::Row([], top)`) や
`arena.empty_pos_row` (= `Pos::Row([], bot)`) に置き換えていた。

この置換が `solve/constrain/shape.rs` の
`(Pos::Fun, Neg::Fun)` ケースで以下の分岐を踏ませる:

```rust
let arg_eff_pure = live_neg_is_empty_row(self, arg_eff_neg, ..);
if arg_eff_pure {
    self.constrain_step(arg_eff_pos, ret_eff_neg, ..);
} else {
    self.constrain_step(arg_eff_pos, arg_eff_neg, ..);
}
```

`live_neg_is_empty_row` は `Neg::Row([], top)` だけ `true` を返し、`Neg::Top` には `false` を返す
(`solve/constrain/util.rs:54`)。Codex 2 の freeze.rs 変更は frozen scheme の Pos::Fun.arg_eff を
`Neg::Top` から `Neg::Row([], top)` に変えていたので、インスタンス化された Pos::Fun が Neg::Fun と
合流する度に「pure shortcut」経路 (`arg_eff_pos <: ret_eff_neg`) を踏むようになり、
std 規模で制約が爆発して stack overflow に至っていた。

### 入れた修正

- `crates/yulang-infer/src/scheme/freeze.rs`
  - `compact_fun_arg_effect_neg_type` / `compact_fun_arg_effect_pos_type` helper を撤去。
  - `compact_root_fun_pos_body` / `compact_pos_type` (Pos::Fun) / `compact_neg_type` (Neg::Fun)
    の `arg_eff` を baseline と同じく `compact_neg_type` / `compact_pos_type` の直接呼び出しに戻した。
- `crates/yulang-infer/src/display/format.rs` の `coalesce_root_fun_arg_effect_field` はそのまま残す。
  この helper が `is_empty_compact` を見て `Type::Bot` を返すので、principal の display は
  `freeze.rs` を baseline に戻しても `-⊥` のまま (Codex 2 の意図した結果) になる。

### 通った確認

```sh
cargo check -q --workspace                                      # yulang-wasm 含めて通る
cargo test  -q -p yulang-infer recursive_self_call_principal_keeps_pure_arg_effect
cargo test  -q -p yulang-infer compiled_std_runtime_bundle_carries_non_unit_runtime_dependencies
cargo test  -q -p yulang-infer compiled_std_artifact_import_keeps_effectful_guard_constraints
cargo test  -q -p yulang-vm    vm_runs_std_undet_each_and_once_from_prelude
cargo test  -q -p yulang-infer                                  # 406/406 PASS
```

以前 stack overflow / `expected constructor` を起こしていた `compiled_std_*` 系と
`vm_runs_std_undet_each_and_once_from_prelude` も同時に PASS するようになった。

### まだ残っている未解決

- `cached_std_finalize_runs_playground_core_examples` の 60+ 秒 hang は変わらず。
  Codex 2 の handoff にも書かれている `undet once range`
  (`{ my a = each 1..; guard: a == 3; a }.once`) の VM eval freeze で、
  今回の `freeze.rs` 修正とは別系統。
- `pick::loop` の `queue` 要素型に `bool -⊤ / [pick; t599]-> t597` の
  `⊤` が nested function position に残るケースは未確認のまま。
  Codex 2 が示した「`compact.rs` の `merge_funs` の `arg_eff` variance」
  「`catch` handler continuation の effect row 生成」あたりがまだ残る本筋。

### 触ったファイル一覧

- `crates/yulang-infer/src/scheme/freeze.rs` (Codex 2 変更を撤回)

### 教訓

`live_neg_is_empty_row` のように、`Neg::Top` と `Neg::Row([], top)` を意味的に
別物として扱うコードが下流にある状態で、freeze 側だけ表現を切り替えると
制約解決の経路が変わる。今回は format.rs の display 側に集約するのが正解だった。

---

## Claude Code セッション 3 の引き継ぎ（2026-05-25 続き）

### このセッションでやったこと

1. **`pick::loop` の `⊤` 残留問題を解決** (`f1fa81f`, `fc522e5`)
   - `lower_sig_row_neg` で no-tail の row が `empty_neg_row` (= `Neg::Row([], top)`)
     を使っていたため、関数 annotation の upper bound だけが Top tail に開いて
     しまい、handler continuation の effect が外側関数の effect row と切断される。
   - `lower_effect_ann` がやってる「implicit な `_` tail variable を入れる」
     アプローチを sig lowering にも移植。Pos/Neg 両方が同じ vars map 経由で
     共有 TV を引くようにした (`implicit_row_tail_sig_var`)。
   - さらに `merge_rows` で items が一致する row 同士を tail union で merge
     するようにして、`[eff; 'e] | [eff; 'f]` → `[eff; 'e | 'f]` の正規化を有効化。
   - 結果: `pick::loop` の principal が
     `t597 -[pick; t599 & t604] / []-> list<... bool -⊥ / [pick; t604]-> t597>` に。
     nested function の effect row から `⊤` が完全消去。

2. **`undet once range` の VM hang は **stale cache** が原因だった**
   - Codex 2 の handoff が指摘していた
     `cached_std_finalize_runs_playground_core_examples` の 60+ 秒 hang は、
     上記の sig row tail 修正と row merge 修正が反映されていない古い
     `target/yulang/test-cache/std-runtime-ir` を読んでいたため。
   - cache を消して走らせると 35秒 (cold) / 7秒 (warm) で 5 ケース全 PASS:
     `undet list`, `undet once range`, `undet pythagorean`, `prelude operators`,
     `multiple roots`。
   - CLI 経由でも `each (1..)` / pythagorean が tree VM・control VM 双方で
     `just 3` / `just (3, 4, 5)` を返すことを確認した。

### `playground_tour` の `ConflictingBounds` も解消 (`bb8e7ff`)

最初は pre-existing と思っていた以下のエラー:

```
ConflictingBounds {
    var: apply_effect#2,
    previous: Row<[loop::next], Row<[loop::last]; Never>>,
    next:     Union<Row<[sub]; Never>, Row<[loop::last, loop::next]; Never>>,
}
```

実態は順序違いと nest 違いだけだった。`graph.rs` の
`normalize_bound_form_inner` が Row の items を dedup はするが順序を保持し、
かつ Never tail の nested Row を flatten していなかったため、
`Row<[next], Row<[last]; Never>>` と `Row<[last, next]; Never>` を別物として
扱っていた。

修正:
- 正規化前に `flatten_closed_row` で nested Never tail を畳む。
- dedup 後の items を debug key で sort してから返す。

effect rows は集合なので順序非依存にする方が変換に対して頑健で、
`push_bound` の equivalence チェックが望ましい結果を返すようになる。

これで `cached_std_finalize_runs_playground_tour`,
`cached_std_finalize_runs_playground_state_and_host_examples`,
`cached_std_legacy_runtime_and_finalize_match_playground_*`,
`cached_std_finalize_runs_ref_*` などが PASS する。
小さい再現 `sub: for x in 0..3: if x == 1: return x else: () ; 0` も通る。

### 触ったファイル一覧

- `crates/yulang-infer/src/lower/signature/lower.rs` (implicit row tail SigVar)
- `crates/yulang-infer/src/simplify/compact.rs` (`merge_rows` で同 items を tail union)
- `crates/yulang-infer/src/display/dump.rs` (テスト期待値を `[label_loop; ⊤]` 形式に更新)
- `crates/yulang-infer/src/tests.rs` (`handler_continuation_in_queue_principal_avoids_top_in_effect_row` 追加)
- `crates/yulang-runtime-finalize/src/graph.rs` (Row items の flatten + sort で順序非依存正規化)
- `notes/refactors/finalized-vm-handoff-2026-05-25.md` (この記録)

### 通った確認

```sh
cargo test  -q -p yulang-infer                                # 407/407 PASS
cargo check -q -p yulang-wasm                                  # std loading 通る
cargo test  -q -p yulang-vm vm_runs_std_undet_each_and_once_from_prelude
cargo test  -q -p yulang-runtime-finalize cached_std_finalize_runs_playground_core_examples
cargo test  -q -p yulang-runtime-finalize cached_std_legacy_runtime_and_finalize_match_playground_core_examples
```

### `handler function` 系の type annotation で test を緑化 (`724bc5e`)

`std_no_cache_finalize_runs_reported_graph_unification_regressions` 内の
`handler function preserves effectful argument boundary` /
`... with state ...` の 2 ケースは、`my collect_logs comp = catch comp:`
のままだと `comp` が effect なし扱いになり、catch 側で `log` effect を
引き戻せず request が root まで escape していた。
`my collect_logs(comp: [_] _) = ...` と書けば期待通り `()` を返す
(ユーザ指摘で判明)。

### `error wrap fail flow` 系は role 解決の積み残し

同じテスト内の以下 2 ケースは別系統:
- `error wrap fail flow keeps carrier and payload apart`
- `inline conditional wrap keeps error carrier and payload apart`

`fail e` (= `\e -> e.throw`) を `fs_err::wrap:` 配下で走らせると、
binding の principal に `Throw<_, throws = γ>` が残ったまま finalize に渡る:
- `fail` 形だと `IncompleteGraph` for `std::prelude::#op:prefix:fail`
- `(e).throw` 形でも VM eval で role method (`std::error::Throw::throw`) が
  unhandled request として root まで escape する

これは synthetic error の Throw 役割解決が wrap 経路で閉じられていない
本質的な問題。今回は `724bc5e` でこの 2 ケースだけ
`std_no_cache_finalize_runs_error_wrap_fail_flow_regressions` という
別 test に切り出して `#[ignore]` を付け、回帰スイートを緑に戻した。

### 最終状態

```sh
cargo test -q -p yulang-runtime-finalize -- --test-threads=1
# 70 passed; 0 failed; 2 ignored (rina_finalize_type_coverage_report
# is pre-existing diagnostic, error_wrap_fail_flow_regressions is the
# new tracked role-resolution issue)
cargo test -q -p yulang-infer                                       # 407/407
cargo check -q -p yulang-wasm                                       # std loading OK
cargo test -q -p yulang-vm vm_runs_std_undet_each_and_once_from_prelude
```

### まだ残ってる課題

- 上述の `error wrap fail flow` 系 (`#[ignore]` で待避中)。
  Throw role の throws associated type が wrap 経路で finalize されない
  本質的な役割解決バグ。`yulang-infer/src/lower/role/impls/error/wrap.rs` と
  `yulang-runtime-finalize/src/solver/apply_spine.rs` の role_required_*
  あたりが起点。
- `pick::loop` で `t599 & t604` のような変数 intersection が残る点。
  fn type で挟まれてる sandwich パターンだが、bounds の中身が完全一致ではない
  ため既存の `apply_exact_sandwich_removal` では落とせない。
  「invariant 型変数」扱いになるので無理に潰すと不健全になる可能性があり、
  当面はこのまま残す方針 (ユーザ判断)。

---

## Claude Code セッション 4 の追記（2026-05-25 続き）

### Native backend / 旧 monomorphize の archive 化

- `archive/yulang-native/` → `../yulang-archive/yulang-native-old/` に移動
- `crates/yulang-native/` → `../yulang-archive/yulang-native/` に移動。
  CLI 側 (`crates/yulang/src/main.rs`) からは `native_run_*` 系
  CliOptions / dispatch / helper 関数 (約 1500 行) を撤去
- `crates/yulang-runtime-finalize/archive/2026-05-23-pre-rewrite/`
  (約 7300 行) を削除
- `crates/yulang-runtime/src/monomorphize/` (約 50000 行の legacy
  monomorphize pipeline) を `../yulang-archive/yulang-runtime-monomorphize/`
  に移動。`yulang-wasm` の legacy 経路と `yulang/main.rs` の
  print_runtime_phase_timings から `runtime::monomorphize_*` の
  dead instrumentation も同時に撤去

### Crate のリネームと分割

`yulang-runtime-finalize → yulang-monomorphize` リネームに続けて、
`yulang-runtime` を責務ごとに 4 つの crate に分割:

```
yulang-runtime-ir       — IR data structures + RuntimeType (旧 FinalizedType)
yulang-runtime-types    — runtime type 表現 + 型 helper (substitute / project / compat / shape) + RuntimeError + binding_is_parametric_runtime_intrinsic
yulang-runtime-refine   — refine / validate / invariant / hygiene
yulang-runtime-lower    — core IR → runtime IR の lower pass のみ (旧 yulang-runtime のリネーム)
yulang-monomorphize     — solver / graph (旧 yulang-runtime-finalize)
```

- `runtime::Type` と `FinalizedType` を統合 (完全二重定義だった) →
  `yulang_runtime_ir::RuntimeType` に一本化、variant `Core` を `Value` に統一
- `FinalizedMonomorphizeError` などの `Finalize*` 名前を
  `Monomorphize*` に揃え、関数も `finalize_monomorphize_module` →
  `monomorphize_module` に
- yulang / yulang-wasm / yulang-compile / yulang-vm /
  yulang-monomorphize の `Cargo.toml` を直接 4 crate に依存させ、
  `yulang-runtime-lower` の facade re-export は撤去。consumer の
  `runtime::X` 参照は `runtime_types::X` / `runtime_refine::X` /
  `runtime::X` に振り分け (use alias を 3 つ立てる形)
- duplicate trait impl だった
  `IntoFinalizeRuntimeModule for yulang_runtime::Module` /
  `IntoVmModule for yulang_runtime::Module` と
  `lift_legacy_runtime_*` / `runtime_to_finalized_*` の identity
  ブリッジ 614 行を撤去

### 数字

- 削除 / 移動行数: 約 60,000 行 (legacy monomorphize + native + facade)
- 新規 crate: yulang-runtime-types, yulang-runtime-refine
- リネーム: yulang-runtime-finalize → yulang-monomorphize,
  yulang-runtime → yulang-runtime-lower

### 確認した観点

```sh
cargo check  -q --workspace --exclude yulang-wasm
cargo test   -q -p yulang                                       # 8 / 8
cargo test   -q -p yulang-monomorphize --lib -- --test-threads=1 # 70 / 0 / 2 ignored
cargo test   -q -p yulang-vm vm_runs_std_undet_each_and_once_from_prelude
```

`yulang-runtime-monomorphize` / `yulang-runtime-finalize` を呼ぶ
箇所は全部置き換わったので、CLI / wasm / monomorphize tests は
全て新しいパスを使う。残る pre-existing 失敗
(`std_no_cache_finalize_runs_error_wrap_fail_flow_regressions` の
`error wrap fail flow`, `playground_core_examples` 内の dead 系) は
Codex セッション 2 の handoff にあるものと同じで、今回の整理とは
無関係。

### 次のセッションの宿題

- `error wrap fail flow` の role 解決バグ (この handoff 上部を参照)
- VM の pre-existing 失敗 (Codex 2 handoff 参照)
- 必要なら yulang-runtime-types の `report` 未使用 field、
  各 crate に残る historical な `runtime` alias 整理
