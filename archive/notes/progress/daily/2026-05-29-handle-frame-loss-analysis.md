# Handle frame loss in parallel resume — analysis 2026-05-29

引き継ぎ元: `2026-05-28-parallel-cache-flake-handoff.md`

## 結論

並列 flake `vm_std_pipeline_survives_parallel_source_ref_runs` の panic は、
VM resume 中に **`run` 関数の再帰呼び出し (`run v: k v` / `run v: k()`) が
新たな `run` の catch まで到達せず、`&s#N::set` を handle する frame が枯渇する**
ことで発生する。

並列でしか起きないのはタイミング敏感な race condition だが、根本は
「特定の eval 経路で Handle frame が積まれない」設計バグの可能性が高い。

## 確実な観察

1. 各 worker の module は **内部完全一貫**: handler arm 名と発火元 effect path が一致
2. `static` / `OnceCell` / `thread_local!` の隠れた共有状態は無い (VM / monomorphize / runtime-pipeline / runtime-lower / infer 各層で確認)
3. 失敗時 panic の frames に **Handle 系 frame が 0 個**
4. flake 率は trace insertion で大きく変動 → race condition 確定
   - trace なし: ~70%
   - buffered trace + panic hook: ~50%
   - 直接 `eprintln!` トレース: 0% (race が消える)
5. `--test-threads=1` や `vm_std_pipeline_survives_repeated_ref_and_effect_runs_on_one_thread` は **常に通る**

## 失敗時の trace パターン (深掘り版)

handle id の正体を分けると:

- `id=1, 3, ...` → `&s#N::run` の handler (arms に `get/set`)
- `id=7, 4, 11, 12, ...` → **`r.update` の loop の handler** (arm に `std::var::ref_update::update` のみ)

失敗時の時系列 (run 4 で `&s#1326::set` の panic 例):

1. handle 1 (run) が `get` を match → arm body 実行
2. arm body 内で `r.update_effect = set(update(get()))` の effect 連鎖が走る
3. handle 7, 4 (r.update) が update を順次 match
4. handle 3 (run) が次の `get` を match
5. handle 4 (r.update) が次の update を match
6. その後 `&s#1326::set` 発火 → 残った handle 11 (r.update) は arm_miss → 外側 handle 無し → no_handler → panic

## 根本原因の見立て

`run` の get arm body = `run v: k v`、つまり「新しい初期値 v で `run` を再帰呼び」して新たな catch を積む設計。

これが正常なら **新たな run の `eval_handle.push` が trace に出るはず** だが、trace では出ていない (handle id 11 以降はすべて `r.update` の handler、run の handle は id 1, 3 のみ)。

→ **`run v: k v` の eval が、新たな run の catch まで到達していない**。

考えうる経路:

- (A) lambda/apply chain の eval (`continue_apply_arg` / `force_apply_callee`) で `run` の呼びが catch まで届かない
- (B) monomorphize 後の `run` の get arm body の構造に問題 (catch を含まない形に変形されている)
- (C) thunk の遅延化と展開 (`bind_here`) のどこかで Handle 構造が捨てられる

## 試行した仮説と結果

| 仮説 | 内容 | 結果 |
| --- | --- | --- |
| (1) | Frame::Handle の Thunk 分岐 / value 分岐の挙動を詳しくトレース | trace で race が変動 → 別アプローチへ |
| (2) | `Frame::Handle` value 分岐の Request パスで Handle frame を再 push | 10/10 全失敗 (悪化)。意味論的に間違い |
| (3) | value 分岐 + arm 無し時に Handle を frames 先頭に再 push | 無限ループ (frames が末尾まで進んで Handle だけになると死ぬ) |

仮説 (2), (3) の VM 改変は **revert 済み**。

## 次の調査ステップ

1. failing worker の `&s#N::run` binding body のうち **get arm body 部分の構造** を詳しく確認
   - `Lambda` / `Apply` の連鎖がどう構成されているか
   - 内側の `Handle` が含まれているか、`Thunk` で包まれていないか
2. `continue_apply_arg` / `force_apply_callee` / `apply` にもトレース追加して、`run v: k v` の eval 経路を追う
3. 並列環境特有のメモリレイアウト差 (allocator per-thread arena 等) を疑う

## 2026-05-29 追跡の追記

### 構造解析の発見

- `&s#N::run` の **binding body** outermost: `Lambda(v) Lambda(x) LocalPushId(AddId(Thunk(Coerce(BindHere(AddId(Thunk(Handle)))))))`
- **get arm body** / **set arm body** どちらも `BindHere(AddId(Thunk(Coerce(Apply chain))))` で、Apply chain は `Apply(Apply(Var(run::mono3), Var(v)), Thunk(Apply(Var(k), x)))`
  - `x` = `Var(v)` (get arm) または `Lit(unit)` (set arm)
- `AddId` の `id: Peek`、`allowed: [&s#N]`、`active: false` — 「`&s#N` の effect は allowed、 それ以外は blocked」というスコープ制御

### Apply chain の eval パスにトレース追加して観測

panic 直前の handle 3 (run) の set arm match の直後の trace パターン:

```
inside_handle.remove target_id=3
apply.entry callee=closure(<other_closure>) arg=thunk(blocked=0)   ← !!! 1 個だけ
bind_here.entry value=thunk_expr blocked_count=0
apply.entry callee=effect_op(get) arg=unit                          ← get 発火
bind_here.entry value=thunk_emit effect=get blocked_count=0
continue_handle_result expected=value result=request outer_frames_len=0 outer_handle_ids=[]
... no_handler → panic
```

予想では Apply chain で **inner Apply (run v) と outer Apply (closure, Thunk(k())) の 2 つの apply.entry が出るはず**。
実際は **outer のみ**。inner Apply が `apply.entry` をスキップする経路を通っている。

### 補足: `continue_handle_result` で expected=value

`'r` (run の戻り値型変数) が monomorphize 後 `Type::Value(_)` に解決されている。これにより `continue_handle_result_for_type` は:

```rust
if matches!(expected_ty, Type::Thunk { .. }) { return self.continue_result(result, continuation); }
match result {
    VmResult::Value(VmValue::Thunk(thunk)) => { bind_here ... continue_result(result, outer) }
    VmResult::Request(request) => { continuation.frames.push(Frame::BindHere); continue_result(Request, outer) }
    ...
}
```

set arm body の result が **Request** だった場合、Frame::BindHere を outer continuation の末尾に push して propagate。outer が空 (handle 3 が最外だった) → no_handler。

### `self_name` 設定の問題 (trace の filter)

VM の Lambda の eval は **常に `self_name = None`** で Closure を作る (`interpreter.rs:99` 付近)。
`make_recursive_local_value` で `let` pattern bind の closure にだけ self_name を設定 (`interpreter.rs:1267-1277`)。
つまり、**toplevel binding (`my run(...)`) の Closure には self_name が無い**。trace で `<other_closure>` 表示される。

### 試した仮説と結果

| 仮説 | 内容 | 結果 |
| --- | --- | --- |
| (4) | 仮説 (2) を Request パスのみに限定 | (今日試した) Apply chain の inner Apply の trace が消えてる謎を解明する手前で進行中 |

### 次回続きから入れる手がかり

- failing 時、handle 3 で set arm match → arm body eval が **想定外の経路** (inner Apply が apply.entry を経由しない) を通る
- ここから直接わかる仮説:
  - (a) `bind_pattern` / `arm_env.insert` の中で apply が呼ばれて trace が乱れている
  - (b) `run` の Var lookup が binding ではなく env から直接値を取得し、Apply 評価が省略されている
  - (c) 並列 race で arm body の expr ツリー自体が共有 / 書き換えられている
- 次回のステップ:
  1. `eval_var` にトレース追加して `run` の lookup が走っているか確認
  2. `bind_pattern` 内で apply が呼ばれないかコードを再読
  3. 上記の事象を確証する pinpoint テストを書く

## 2026-05-29 続き — 根本原因が見えた

### 追加トレース

- `eval_var.binding_lookup` / `eval_var.env_hit` / `eval_var.effect_op` を追加（`&s#`, `run`, `update` フィルタ）
- `apply_eval.entry` (ExprKind::Apply 分岐に入った時点で callee/arg の ExprKind と `delay_arg`)
- `apply_eval.callee_ready` (callee 評価が終わって continue_apply_arg に渡る直前)
- `apply_eval.callee_ty` (set/run/Apply の callee.ty を dump)

### failing 時の handle 3 (set match) 直後の経路

```
inside_handle.remove target_id=3 frames_len=9 handle_ids=[3, 4, 7]
bind_here.entry value=thunk_expr blocked_count=1                       ← set arm body の BindHere(AddId(Thunk))
apply_eval.entry callee_kind=Apply arg_kind=Thunk delay_arg=true       ← outer Apply の eval
apply_eval.entry callee_kind=Var(run::mono3) arg_kind=Var(v#local_101343) delay_arg=false  ← inner Apply の eval
eval_var.binding_lookup path=run::mono3
apply_eval.callee_ready callee=closure(self_name=<anon>,body=lambda)
apply.entry callee=closure arg=thunk(blocked=0)                         ← inner Apply の apply(Closure, Thunk)
bind_here.entry value=thunk_expr blocked_count=0                        ← force_apply_arg → bind_here(Thunk)
apply_eval.entry callee_kind=EffectOp(ref_update::update) arg_kind=other ← bind_here 内
apply_eval.entry callee_kind=EffectOp(&s#101326::get) arg_kind=Lit
apply.entry callee=effect_op(get) arg=unit                              ← get の発火
bind_here.entry value=thunk_emit effect=get blocked_count=0
continue_handle_result expected=value result=request outer_frames_len=0 ← outer 空、handler 無し
```

### 根本原因 — set effect op の callee_ty が Thunk param

別の `set` 発火点 (handle 1 の get arm 経由) で `apply_eval.callee_ty` を取った:

```
EffectOp(&s#201326::set) の expr.ty
= Fun {
    param: Thunk { effect: Row[&s#201326, std::var::ref_update], value: Value(str) },
    ret:   Thunk { effect: Row[&s#201326, std::var::ref_update], value: Value(unit) }
  }
```

つまり set 自体の関数型が **`Thunk(str) → Thunk(unit)`** と推論されている。これだと:

1. `set(...)` apply 時 `expects_thunk_arg(&set.ty)=true` → arg を `Thunk(ThunkBody::Expr(arg))` で wrap
2. `apply(EffectOp(set), Thunk)` → `Thunk(Emit { effect: set, payload: Thunk(...) })`
3. handle_request 時の `request.payload` が **Thunk**
4. set arm payload pattern `As { Wildcard{ty:str}, name: v#local_101343 }` → `arm_env.insert(v, Thunk)`
5. set arm body `run v: k()` の eval で `Apply(Apply(run, v=Thunk), Thunk(k()))`
6. inner Apply `apply(run, v=Thunk)`:
   - run の `Lambda(v)` の `param_ty = Value(str)`
   - `closure_param_forces_thunk_arg(Value(str)) = true` かつ `arg = Thunk(_)` → **`force_apply_arg`**
   - `bind_here(Thunk)` で thunk.body の Expr (= `set:ref_update::update:get()` の get 部分) が eval され、`Request(get)` を出す
7. その Request の continuation は inner Apply の `Frame::ApplyArg` だけ。set arm body の outer の `Frame::Coerce / BindHere / AddId` などはまだ積まれていない (return path で乗る前に Request が脱出)
8. `continue_handle_result` で `outer_frames_len=0` → propagate → no_handler → panic

handle 1 (get) では get に payload が無いので同じ症状にはならない。**set だけ payload を持つから** ここでだけ症状が出る。

### なぜ並列でだけ起きるか

- 単スレッドでも構造的には起きうるはずだが、テストが通っている
- 仮説: monomorphize / lower キャッシュが並列実行で「set の type を `Thunk(...) → Thunk(...)` 形で焼き付けたバージョン」と「`Value(str) → Value(unit)` のバージョン」が混在し、handle 1 のような最初の `set` (handler arm の外) は前者で焼かれ、handle 3 の set arm の中の `set` 発火は後者で焼かれる、というように **同じ source の異なる use site が別 type で monomorphize されている** 可能性
- Codex の compile_vm_module キャッシュレイヤを次に疑う

### 次回のステップ

1. **set effect op の type が `Thunk(...) → Thunk(...)` になっている経路を特定**:
   - effect の declared type は `set: 't -> ()`。これが lower3 / infer3 / monomorphize のどこで Thunk(...) に化けるか
   - 直接的に: `crates/yulang-runtime-lower/` で effect op の declared type → Expr ty の変換を確認
2. **`closure_param_forces_thunk_arg` が True のとき force_apply_arg で bind_here を呼ぶ設計の妥当性**:
   - もし type が `Value(str)` で正しく、arg が誤って Thunk になっているなら、payload を eager 評価する側を直す
   - もし型レベルで Thunk(...) → Thunk(...) が正しく、handler 側で payload を force する責務なら、bind_here の effect 発火経路を outer continuation に乗せる修正
3. **pinpoint テスト**:
   - `act foo: our op: int -> ()` のような最小 effect を定義
   - `catch:` 内で payload を再帰呼び出しに渡す ↓ パターンで再現する単スレッドテスト
   - 並列実行に依らず再現すれば、構造バグであることが確定する

### 残してある trace 装備（git diff に乗ってる）

- `interpreter.rs::eval_var` に `trace_eval_var{,_binding,_effect_op}` の三系列
- `interpreter.rs::eval_expr::Apply` に `trace_apply_eval_entry` / `trace_apply_callee_ty` / `trace_apply_eval_callee_ready`
- すべて `YULANG_TRACE_HANDLE` env で gate されているので、通常実行には影響しない

## 道具立て (revert 済み、次回再現用)

以下を `crates/yulang-vm/src/vm/` 配下に再実装する想定:

- `interpreter.rs`:
  - `handle_trace_enabled()` (env var `YULANG_TRACE_HANDLE` で gate、`OnceLock` でキャッシュ)
  - `HANDLE_TRACE_BUFFER` (`thread_local!` の `Vec<String>`)
  - `trace_handle_push` (eval_handle で Handle frame push 直前)
  - `trace_handle_repush` (Frame::Handle の Thunk 分岐の再 push)
  - `trace_handle_request_outcome` (`handle_request` で blocked / matched 判定)
  - `trace_handle_request_arm_miss` (arm match 失敗 + arm 一覧)
  - `trace_propagate_entry` (`propagate_request_before` 入口で frames 状態)
  - `trace_propagate_no_handler` (handler 見つからず外に流れた時)
- `continuation.rs`:
  - `trace_handle_event` (`inside_handle` / `outside_handle` の remove/truncate/clear 直前)
- `tests.rs`:
  - panic hook (`ensure_panic_dump_hook`) で panic 時に thread-local trace buffer + `&s#` を含む binding body を出力
  - env var `YULANG_PANIC_DUMP=1` で binding body 全文 dump 追加

10 回ループ実行例:

```sh
for i in $(seq 1 10); do
  YULANG_TRACE_HANDLE=1 RUSTC_WRAPPER= \
    cargo test -q -p yulang-vm vm_std_pipeline_survives_parallel_source_ref_runs -- --nocapture \
    > /tmp/yulang-trace-$i.log 2>&1
  echo "run=$i exit=$?"
done
```

## 注意点

- `cargo test ... | tail -N` で **exit code が tail のものに変わって誤認** する (pipefail なしの場合)。直接 redirect 推奨。
- trace を挿入すると flake 率が大きく変動する。判断は十分なサンプル数 (10+ 回) で。
- 直接 `eprintln!` トレースは race を完全に消す。**buffered trace + panic hook** が現実的。

## 引き継ぎ前提

- 標準ライブラリの一時変更は **戻されたまま** (引き継ぎ通り)
- 全テスト通過していないので publish / deploy は **しない**
