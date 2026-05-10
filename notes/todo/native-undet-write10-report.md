# write10.md 実装報告

## 受領した指示

1. Phase F.5 step 5 を実装する（lower_root / lower_lambda / lower_recursive_lambda の return site で `force_if_non_thunk_demand`）
2. evaluator で root thunk を無条件 force しない
3. ListAppend/ListUncons や Cranelift helper には今は進まない、まず root thunk leak を解消する
4. 成功条件: `debugs_std_undet_once_skip_eval_layers` が CPS eval → CPS repr eval → Cranelift の 3 層で通る

## 進めたこと

### 1. Phase F.5 step 5 実装

`crates/yulang-native/src/cps_lower.rs` の以下に `force_if_non_thunk_demand` を入れた:

- `lower_root` 内 `Return(value)` 直前
- `lower_lambda` 内 `Return(value)` 直前
- `lower_recursive_lambda` 内 `Return(value)` 直前

既存の `force_if_non_thunk_demand` をそのまま使用（write10.md に「既存をそのまま return にも使う」と書いてあった通り）。

### 2. ApplyClosure dispatch on Resumption（cps_eval.rs）

`std::undet.once` の reject arm が queue から resumption を取り出して `k false` する経路で、surface 型からは `k` が closure か resumption か判別できないため lowering は `ApplyClosure` を出す。eval 側で `ApplyClosure` の対象が `Resumption` 値だった場合、`Resume` として実行するように切り替えた。

### 3. List ops in CPS domain（cps_eval.rs）

resumption 入りの queue に対して `std::list::uncons` が動くよう、`eval_cps_primitive` に以下を追加:

- `PrimitiveOp::ListLen`
- `PrimitiveOp::ListIndex`
- `PrimitiveOp::ListIndexRangeRaw`
- ヘルパ `cps_value_to_usize`

### 4. unit test golden 更新

新しい return forcing の影響で:

- `lowers_pure_int_add_to_multishot_cps`
- `lowers_direct_call_to_cps`
- `lowers_if_to_multishot_continuation_graph`

の 3 つで CPS dump が変化（`Return` する value が `ForceThunk` 後の slot に変わる）したので、期待値を更新。

## 結果

`debugs_std_undet_once_skip_eval_layers` の症状は

```
Eval(ExpectedPlainValue { function: "root_0", id: usize::MAX })
```

から

```
ValueMismatch { index: 0, vm: Int("2"), cps: Int("1") }
```

に変わった。**root thunk leak は解消した**。しかし新たに**Aborted propagation の semantic 問題**が顕在化した。

## 判明した問題

### 中核の問題: Aborted が catch scope を越えて root まで propagate する

CPS eval の `Perform` terminator は handler arm の戻り値を `Aborted(value)` で wrap する。Aborted は `DirectCall` / `ApplyClosure` / `ForceThunk` / `Resume` / `ResumeWithHandler` で「skip」されて伝播する。最終的に `unwrap_aborted` が root で剥がす。

`each [1,2,3]` の実装は

- sub-flow handler を install
- fold で各要素に対し `case branch(): true -> sub::return x | false -> ()`
- fold 後に `reject()`

という構造で、`each` は **必ず abort で抜ける**（sub::return か reject かのどちらか）。sub::return v は sub-flow handler が捕捉して v を返す。

Aborted の現状の semantic はざっくり「直近の Perform から root まで一直線に skip する」。これだと、

```yulang
my work(): int = {
    my n = each [1, 2, 3]   --(1) sub::return 1 が abort で漏れる
    guard: n > 1            --(2) 実行されない
    n                       --(3) 実行されない
}
case work().once: ...
```

の (1) で sub::return 1 → Aborted(1) → work の guard / Return をすべて skip → once → root で unwrap → 1。VM だと (1) は `each` の戻り値として 1 を return するだけで、(2) で guard が reject、once が backtrack して 2 を取り出すが、CPS だとそこに到達しない。

### 「Aborted を Perform で wrap しない」を試すと別のとこが壊れる

`Perform` 終端で `Aborted(...)` を作らず arm の戻り値をそのまま返すと、

- sub::return 1 は arm cont(13) → Continue cont(2) → `Return V1` で eval_continuations は 1 を返す
- これは `each` の cont(0) で `DirectCall fold_impl` の結果になってしまう
- 次に `Perform reject(V19)` が実行されてしまう（sub::return が短絡しなくなった）
- once の reject arm が動いて backtrack するが、その結果が `each` の戻り値として外に出てくる
- work が `each` の結果として `Variant just(2)` のような変な値を受け取り、`> Variant 1` で `PrimitiveTypeMismatch IntGt: Variant nil` で爆死

つまり Aborted は「sub::return が `each` 全体を一発で抜ける」短絡の意味で必要。一方で root まで全部 skip するのは行き過ぎ。

### 望ましい semantic

Aborted は **handler の install scope** を抜けるところまで走り、その scope を抜けた瞬間に「unwrap して通常値として」flow に戻すべき。具体的には:

- `each` 内の sub-flow handler scope を抜ける時に Aborted(1) → 1 になるべき
- `each` の caller (work) は 1 を見るべき
- 一方、once の branch arm が perform した Aborted(loop_result) は once の install scope（once cont(3) の InstallHandler）を抜ける時に unwrap される

これを実装するには Aborted が「どの handler に向かっている abort なのか」を知る必要がある。あるいは InstallHandler/UninstallHandler 周辺で flow を見て unwrap タイミングを判定する。

### 試したが見送ったアプローチ

1. **`lower_expr_as_thunk_value` で expr.ty が Thunk なら wrap しない** — over-wrapping を消そうとした。`compares_std_undet_once_scalar_unwrapped`（既に通っていたテスト）を壊したので revert。
2. **Perform で Aborted wrap しない** — 上に書いた通り型不整合になる。
3. **eval_function 境界で Aborted を unwrap する** — once（外側に install）と sub-flow（内側に install）を区別できないので不可。

## 質問

1. **Aborted propagation の handler-aware 化を実装すべきか？** たとえば `Aborted { handler_id, value }` にして、`InstallHandler` の地点を抜けるとき unwrap するように設計を改める。CPS repr / Cranelift にも同じ semantic を波及させる必要があるので影響範囲は中規模。
2. **あるいは別の表現方法**（例: `CpsRuntimeValue::ScopeReturn { from_handler: HandlerId, value }`）の方が良いか？
3. **同じ問題が CPS repr eval / Cranelift にも存在するはず** だが、現状は CPS eval が落ちるので発見できていない。CPS eval を直してから次に行くべきか、それとも Cranelift で先に検出してから設計を決めるか？
4. simple test `compares_std_undet_once_scalar_unwrapped` がたまたま通っていたのは、x=1 のとき VM/CPS どちらも 1 を返して一致するため。**この test も実は handler-aware Aborted が無いと semantically 怪しい** ことを念頭に置くべき。

## 副作用 / 副産物

### `force_if_non_thunk_demand` の挿入箇所

すべての lambda body / root return に挿入したので、CPS dump がやや冗長（連続する `ForceThunk` が増える）。`ForceThunk` は plain value に対して no-op なので runtime コストはほぼ無いが、IR の見た目は変わった。

### unit test 3 つの golden 更新

`crates/yulang-native/src/cps_lower.rs` の以下のテスト golden を更新:

- `lowers_pure_int_add_to_multishot_cps`
- `lowers_direct_call_to_cps`
- `lowers_if_to_multishot_continuation_graph`

これは仕様上の変更（return site で必ず force する）の付随的な変化。

### 既存 ignored test の状態

write9 で追加した 4 本の regression は引き続き `#[ignore]`:

- `compares_recursive_closure_self_reference_through_cps_repr_cranelift`
- `compares_std_undet_once_skips_rejected_first_choice_through_cps_repr_cranelift`
- `compares_std_undet_once_returns_nil_when_all_rejected_through_cps_repr_cranelift`
- `compares_std_undet_once_two_nested_choices_through_cps_repr_cranelift`

`debugs_std_undet_once_skip_eval_layers` も依然 `#[ignore]`。すべて Aborted の handler-aware 化を待つ。

## 触っていない

- write10.md 第5節の「次に確認する小さいテスト」の系列（effect なし if、effect あり guard なし、effect あり guard あり）は CPS eval が落ちるので比較できていない
- recursive closure regression を `with: our loop` 系で書く改善は未着手
- block syntax `case ({ ... }).once:` の `undefined name` 問題は別 issue として保留

## 状態スナップショット

- 170 passed, 12 ignored, 0 failed (yulang-native)
- 主な変更: cps_lower.rs（Phase F.5 step 5）, cps_eval.rs（ApplyClosure-on-Resumption + list ops）, cps_lower.rs unit test goldens 更新

次は handler-aware Aborted の設計判断待ちかなぁ。
