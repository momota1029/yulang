# runtime-finalize 引き継ぎメモ 2026-05-24

## 背景

`yulang-runtime-finalize` の新 solver で、apply 結果の型変数が十分に束縛されず、トップレベル以外や中間 apply の型が不安定になっている。

ユーザーからの直近指示は次の通り。

- `boundary_expr` 判定で root / boundary だけを特別扱いするのは不可。
- 片側 bound でもよいので、apply 結果はちゃんと束縛する。
- 式や制約式は、内容を理解してから変化させる。
- 現在の途中差分は別担当に引き継ぐ。

## 現在の worktree

未コミット差分あり。

- `crates/yulang-runtime-finalize/src/graph.rs`
- `crates/yulang-runtime-finalize/src/solver.rs`
- この引き継ぎメモ

直前の clean commit は `c84245a Add runtime finalize IR dump`。

現在のコード差分はかなり大きい。特に `graph.rs` の effect row merge / normalize は実験色が強く、まだ採用確定ではない。

## 直近で確からしい観測

### 1. `boundary_expr` 方式は捨てる

`boundary_expr` で root apply だけ結果型を縛る方式は rejected。

現在の差分では `boundary_expr` は削除済みで、各 `ApplyStep` に `apply: &Expr` を持たせ、spine 内の全 apply step で結果 hole を作る方向に寄せている。

### 2. apply ごとに value result と effect result を分ける必要がある

単に apply 結果を `runtime_type_to_core(expr.ty)` に縛るだけだと、`RuntimeType::Thunk { effect, value }` の effect を落として handler から request が漏れる。

現状の方向性:

- `result = graph.fresh_hole("apply")`
- `result_effect = graph.fresh_hole("apply_effect")`
- expected callee を `arg_type -arg_effect / result_effect-> result` として作る
- `current <: expected` を入れる
- apply 式の evidence / runtime type から `result` と `result_effect` を追加で束縛する

これは方向性としては妥当そう。

### 3. VM は中間 apply の `callee.ty` を見て thunk 引数を遅延する

重要。

`yulang-vm` の control VM は apply 引数を遅延するかどうかを `expects_thunk_arg(&callee.ty)` で判定している。

つまり、例えば `(&x::run init) body` のような二段 apply では、二段目 apply の callee は一段目 apply そのものなので、一段目 apply の `ty` が `RuntimeType::Fun { param: Thunk(...), .. }` になっていないと body が遅延されない。

runtime-finalize が最終 apply の `expr.ty` だけ更新して、中間 apply の `ty` を更新しないと、handler の外で effectful body が評価されて `&x#get` / `&x#set` が漏れる。

この観測はかなり確度が高い。

関連箇所:

- `crates/yulang-vm/src/vm/control.rs`
  - `ControlBuilder::expr`
  - `expects_thunk_arg`
  - `control_lambda_shape`
- `crates/yulang-runtime-finalize/src/solver.rs`
  - `rewrite_simple_apply`
  - `replace_apply_spine_binding`

現在の差分では `refresh_apply_spine_runtime_types` を追加して中間 apply 型を再計算しようとしているが、まだ ref テストは通っていない。

## 現在の未コミット差分の内容

### `graph.rs`

入っているもの:

- `TypeGraph` に `constraints: Vec<SubtypeConstraint>` を追加。
- `constrain_subtype` が constraint を保存し、bound 追加後に再伝播する。
- `record` / `push_bound` が `bool` を返し、伝播ループの変更検知に使う。
- `subtype_constraints_propagate_after_later_bounds_arrive` テスト追加。

これは比較的まともな方向に見える。理由は、`a <: b` を先に入れてから `a` の下界が後で来るケースを拾えるため。

怪しいもの:

- `type_contains_var(previous) || type_contains_var(&ty)` のとき conflict を握りつぶす処理。
- `normalize_bound_form` / `merge_effect_row_bounds` / effect row flatten 系。
- upper bound 側の row merge / intersection flatten。

これらは二重ループ ref update の衝突を避けようとして入れたが、最後は stack overflow まで行った。次の担当は一度戻す候補として見た方がいい。

### `solver.rs`

入っているもの:

- `ApplyStep` に `apply: &Expr` を追加。
- apply ごとに `apply_effect` hole を作る。
- `ApplyEvidence.result` と `expected_callee/callee` の `ret_effect` から result / effect の bound を追加する helper を追加。
- `runtime_type_from_core_value*` を追加し、core function type を `RuntimeType::Fun` / `RuntimeType::Thunk` へ戻す処理を追加。
- `solved_callee_runtime_type` を追加し、alias callee type に `binding.body.ty` を materialize したものを使う試み。
- `refresh_apply_spine_runtime_types` を追加し、rewrite 後の中間 apply 型を再計算する試み。
- `root_apply_result_type_bounds_open_return_var` テスト追加。

比較的残す価値がありそうなもの:

- `ApplyStep.apply`
- apply ごとの `result` / `result_effect` hole
- `ApplyEvidence.result` を value result bound として使うこと
- 中間 apply の `ty` 再計算が必要という観測

怪しいもの:

- `result_effect` bound を `expected_callee` / `callee` の ret_effect からどう取るか。
- `RuntimeType::Core(Fun)` から `RuntimeType::Fun` へ戻す helper の条件。
- `solved_callee_runtime_type` が `binding.body.ty` を優先する処理。
- `runtime_type_value_is_function` で runtime type の function upper を一部 skip する処理。

## 現在のテスト状況

通常テスト:

```sh
cargo test -q -p yulang-runtime-finalize
```

結果:

- pass
- `35 passed; 0 failed; 5 ignored`

ignored の ref 系:

```sh
cargo test -q -p yulang-runtime-finalize prewarmed_std_finalize_runs_ref_assignment_inside_nested_block -- --ignored --nocapture --test-threads=1
```

現在の失敗:

```text
expected int VM result, got request Path { segments: [Name("&x#481"), Name("set")] }
```

以前の同テスト失敗は `&x#get` だった。中間 apply 型の再計算を入れてから `get` から `set` に変わった。

```sh
cargo test -q -p yulang-runtime-finalize prewarmed_std_finalize_runs_ref_assignment_inside_nested_for_loops -- --ignored --nocapture --test-threads=1
```

現在の失敗:

```text
thread 'runtime-finalize-large-stack' has overflowed its stack
fatal runtime error: stack overflow
```

全 ignored:

```sh
cargo test -q -p yulang-runtime-finalize -- --ignored --nocapture --test-threads=1
```

現在は nested block で `&x#set` が漏れ、その後 nested for loop で stack overflow。

## 重要な再現入力

### nested block ref update

```yul
{
    my $x = 0
    {
        &x = 9
    }
    $x
}
```

期待値: `9`

現在の ignored test では `&x#set` request が handler から漏れる。

### nested for loop ref update

```yul
{
    my $total = 0
    for x in 1..3:
        for y in 1..2:
            &total = $total + x + y
    $total
}
```

期待値: `21`

現在は runtime-finalize test thread で stack overflow。

## 次の担当へのおすすめ方針

### 1. まず effect row merge 実験は疑う

`graph.rs` の `normalize_bound_form` / `merge_effect_row_bounds` 系は、症状回避のために後から足したもの。

今の stack overflow は、upper bound の effect row を広げたり、handler の subtraction 済み effect を壊した結果の可能性がある。

ここは最初に戻す候補。

残すなら、`lower` は union、`upper` は intersection という lattice として明文化し、row tail / inter / synthetic effect atom の正規化を別 module に切る方がよい。

### 2. 中間 apply 型の再計算を小さく検証する

`refresh_apply_spine_runtime_types` の発想自体は正しそうだが、現在の実装はまだ荒い。

確認したいこと:

- `&x::run #x body` の rewrite 後、一段目 apply の `ty` が `RuntimeType::Fun { param: Thunk[&x, int], ret: int }` 相当になっているか。
- 二段目 apply の arg が VM builder で `delay_arg = true` になるか。
- `&x#set` を含む inner block が handler の内側で thunk として評価されるか。

IR dump を使うなら:

```sh
printf '{\n    my $x = 0\n    {\n        &x = 9\n    }\n    $x\n}\n' \
  | cargo run -q -p yulang -- dump --runtime-finalize-ir --verbose-ir
```

ただしこれは finalize 前 dump。finalize 後 dump はまだ無い。

### 3. alias callee type の決め方を整理する

現状の `solved_callee_runtime_type` は、まず `binding.body.ty` を materialize して、閉じていればそれを alias callee type にしている。

狙いは、scheme の core function から復元すると `Any` / Top effect が落ちて、VM の thunk 遅延判定に必要な `RuntimeType::Thunk` が消えるのを避けること。

ただし、この処理だけでは `&x#set` 漏れは直っていない。理由候補:

- `binding.body.ty` が閉じているように見えても、必要な effect structure が失われている。
- `refresh_apply_spine_runtime_types` が spine の途中型を正しく更新していない。
- rewrite の順序上、materialize 後に別処理が `expr.ty` を潰している。
- handler body の thunk / bind_here 形そのものを旧 monomorphizer 相当に復元する必要がある。

### 4. 旧 monomorphizer の該当処理を読む

参考箇所:

- `crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs`
  - `rewrite_apply`
  - `adapt_apply_result_from_evidence`
  - `runtime_type_from_core_value_and_effect`
  - `contextual_final_call_type`
- `crates/yulang-runtime/src/monomorphize/pipeline/shape.rs`
  - `core_function_as_hir_type`
  - `effected_core_as_hir_type`
- `crates/yulang-runtime/src/types/effect.rs`
  - `should_thunk_effect`
  - `effect_is_empty`

旧実装は大きいが、次だけは runtime-finalize 側にも必要そう。

- core function type を HIR runtime function type に戻す。
- apply の result effect が非空なら、VM が thunk として扱える runtime type を残す。
- 中間 apply の `ty` を、単相化後の callee type から連鎖的に更新する。

## 注意点

- `Any` は Top。曖昧型ではない。
- `Never` は Bottom。placeholder ではない。
- 未確定は `Unknown` のみ。
- path 文字列ベースで型を決めない。
- `boundary_expr` 判定に戻さない。
- effect handler の `junction` と if branch 合流を混同しない。
- effect row の subtraction があるので、row を単純 union してはいけないケースがある。

## いまの差分をどう扱うか

おすすめは次のどちらか。

1. 現在の差分から、明らかに使える小さい核だけを抽出する。
   - constraint replay
   - per-apply `result` / `result_effect` hole
   - 中間 apply 型再計算の必要性を示す小テスト

2. `c84245a` から作り直す。
   - ただし `boundary_expr` 方式は戻さない。
   - ref test を先に置き、VM の `delay_arg` 判定に必要な runtime type を保証する方向で進める。

現在の大きな dirty diff をそのまま積むのは危険。
