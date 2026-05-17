# prompt-10: ignored bind_here force と handler specialization shape

2026-05-17 追加。

対象:

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_junction_method_undet_once_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_loop_through_cps_repr
```

## 直したこと

### ignored `bind_here` force の direct call mode

`Stmt::Expr(BindHere(...))` の値を捨てる immediate force では、戻り値の thunk を
その場で force するため、通常の `sync_apply_for_immediate_force_depth` と同じ扱いに
すると、effectful helper の direct call mode が広すぎる。

ただし、`std::junction::*` のような higher-order helper は、値を捨てる immediate force
でも handler / callback 境界をまたぐ return frame が必要になる。

そのため `sync_direct_call_for_ignored_force_depth` を分けた。

- 値を捨てる `unit` thunk immediate force は `SyncDirect`
- higher-order helper の非 `unit` thunk は `EffectfulWithResume`
- ignored immediate force では通常の `target_may_perform` だけで `EffectfulWithResume`
  にしない

これで次を両立した。

- `runs_junction_method_undet_once_through_cps_repr`
- `runs_effect_handler_guard_block_tail_through_cps_repr`

### handler adapter 後の specialization shape

`runs_var_update_in_for_loop_through_cps_repr` は `4` ではなく `15` になっていた。

bisect では `d209ca1 Refine monomorphized runtime type audit` から壊れていた。
ただし substitutions 自体は正しく、`std::flow::loop::for_in` では
`t5852 := &hits#var` まで解けていた。

壊れていたのはその後で、handler adapter 適用後の final refresh が
`binding.body.ty` から `binding.scheme.body` を再投影し、contextual input/output shape を
落としていた点。

結果として `for_in` の callback が:

```text
int -> Thunk[&hits#var, unit]
```

ではなく:

```text
int -> Thunk[[std::flow::loop; &hits#var], ⊤]
```

へ広がり、var handler の resumption が loop continuation まで巻き込んで replay していた。

final refresh 後に `input_shapes` / `output_shape` を scheme へ再適用し、同じ runtime type を
lambda spine にも戻すようにした。これで function table が見る param/return type と
specialization key の shape が一致する。

## 確認したテスト

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_loop_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_if_body_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_var_update_in_for_if_else_body_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_junction_method_undet_once_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_junction_condition_once_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_undet_logic_nested_each_sum_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_effect_handler_guard_block_tail_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_direct_return_hygiene_result_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_callback_return_hygiene_result_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_indexed_ref_update_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_recursive_effect_handler_tuple_result_through_cps_repr
```

すべて pass。
