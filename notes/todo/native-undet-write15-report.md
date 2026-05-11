# native-undet-write15 実装レポート

## 実装したこと（write15 指示ベース）

write15 §3 の targeted lowering + §4 の判定条件強化 + 追加 delimited-continuation extent
管理を実装した。

### 1. `FunctionLowerer.higher_order_helper` フラグ

関数名ベースで「higher-order helper」を判定する flag を追加。

```rust
let higher_order_helper = name.starts_with("std::list::fold_impl")
    || name.starts_with("std::undet::undet::each")
    || name.starts_with("std::undet::undet::once");
```

write15 §4 D に従い、「temporary targeted workaround」コメント付き。
将来は effect row based detection へ置き換える前提。

### 2. `lower_apply` の targeted 化

`higher_order_helper` の関数の body 内で、apply の result type が Thunk-wrapped なら
`EffectfulApply` terminator を発行（write15 §3.1）。post-call cont を split。

```rust
if self.higher_order_helper && matches!(expr.ty, runtime::Type::Thunk { .. }) {
    let post_cont = self.fresh_continuation();
    let result = self.fresh_value();
    self.terminate(CpsTerminator::EffectfulApply { closure, arg, resume: post_cont });
    self.finish_current();
    self.current = ContinuationBuilder::new(post_cont, vec![result]);
    return Ok(result);
}
```

### 3. `lower_expr` direct_apply の targeted 化

同様に DirectCall も EffectfulCall terminator にする（write15 §3.2）。
ここは `info_returns_thunk` (callee's return type) で判定 — `expr.ty` が runtime IR で
ストリップされているケースを拾うため。

```rust
if self.higher_order_helper && info_returns_thunk {
    let post_cont = self.fresh_continuation();
    let result = self.fresh_value();
    self.terminate(CpsTerminator::EffectfulCall { target, args, resume: post_cont });
    self.finish_current();
    self.current = ContinuationBuilder::new(post_cont, vec![result]);
    return Ok(result);
}
```

### 4. 引数の demand-side forcing

call site で arg が `Thunk{Fun{...}}` に wrap されているケースを `force_if_non_thunk_demand`
で展開して callee に plain な closure を渡せるようにした。

```rust
.map(|(idx, arg)| -> CpsLowerResult<CpsValueId> {
    let expected = info_params.get(idx).cloned().unwrap_or_else(runtime::Type::unknown);
    let lowered = if matches!(expected, runtime::Type::Thunk { .. }) {
        self.lower_expr_as_thunk_value(arg)?
    } else {
        self.lower_expr(arg)?
    };
    Ok(self.force_if_non_thunk_demand(lowered, &expected))
})
```

### 5. `CpsHandlerFrame.return_frame_threshold`

write15 のテキストには直接書かれてなかったけど、`sub::return` のような non-local exit が
ハンドラスコープ内で push された return_frame を discard する必要があると判明したので、
新フィールドを追加。

```rust
struct CpsHandlerFrame {
    // ...
    /// `return_frames.len()` at the time this handler was installed.
    /// When a `ScopeReturn` jumps via this handler's escape, frames
    /// pushed after install must be discarded (delimited continuation
    /// extent semantics).
    return_frame_threshold: usize,
}
```

`ScopeReturnAction::JumpOrExit` にも threshold を伝播。dispatch_scope_return と Perform
postprocessing で `return_frames.truncate(threshold)` を実施。

### 6. 必要な防御

continue_return_frames で `frame.owner_initial_frame_count > rest.len()` になりうる
(ScopeReturn truncation で削られた後) ので `min` で clamp。

```rust
let owner_initial = frame.owner_initial_frame_count.min(rest.len());
```

---

## テスト状況

### 通った

- **既存 167 通常テスト** PASS（regression なし）
- `debugs_local_choice_caller_rest_eval` (write12 minimal) PASS
- `debugs_local_choice_callback_rest_eval` (write13 Test A) PASS

### Cranelift で #[ignore] にした

write15 §1.1 で予告されていた regression に対応するため、3 テスト ignore：

- `compares_std_undet_once_scalar_unwrapped_through_cps_repr_cranelift`
- `compares_std_each_with_local_once_dfs_through_cps_repr_cranelift`
- `compiles_std_undet_once_through_cps_repr_object`

これらは Cranelift backend が `EffectfulCall/Apply/Force` を未実装で `todo!()` で停止する。
write15 §10「Cranelift は別段階」の方針通り。

### まだ通らない（次段階）

- **`debugs_std_undet_once_skip_eval_layers`**:
  - write14: `cps:0 vs vm:2`
  - 今回 (write15 修正後): `cps:3 vs vm:2`
  - **進歩**: fold_impl 内の effectful callsite が capture されるようになり、
    バックトラックの一部が動いている（cps:0 = 完全失敗ではなく cps:3 = 部分動作）
  - **残るバグ**: バックトラックが 1→2 で止まらず 1→2→3 と進む。
    once の `loop(k true, queue+[k])` 部分または resumption の状態管理が
    まだ何か外している。

---

## fold-like local minimal test について

write15 §7.2 が示した Test B（`fold2`-based）をいくつかの形で試したが、
yulang の `catch` セマンティクス（同じハンドラが再入 branch を扱えない、
inner catch's value arm が外側の branch を伝播しない等）と組み合わさり、
**期待値が VM レベルですら明確に決まらない**ケースが多かった。

`my work() = { my n = fold2 0 (\a b -> case branch: true -> b; false -> reject); ... }`
の期待値 2 を VM が出さず Request になる（branch 2回目を H1 が catch しないため）。

サブ書き換えに時間がかかるので、Test B は今回 commit せず、std::undet.once 経路の
直接デバッグに集中した。

---

## 残るバグの読み（cps:3）

trace で確認した行動:
1. iter 1: branch=true → sub::return 1 → each returns 1 → work n=1 → guard fail → reject
2. once の reject arm: uncons queue → just(k1, []) → loop(k1 false, [])
3. iter 2: callback for x=2 with branch=false → fold continues
4. iter 3: callback for x=3 with branch=... ← どこかでパスが分岐ミス
5. 最終的に 3 が返る

`cps:3` は `each [1,2,3]` の最後の要素。バックトラックが 2 で止まらず 3 まで
進んでしまっている。

可能性:
- once の `loop` 再帰呼び出し（`loop k_thunk queue`）が curried ApplyClosure stmt の
  ままで、my type-check (expr.ty Thunk) が curried partial には matchしない
- 結果として loop の再帰が「post-iteration cont を frame として持たない」状態
- 2 で guard が pass しても、何らかの理由で work が 2 を返さず、再 reject に流れて
  3 まで進む

次のステップ:
- once__mono4 の cont 6 (branch arm) の ApplyClosure を unconditionally
  EffectfulApply にする（curried 2段とも）
- または、once 専用に `ApplyClosure → EffectfulApply` 化を強化
- もしくは Cranelift 対応を先に進めて、Layer 1 だけで semantics 確認

---

## 触ったファイル

- `crates/yulang-native/src/cps_lower.rs`: higher_order_helper flag、lower_apply/direct_apply
  の effectful 化、args の force_if_non_thunk_demand
- `crates/yulang-native/src/cps_eval.rs`: `CpsHandlerFrame.return_frame_threshold`、
  `ScopeReturnAction::JumpOrExit.return_frame_threshold`、dispatch_scope_return での
  truncate、continue_return_frames での owner_initial clamp
- `crates/yulang-native/src/source.rs`: 3 つの Cranelift テストに `#[ignore]`

---

## りなに渡す質問

1. **`expr.ty` 経由の effect 判定が不安定**:
   curried partial apply の `Fun{queue, Core(opt int)}` のような中間タイプは
   Thunk-wrapped でない場合が多く、`info.ret` を見ても callee が closure value だと
   不明。`higher_order_helper` 内では全 ApplyClosure を effectful にする方向と、
   callee の型 (Var → closure param) を見て判定する方向、どちらが筋がいい？

2. **`return_frame_threshold` 設計**:
   今回 ScopeReturn の non-local exit で `return_frames.truncate(threshold)` を入れた。
   これは delimited continuation extent としては妥当だと思うが、`continue_return_frames`
   の owner_initial が後から不整合になる現象が起きた。設計上正しい解は何？

3. **cps:3 になる原因**:
   `loop(k true, queue+[k])` の curried apply が sync ApplyClosure stmt のままで
   local rest が漏れている、という読みであっている？
   それとも別の場所（once の value arm `v -> just v` の伝播路、もしくは reject arm の
   recursive call 等）の問題？

---

## コミット予定

write15 partial。
- 既存 170-3 = 167 通常テスト PASS
- write12/13 local minimal tests 継続 PASS
- 3 つの std::undet 系 Cranelift テスト #[ignore] 化
- std::undet.once Layer 1 は cps:3 vs vm:2 で未通過（次タスク）
