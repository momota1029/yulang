# prompt-8: junction + each + method の `:just 3`

対象:

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_junction_method_undet_once_through_cps_repr
```

2026-05-17 の状態:

- CPS eval / CPS repr eval は `:just 18`
- Cranelift JIT は `:just 3`
- 近い guard:
  - `runs_junction_condition_once_through_cps_repr` は通る
  - `runs_undet_once_if_true_branch_through_cps_repr` は通る
  - `return_hygiene` は通る

## 今回の切り分け

`YULANG_CPS_JIT_TRACE=1` で見ると、失敗時の終盤は次の形になる。

```text
route_scope_return.scan: prompt=1 value=:just 3 current_eval=274 ...
  stack=[h5(prompt=1, install_eval=6), h0(prompt=2), h1(prompt=9)]
  frames=[
    frame owner_eval=8 owner_fn=root handlers=[h5, h0],
    frame owner_eval=270 owner_fn=each handlers=[h5, h0, h1],
    frame owner_eval=274 owner_fn=fold handlers=[h5, h0, h1],
  ]
route_scope_return: prompt=1 action=propagate value=:just 3
...
route_scope_return: prompt=1 current_eval=7 action=frame_walk fi=2 hi=0 value=:just 3
abort_mode: mode=2 frame_len=1 value=:just 3
```

つまり、outer `.once` の prompt 自体は最終的に frame-walk で見つかる。
ただし、その時点で値がすでに `:just 3` になっている。これは
`each [3, 4, 5]` の first payload `3` が、`point { x: 3, y } .norm2`
まで進まずに `.once` の value arm へ入っている形。

## 試したが違った方向

### `return_i64` で guarded routed jump を consume する

`return_i64` の `mode == 2 && RoutedJump` ガードを外すと、
`runs_junction_condition_once_through_cps_repr` が `:just 18` ではなく
`18` になる。

これは prompt-7 / direct return hygiene で見た通り、guard を持つ routed jump を
一般に consume すると `.once` の value arm 境界を飛ばす。今回もこの方向は
症状側の修正で、原因ではない。

### `force_thunk_i64` の snapshot restore 条件だけを広げる

`ScopeReturn` が未解決のまま残る場合、caller frame snapshot を戻す方向は
N13 の過去メモと一致する。ただしこれだけでは `:just 3` は変わらない。

このため、単純に「method 後続 frame が復元されていない」だけではなく、
outer `.once` が再開する resumption の中で `sub::return x` 以降の continuation
segment が短すぎる可能性が高い。

## 次に見る場所

本命は `branch(), k -> loop(k true, ...)` の `k true` が返す範囲。

期待する流れ:

```text
branch true
  -> each の fold callback
  -> sub::return 3
  -> each 式の後続
  -> point { x: 3, y: 3 } .norm2
  -> outer once value arm
  -> :just 18
```

今の JIT は実質的に次のように見える。

```text
branch true
  -> each の fold callback
  -> sub::return 3
  -> outer once value arm
  -> :just 3
```

なので次は、`effectful_apply_resumption_native` /
`merge_extras_into_frames_native` /
`rebase_captured_handler_thresholds` のどこで
`sub::return` 後の ordinary continuation が落ちるかを見る。

特に trace では、JIT の `effectful_apply_resumption` が combined frame を
作ったあとに `ScopeReturn` routing / state restore を caller と同じ粒度で
扱えているかを確認する。

