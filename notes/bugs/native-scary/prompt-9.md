# prompt-9: junction method once の capture parity と外れた仮説

対象:

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_junction_method_undet_once_through_cps_repr
```

2026-05-17 追加の切り分け。

## 分かったこと

`effectful_apply_resumption_native` は、この失敗ケースの終盤では直接出てこない。
`.once` の queue replay は `ApplyClosure(Resumption)` 経由で
`yulang_cps_resume_i64` に入る。

失敗の終盤は、outer `.once` の prompt 1 が見つからないのではなく、
prompt 1 へ届く値がすでに `:just 3` になっている。

代表 trace:

```text
make_resumption: id=7 ... frames=[
  F#0/id25:k34(owner_eval=8,owner_fn=31,init=4, handlers=[h5,h0]),
  F#1/id26:k1(owner_eval=201,owner_fn=15,init=0,prompt_exit=7, handlers=[h5,h0,h1]),
  F#2/id27:k15(owner_eval=201,owner_fn=15,init=0, handlers=[h5,h0,h1]),
  F#3/id28:k1(owner_eval=205,owner_fn=14,init=2, handlers=[h5,h0,h1]),
  F#4/id29:k14(owner_eval=224,owner_fn=15,init=4, handlers=[h5,h0,h1])
]
resume: anchor=prompt 1 ... adjusted_frames=5
continue_return_frame: id=25 owner_eval=8 owner_initial=0 value=3
...
continue_return_frame: id=4 owner_eval=7 owner_initial=3 value=:just 3
```

`k34 -> k35 -> k27` は if then branch の `y` 値を返す continuation。
`point { x: 3, y } .norm2` は外側の `k36` にある。
失敗時の resumption には `k34` 以降は入っているが、`k36` は replay される前に
`.once` の value arm が `3` を `:just 3` に包んでいる。

## 入れた小さい parity 修正

JIT の `capture_native_i64_return_frames_from_start` は、CPS eval / CPS repr eval と違い、
captured return frames の `owner_initial_frame_count` を 0 に正規化していなかった。

CPS eval / repr eval 側:

```text
own_captured_return_frames(...)
```

JIT 側も同じ規則に寄せた。
これは対象を直接直さないが、captured resumption frame を元の live caller stack から
独立させるという既存 interpreter 側の不変条件とのズレなので残す。

## 試したが外れた仮説

### `yulang_cps_resume_i64` 内の route を消す

`ApplyClosure(Resumption)` の呼び出し側にも `dispatch_scope_return` があるため、
resume 内で route するのが早すぎる可能性を試した。

結果:

- `runs_junction_method_undet_once_through_cps_repr` は `:just 3` のまま
- `runs_junction_condition_once_through_cps_repr` は通る
- `return_hygiene` は通る

対象に効かず、責務も広げるため戻した。

### routed jump の pending frames を push 前に戻す

`id25:k34` は `owner_initial=4` なのに `len_before=0` で push される。
そこで `NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES` を push 前に戻す仮説を試した。

結果:

- pending がこの局面では存在せず、`id25` は `len_before=0` のまま
- 対象は `:just 3` のまま

この経路では pending routed jump ではなく、より前の thunk force / ordinary return-frame
復元で `k36` がすでに消えている。

### thunk force の普通値フローで caller frame snapshot を広く戻す

`force_thunk_i64` の普通値フローで、消費された caller prefix を復元する方向を試した。

結果:

```text
":just :just <壊れた payload>"
```

全面 restore でも、`initial_frame_count` で caller prefix だけ守る restore でも、
値が二重に wrap され、payload も壊れる。つまり単純な frame 復元は原因側の規則ではない。
`k36` を戻すだけでは、すでに value arm に入った `:just 3` を外側 continuation に再投入してしまう。

## 次の本命

`k36` が capture に入らない原因は、return-frame stack 復元だけではなく、
outer `.once` の handler arm が「resume continuation をどこまで含めるか」の境界にある。

次は次の 2 点を見る。

1. prompt 1 の handler arm が `sub::return 3` を受けたとき、
   handler の value arm が wrap する前に `k36` へ resume する構造になっているか。
2. JIT の `route_scope_return_i64` が frame-walk match 後、
   handler escape を `RoutedJump` として遅延する条件で、CPS eval / repr eval の
   `CpsRoutedJump` と同じ `return_frames` / `initial_frame_count` を持てているか。

特に、CPS dump 上では:

```text
k34: EffectfulForce(thunk=y_candidate, resume=k35)
k35: Continue(k27, y)
k27: Return(y)
k36: point { x: 3, y } .norm2
```

なので、`k27` の Return が outer `.once` に届く前に `k36` を再開するための
frame-walk / routed jump の不変条件を eval/repr と並べて見るのが次の作業。
