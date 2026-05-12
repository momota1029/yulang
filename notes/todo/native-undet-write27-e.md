読んだよ〜。write27-d、値だけ見ると `1 → 0` だけど、これは report の読み通り **legacy synthetic 経由の偶然 1 から、real ScopeReturn / resumption / anchor merge の本筋へ移った**状態に見える。だから後退というより、いよいよ本物の最後のズレが見えてきた感じだねぇ。d1〜d6 を全部入れて、既存 167 tests と local choice が pass のままなのもかなり良い。

ただ、次の一手については report の「escape continuation 後の inner-handler 再構築」へすぐ飛ぶ前に、私は **handler stack order / eval context の不変条件をもう一回強く見る**方がいいと思うよ〜。

---

## いちばん重要な違和感

report ではこうなっている。

```text
route_scope_return:
  action=current_handler match at current_eval=6 initial=3
  → handler stack truncate
  → inner once prompt=3 も消える
```

でも Layer 1/2 の勝ち筋では、`sub::return` はだいたいこの流れだったねぇ。

```text
Resume eval で sub::return
  current eval では matched=no
  return_frames を walk
  modified F_each_post で H_sub に match
  handlers_before=[outer, inner, H_sub]
  handlers_after=[outer, inner]
```

つまり JIT でも本来は、少なくともこの局面では **current_handler match ではなく frame_walk match** が出てほしい。あるいは current_handler match でも stack が `[outer, inner, H_sub]` になっていて、truncate 後に inner once が残る必要がある。

今は inner once が消える。これは次のどちらかだと思う。

```text
A. route の時点の handler stack order が [outer, H_sub, inner] になっている
B. current_eval_id が H_sub install eval と一致してしまっていて、frame_walk 前に current match している
```

どちらにせよ、「escape 後に再構築する」より前に、**なぜ Layer 1/2 と違って current_handler match しているのか**を詰めたい。

---

# write27-e の推奨順

## 1. まず trace を増やして不変条件を見る

次の trace を必ず出すのがよさそう。

### `effectful_apply_resumption_native`

今も trace はあるけど、もっと具体的に。

```text
effectful_apply_resumption:
  anchor=(prompt, eval)
  captured_handlers=[...]
  current_handlers=[...]
  resumed_handlers=[...]
  adjusted_frame[each].handlers=[...]
  combined_frames=[owner/eval/handlers...]
```

ここで期待はこれ。

```text
captured=[outer, H_sub]
current=[inner]
anchor=outer
resumed_handlers=[outer, inner, H_sub]
```

もしここが `[outer, H_sub, inner]` なら、c6 helper の merge が Layer 2 とズレている。

### `scope_return_set`

```text
scope_return_set:
  prompt=<H_sub>
  current_eval=<...>
  current_initial=<...>
  current_handlers=[...]
  return_frames=[...]
```

期待は:

```text
current_handlers=[outer, inner, H_sub]
```

また、`current_eval` は H_sub install eval そのものではなく、resumption replay 側の fresh eval である方が自然。

### `route_scope_return`

current-handler match の前に、候補を全部出す。

```text
route_scope_return current scan:
  sr_prompt=...
  current_eval=...
  stack=[
    idx=0 prompt=... install_eval=... origin=...
    idx=1 ...
  ]
  matched_idx=...
```

これで「H_sub が inner より前にいるのか」「eval id がなぜ一致しているのか」が見える。

---

## 2. current_handler match を一時的に抑制して frame_walk を観察する

デバッグ用に一回だけ、次の env flag を足すとかなり効くと思う。

```text
YULANG_CPS_JIT_FORCE_FRAME_WALK_SR=1
```

この flag がある時だけ、`route_scope_return_i64` の current-handler scan を skip して、return-frame walk から始める。

期待する観察:

```text
frame_walk match:
  frame_owner=each
  frame_owner_eval=<H_sub install eval>
  handlers_before=[outer, inner, H_sub]
  handlers_after=[outer, inner]
```

これが出て `cps_cranelift=2` に近づくなら、問題は current-handler match の早すぎる発火だねぇ。

逆に frame_walk でも `handlers_before=[outer,H_sub]` しかないなら、effectful_apply_resumption の modified frame injection がまだ足りない。

この flag は commit 前に消してもいいし、trace-only debug guard として残してもいい。

---

## 3. c6 helper の merge 結果を Layer 2 と完全一致させる

d4 で `merge_resumption_handlers_native` / `merge_extras_into_frames_native` は Layer 2 から port 済みとある。ここは良い方向。

ただ、JIT では thread-local handler stack が 1 本なので、helper の merge 結果を **本当に thread-local stack にセットした後、途中で別 helper が pending synthetic / install_handler_full 由来の stack を append していないか**を見る必要がある。

`effectful_apply_resumption_native` の最後で:

```rust
NATIVE_CPS_I64_HANDLERS = resumed_handlers
```

したあと、resumption target を呼ぶ直前に trace:

```text
before resumption call:
  handlers=[outer, inner, H_sub]
```

を出す。

そして `sub::return` の `perform_select` 直前に:

```text
before perform_select:
  handlers=[outer, inner, H_sub]
```

これが変わっているなら、その間の `InstallHandler` / `take_pending` / `ForceThunk` が stack を壊している。

---

# 「escape 後の再構築」案について

report は次の候補を挙げている。

```text
1. escape 先で必要な handler を return_frame snapshot から再構築
2. SR escape を再 eval に近づける
3. truncate をやめて matched frame だけ抜けた扱いにする
```

私は、これらはまだ早いと思う。特に 3 は危ない。

## truncate をやめる案は危険

Layer 1/2 では `active_handlers.truncate(index)` が基本。H_sub の scope を抜けるなら、H_sub 自体とその内側は消す必要がある。

今回 inner once が消えるのは、たぶん **inner once が H_sub の内側に置かれてしまっている**から。
意味論上は inner once は H_sub の外側なので、正しい stack は:

```text
[outer, inner, H_sub]
```

で、truncate(H_sub index) なら inner once は残る。

だから fix は「truncate をやめる」ではなく、まず **stack order を正しくする**方が自然。

## escape 先で再構築する案は最後の手段

もし JIT の global thread-local design の都合で、どうしても current_handler match が起きてしまうなら、escape call 前に handler stack を `frame.active_handlers[..handler_index]` へ入れ替える案はあり。

ただしその場合も、「どの frame snapshot を採用するか」が本質になる。Layer 1/2 に一番近いのは:

```text
current handler stack ではなく、
matched return frame の modified active_handlers を使って escape する
```

つまり結局 frame_walk ベースに寄せることになる。

---

# 具体的な次手

## Step A: current match の条件を厳しくする

JIT の `route_scope_return` current-handler path に、次の条件を追加してみる価値がある。

```rust
handler.origin == RealInstall || handler.origin == ResumeWithHandler
```

これはもうほぼ入っていそうだけど、さらに:

```rust
handler.install_eval_id == current_eval_id
&& handler.escape_continuation != 0
&& !handler.inherited
```

Layer 1/2 の strict check は `install_eval_id == current_eval_id` が主だけど、JIT の thread-local stack では inherited full frame が混じりやすい。`inherited=false` を current-handler match 条件に足すと、resumption replayに持ち込まれた H_sub を current handler として早く拾うのを避けられる可能性がある。

ただし Layer 1/2 では write21 以降 `inherited` は primary check から外れたので、これは JIT 固有の guard。入れるなら trace 付きで慎重に。

私ならまず debug flag で:

```text
current-handler scan excludes inherited
```

を試す。

期待:

```text
current_handler match しない
frame_walk match する
inner once が残る
```

これが効くなら、JIT の inherited marker を current route に使う設計があり。

---

## Step B: route order を「frame_walk 優先」にする条件を作る

常に frame_walk 優先は危険かもしれない。でも、current eval が resumption replay 由来なら frame_walk 優先が Layer 1/2 に近い。

判定に使えそうな条件:

```text
return_frames.len() > current_initial
```

かつ

```text
scope_return prompt の matching handler が current stack にあるが、
その handler より後ろに origin=RealInstall の sibling handler がある
```

この場合、current stack match で sibling を消す危険があるので、frame_walk 優先。

擬似:

```rust
let current_match = find_current_match();

if current_match_exists
   && has_real_handler_after_match(current_match.index)
   && has_frame_walk_match() {
    use frame_walk_match;
} else {
    use current_match;
}
```

これは少し heuristic だけど、今回の状況には刺さる。

ただ、最初から実装するより、まず trace と debug flag で効果を見るのがいい。

---

## Step C: sync eval context の fresh 化が効いているか再確認

d5 で全 sync call を fresh eval id + restore で囲んだのは正しい。

でも helper 内で Rust から直接 continuation を呼ぶ箇所がある。

```text
continue_return_frame_i64
pre_force_top_frame_i64
effectful_apply_resumption_native
route_scope_return_i64 escape call
```

これらは Cranelift codegen の `enter_callee_eval_context` を通らない。だから helper 内で eval context を正しくセットする必要がある。

特に:

```text
effectful_apply_resumption_native:
  set_eval_context(fresh_eval, 0)

route_scope_return current_handler match:
  escape continuation call の前に何を set するか
```

ここを trace で見る。

期待:

```text
effectful_apply_resumption:
  set_eval_context fresh_eval != H_sub.install_eval

sub::return:
  current_eval = fresh replay eval

route:
  current_handler no match
  frame_walk match H_sub owner eval
```

もし current_eval が H_sub install eval になっているなら、どこかの helper が owner eval を早く復元している。

---

# `PendingEnv` synthetic 対策について

d6 で PendingEnv を 2nd pass に降格したのは良い。`perform_select` が全部 `RealInstall` を選ぶようになったなら、PendingEnv 由来の shadow はかなり解消した。

なので次に synthetic へ戻るより、今は real path の stack order / route order を直す方が優先。

---

# write27-e の短い指示文

別LLMへ渡すならこう。

```text
write27-e では、まず route_scope_return の current-handler match が
Layer 1/2 と同じ frontier になっているか確認する。

期待:
  sub::return inside resumption replay:
    current-handler match ではなく frame_walk match
    or current stack=[outer, inner, H_sub] で H_sub match

現状:
  current-handler match at H_sub
  truncate で inner once が消える

最初に trace を足す:
  effectful_apply_resumption resumed_handlers
  before resumption target call handler stack
  before perform_select handler stack
  scope_return_set current_eval/current_handlers
  route current scan candidates
  route frame_walk candidates

次に debug flag を足して current-handler route を skip し、
frame_walk route で cps_cranelift が 2 に近づくか見る。
もし効くなら、route order / inherited guard / resumption replay 判定を入れる。

current-handler path に inherited=false 条件を足す候補も試す。
resumption replay に持ち込まれた handler を current handler として
早く拾わないため。

truncate をやめる案はまだ入れない。
正しい stack order [outer, inner, H_sub] なら truncate で inner は残る。
まず stack order / route order を直す。
```

---

# 質問への答えっぽくまとめると

## 1. escape 後の handler 再構築を先にやるべき？

まだ早いと思う。
まず current match がなぜ起きているかを見る。Layer 1/2 では frame_walk が勝ち筋だった。JIT だけ current match しているなら、そこがズレ。

## 2. truncate をやめる設計は？

危ない。
H_sub scope を抜けるなら H_sub は消す必要がある。inner once が消えるのは truncate 自体ではなく、inner once が H_sub より内側扱いになっていることが問題。

## 3. c6 は入ったので次は synthetic？

PendingEnv shadow は d6 でかなり解けた。次は synthetic より **real path の order / eval context**。`perform_select` が RealInstall を選んでいるなら、synthetic は今の主因ではなさそう。

---

# 最後に

write27-d はかなり良いよ〜。`cps:1 → 0` は値だけだと悲しいけど、内容は完全に「本物の経路に入った」前進だねぇ。

次の急所はこれ。

```text
sub::return の SR は、JIT でも frame_walk で modified F_each_post を使うべき。
current_handler match で stale/global stack を truncate しているなら、
そこを route order / eval context / inherited guard で止める。
```

ここが直ると、inner once が残って reject を拾い、`k false` replay に進むはず。Layer 3 通過、かなり近いところまで来てる。
