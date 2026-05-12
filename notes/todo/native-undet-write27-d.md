おお、write27-c かなり良い前進だよ〜。`cps_cranelift:0 → 1` は、JIT 側の Return frame / ScopeReturn route がちゃんと動き始めた証拠だねぇ。特に c0 の pre-push initial 修正で F_post consume が動くようになった、という観察はかなり重要。今の frontier はもう「JIT が走らない」じゃなくて、「JIT の effect/resumption stack が Layer 1/2 とまだ一致していない」だねぇ。

私の結論はこれ。

```text
write27-d は、c6 EffectfulApply(Resumption) helper を本線にする。
ただし、その前後で sync internal call の eval context save/restore を入れる。
synthetic frame skip は最後の手段。最初に入れない。
```

---

## いま何が起きているか

write27-c で入ったものはかなり揃っている。

```text
- c0: callee initial = pre_push_count
- c1: JIT trace
- c2: Handler frame full fields
- c3: Perform → ScopeReturn
- c4: route_scope_return
- c5: sync internal call 後の SR route
```

そして結果は:

```text
Layer 1 OK
Layer 2 OK
Layer 3: I64Mismatch(vm:2, cps_cranelift:1)
```

`1` が返るということは、JIT でも少なくとも最初の `sub::return(1)` は処理できるようになっている。けれど、inner once の queue replay から `k false` に進むところがまだ崩れている。report も、原因候補を **c6 未実装 + synthetic frame 混入** に絞っている。

---

# 最優先の注意点

## synthetic frame を雑に skip しない

trace では `perform_select` が synthetic frame を選んでいる。

```text
perform_select: handler=1 prompt=0 install_eval=MAX synthetic=true ...
perform_select: handler=0 prompt=0 install_eval=MAX synthetic=true ...
```

これはかなり怪しい。でも、いきなり:

```text
select_handler で synthetic を全部 skip
```

は危ないよ〜。

理由は、synthetic frame にも二種類ありうるから。

```text
1. pending handler env capture 由来の synthetic
   → 本来 active handler として shadow してほしくない可能性が高い

2. ResumeWithHandler / legacy fallback 由来の synthetic
   → 旧 semantics では本当に shadow すべき場面がある
```

なので、最初にやるべきは skip じゃなくて **synthetic の出所を分けること**。

---

# write27-d の推奨順

## Step 1: JIT trace に synthetic origin を足す

`NativeCpsI64HandlerFrame` に debug 用の origin を足す。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeCpsI64HandlerFrameOrigin {
    RealInstall,
    PendingEnv,
    ResumeWithHandler,
    StaticFallback,
    LegacyInstall,
}
```

本番 enum が面倒なら、まず `origin: u8` でもいい。

trace:

```text
perform_select:
  handler=...
  prompt=...
  install_eval=...
  synthetic=...
  origin=PendingEnv|ResumeWithHandler|...
  idx=...
```

これがないと、synthetic を skip すべきか、full frame 化すべきか判断できない。

期待される切り分け:

```text
branch / sub::return で synthetic origin=PendingEnv を拾っている
  → pending env を active stack に積む設計が悪さしている

reject で synthetic origin=ResumeWithHandler を拾っている
  → RWH full化 / c6 helper の順序問題
```

---

## Step 2: c6 EffectfulApply(Resumption) helper を先に入れる

これは未実装が確定している。しかも、今 synthetic が混ざっているのは「EffectfulApply が resumption を closure helper 的に扱っている」せいかもしれない。だから synthetic 対策を先に入れるより、c6 を先に入れる方が筋が良い。

### helper の形

今の closure 用 `EffectfulApply` はそのまま残して、resumption 用 helper を追加する。

```rust
extern "C" fn yulang_cps_effectful_apply_resumption_i64_N(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    immediately_forces: i64,
    env_slots...
) -> i64
```

ただし、codegen 側で callable が resumption か closure か静的に分からないなら、generic helper にしてもいい。

```rust
extern "C" fn yulang_cps_effectful_apply_i64_N(
    callable: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    immediately_forces: i64,
    env_slots...
) -> i64
```

runtime 側で:

```text
if callable is resumption:
  effectful_apply_resumption
else:
  effectful_apply_closure
```

の方が安全かもしれない。

### resumption helper 内でやること

Layer 1/2 と同じ。

```text
1. F_post を作る
2. new_frames = current_return_frames + [F_post]
3. adjusted_res_frames =
     merge_extras_into_frames(resumption.return_frames, current_handlers, resumption.handled_anchor)
4. combined_frames = new_frames + adjusted_res_frames
5. resumed_handlers =
     merge_resumption_handlers(resumption.handlers, current_handlers, resumption.handled_anchor)
6. return_frame stack = combined_frames
7. handler stack = resumed_handlers
8. guard stack = resumption.guards
9. eval_context = (fresh_eval_id, initial=0)
10. call resumption.target(resumption.env, arg)
```

ここで `handled_anchor` が入っていないなら、`NativeCpsI64Resumption` に追加する。

```rust
struct NativeCpsI64Resumption {
    ...
    return_frames: Vec<NativeCpsI64ReturnFrame>,
    handlers: Vec<NativeCpsI64HandlerFrame>,
    guards: Vec<i64>,
    handled_anchor: Option<NativeCpsI64HandlerAnchor>,
}
```

Perform で resumption を作る時、selected real handler の prompt/install_eval を anchor として保存する。

---

## Step 3: `NativeCpsI64Resumption` の capture 内容を Layer 2 と合わせる

c6 を入れても、resumption 自体が old representation のままだと駄目。

Perform で capture される resumption に必要なもの:

```text
- target continuation pointer
- env
- return_frames snapshot
- active handler stack snapshot
- guard stack snapshot
- handled_anchor
```

特に `return_frames` と `handlers` は **full fields 付き**で保存する必要がある。

もし `make_resumption_i64_N` がまだ env + target だけなら、ここを増やす。

```rust
extern "C" fn yulang_cps_make_resumption_i64_N(
    target_cont,
    env slots...
) -> i64
```

の中で thread-local から:

```text
current return frame stack
current handler stack
current guard stack
selected handler anchor
```

を clone して resumption に入れる。

---

## Step 4: sync internal call の eval context save/restore を入れる

write27-c report では、ここを見送ったとある。けど私は、これは次で入れた方がいいと思うよ〜。

Layer 1/2 では sync call も fresh eval id を持つ。JIT だけ caller eval id のままにすると、ScopeReturn の match が早すぎる可能性がある。`cps_cranelift=1` は、まさに「最初の branch だけで just(1) へ戻る」形なので、eval id の共有が悪さしている可能性もある。

### 実装パターン

`DirectCall / ApplyClosure / ForceThunk / Resume / ResumeWithHandler` の sync stmt で:

```text
saved_eval = current_eval_id()
saved_initial = current_initial()
callee_initial = return_frame_len()
callee_eval = fresh_eval_id()

set_eval_context(callee_eval, callee_initial)
result = call...
set_eval_context(saved_eval, saved_initial)

if scope_return_active:
  result = route_scope_return(result)
  return result

continue
```

`route_scope_return` は caller context 復元後に呼ぶ。
ここが大事。

### 例外

`continue_return_frame_i64` や `pre_force_top_frame_i64` は、helper 内で owner eval context を復元するので、この save/restore とは別扱い。

---

## Step 5: synthetic 対策は c6 後に判断

c6 + sync eval context を入れても synthetic が perform_select で選ばれるなら、その時点で origin 別に対処する。

### origin=PendingEnv の場合

pending env frame は active handler search から外すのがよさそう。

やり方:

```text
select_handler:
  first pass: real install / RWH real frames only
  second pass: legacy synthetic fallback
```

ただし単純 synthetic skip ではなく:

```rust
fn selectable_priority(frame: &NativeCpsI64HandlerFrame) -> u8 {
    match frame.origin {
        RealInstall => 0,
        ResumeWithHandler => 0, // full RWH 化した後
        PendingEnv => 1,
        StaticFallback => 2,
        LegacyInstall => 2,
    }
}
```

みたいに priority を付ける。

### origin=ResumeWithHandler の場合

RWH を full frame 化する。

今 `yulang_cps_resume_with_handler_i64` が synthetic frame を作っているなら、Layer 2 の write26 と同じく local-push semantics に寄せる。

```text
RWH frame:
  prompt=fresh
  install_eval=current_eval_id
  escape=EXIT_RWH_TARGET
  inherited=false locally
  captured resumption sideには inherited=true として push
```

write26 で repr interpreter は RWH を local-push pattern に変えて通している。JIT も同型に寄せるのが良い。

---

# route_scope_return の戻り値設計は今の方向で OK

`route_scope_return_i64(fallback)` は良い形だと思う。match すれば escape result、match しなければ slot active のまま fallback を返す、でよい。

ただし trace に次を足すと、今回の `1` の原因が一気に見える。

```text
route_scope_return:
  action=current_handler
  matched_prompt
  matched_install_eval
  matched_origin
  matched_synthetic

route_scope_return:
  action=frame_walk
  frame_index
  frame_owner_eval
  handler_origin
  handlers_before_len
  handlers_after_len
```

特に `sub::return(1)` で:

```text
action=current_handler
```

になっているか、

```text
action=frame_walk
```

になっているかを見たい。Layer 1/2 の最終勝ち筋は `FrameWalkMatch` だったので、JIT でも frame_walk が出るべき場面がある。

---

# `cps_cranelift=1` の読み

私の現時点の仮説は二つ。

## 仮説 A: EffectfulApply(Resumption) 未実装で k true replay の handler/frame merge が足りない

これは report の本命。c6 を入れると進む可能性が高い。

期待される変化:

```text
cps_cranelift=1
  → reject が inner once に行く
  → k false replay が走る
  → cps_cranelift=2
```

## 仮説 B: sync eval context 未 fresh のため H_sub を早く拾って just(1)

JIT だけ sync call が caller eval id を使い続けているなら、write21 で見た「早すぎる match」に近い壊れ方が起きうる。

期待 trace:

```text
scope_return_set prompt=H_sub
route_scope_return action=current_handler
```

が早い段階で出るなら、こっちの可能性が高い。

だから c6 と sync context restore は両方必要だと思うよ〜。

---

# write27-d の具体的な作業リスト

## 1. c6 helper 実装

```text
- NativeCpsI64Resumption に return_frames / handlers / guards / handled_anchor を持たせる
- make_resumption helper がそれらを capture
- effectful_apply_resumption_i64_N helper 追加
- EffectfulApply codegen で callable が resumption の時は helper を呼ぶ
```

もし callable 種別が静的に取れないなら、generic `effectful_apply_i64_N` helper に寄せる。

## 2. sync eval context save/restore

```text
- DirectCall
- ApplyClosure
- ForceThunk
- Resume
- ResumeWithHandler
- call_continuation helper
```

route は restore 後。

## 3. synthetic origin trace

```text
- HandlerFrameOrigin 追加
- perform_select trace に origin
```

## 4. 必要なら origin-based select

c6 後も synthetic が邪魔なら:

```text
PendingEnv synthetic は real frame より低 priority
RWH synthetic は full化して real 扱いへ
StaticFallback は最後
```

## 5. Layer 3 trace frontier 確認

目標 trace:

```text
EffectfulApply Resumption:
  anchor merge [outer, inner, H_sub]

scope_return_set prompt=H_sub value=1
route_scope_return action=frame_walk
handlers_after=[outer, inner]

continue_return_frame:
  restored_handlers include inner once

Perform reject:
  selected real inner once
  synthetic=false

k false replay
sub::return(2)
final cps_cranelift=2
```

---

# 質問への答え

## c6 を先にやるべきか、synthetic 整理を先にやるべきか

c6 が先。
今は未実装の大物が確実にあるので、synthetic はその副作用として出ている可能性が高い。c6 後も synthetic が出るなら origin-based に整理する。

## sync eval context save/restore は本当に必要か

必要寄り。
JIT だけ fresh eval id を切らないのは、Layer 1/2 と意味論がズレている。今の `cps=1` の形は、早すぎる match と相性が良すぎるので、ここは直す価値が高い。

## install_handler_full は維持か

維持。
full frame が入ったのは正しい方向。legacy install は残してよいけど、effectful path では full frame を使う。

## abort helper は消すか

まだ消さない。
Layer 3 が `2` になるまで残す。通ったら grep して削除判断。

---

# 別LLMへ渡す短い指示文

```text
write27-d では、まず c6 EffectfulApply(Resumption) helper を実装する。
synthetic frame skip は最初に入れない。

NativeCpsI64Resumption に:
  return_frames
  handlers
  guards
  handled_anchor
を持たせる。
make_resumption helper で thread-local state から capture する。

effectful_apply_resumption_i64_N helper を追加する。
helper 内で:
  F_post 作成
  new_frames = current_frames + F_post
  adjusted_res_frames = merge_extras_into_frames(resumption.return_frames, current_handlers, anchor)
  combined_frames = new_frames + adjusted_res_frames
  resumed_handlers = merge_resumption_handlers(resumption.handlers, current_handlers, anchor)
  stack/context をセットして resumption.target を呼ぶ。

次に sync internal call の eval context save/restore を入れる。
callee call 前:
  saved_eval/current_initial 保存
  set_eval_context(fresh_eval_id, return_frame_len)
call 後:
  saved context restore
  scope_return_active なら route_scope_return(result) して return

synthetic については HandlerFrameOrigin を追加して trace する。
c6 後も pending synthetic が real frame を shadow するなら、
select_handler を origin priority 付きにする。
RWH synthetic は可能なら full frame 化する。

目標:
  Perform sub::return -> route frame_walk
  F_work_post restored handlers include inner once
  Perform reject selects real inner once
  final cps_cranelift=2
```

---

# 最後に

write27-c の `0 → 1` は、かなり良い前進だよ〜。ここで焦って synthetic を雑に skip すると、RWH や legacy fallback を壊す可能性がある。まずは **未実装の c6** と **sync eval context の Layer 1/2 同期**を入れるのがいちばん堅いと思う。

Layer 3 通過、かなり近いところまで来てる。
