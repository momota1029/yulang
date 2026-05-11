見たよ〜。write22、かなり良い進み方だねぇ。数値は `cps:1 → cps:0` に戻っているけど、これは「悪い後退」じゃなくて、write21 のゆるい function-name match を外して、本物の壊れ方が見えるようになった状態だと思うよ〜。

write22 の要点は、`CpsEvalId`、`CpsHandlerFrame.install_eval_id`、`CpsReturnFrame.owner_eval_id` を入れて、`handle_scope_return` を `install_eval_id == current_eval_id` の strict 判定へ変えたこと。local choice 系も既存 167 tests も pass しているので、土台としてはかなり健全。`cps_eval.rs` 側でも strict check と `owner_eval_id` 復元方針が入っているのを確認したよ〜。

## いまの見立て

write22 後のバグは、もう **「H_sub をどこで拾うか」ではない**ねぇ。

そこは直っている。

```text
sub::return in Resume eval
  eval=24 では prompt=1 matched=no
  ...
  eval=8 で install_eval=8 と一致して matched=yes
```

この trace はかなり強い証拠だよ〜。`H_sub` は元の `each` eval で拾えている。

次の本体はこれ。

```text
H_sub による abort のあと、
work cont 1 が guard(false) → reject を perform する時、
inner once prompt=2 が active_handlers に残っていない
```

write22 report の通り、reject 時点の `active_handlers=[outer once only]` になっている。だから queue=[k1] を持つ recursive once ではなく、queue=[] の outer once が reject を拾って nil → 0 になる。

---

# write23 への結論

私なら write23 は、レポートの「案 A + 案 B」をそのまま始めるより、少し順番を調整する。

## 推奨順

```text
1. handler stack merge order を直す / trace で確定する
2. write17 pre-force を「top frame owner context dispatch」方式で再試行する
3. それでも inner once が消えるなら ScopeReturn に preserved_handlers を持たせる
```

理由は、write22 trace のこの形がかなり怪しいから。

```text
active_handlers=[(0,T,1),(1,T,0),(2,T,1)]
```

ここで `0 = outer once`, `1 = H_sub`, `2 = inner once` だねぇ。

でも意味論的には、recursive once の handler は resumed continuation の **外側** にあるはず。つまり stack order はたぶんこうであるべき。

```text
[outer once, inner once, H_sub]
```

今はこう。

```text
[outer once, H_sub, inner once]
```

この順番だと `H_sub` に match した瞬間に `truncate(index_of_H_sub)` で inner once が消える。だから、write22 report の案 C は「単なる補助案」じゃなく、かなり本命に近い確認ポイントだと思うよ〜。

---

# 実装LLMへ渡す具体手順

## Step 0: baseline を固定する

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture

YULANG_CPS_TRACE_FRAMES=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待される現状:

```text
167 pass
local choice caller rest: pass
local choice callback rest: pass
std_undet_once_skip_eval_layers:
  VM  = Int("2")
  CPS = Int("0")
```

ここが違ったら、write22 report と現在の branch がずれている可能性あり。

---

## Step 1: trace を handler merge に寄せる

まず追加 trace。ここは修正前に必ず入れるといいよ〜。

### 1. `summarize_handler_stack`

既に handler stack summary があるなら、次の情報を必ず含める。

```text
prompt
inherited
install_eval_id
escape_owner_function
return_frame_threshold
```

表示例:

```text
[(p=0,inh=T,eval=4,owner=once,thr=1),
 (p=1,inh=T,eval=8,owner=each,thr=0),
 (p=2,inh=T,eval=22,owner=once,thr=1)]
```

### 2. Resume / ApplyClosure(Resumption) / ResumeWithHandler 前後

次を出す。

```text
ResumeHandlerMerge:
  fn=<current fn>
  eval=<current_eval_id>
  captured_handlers=<resumption.handlers>
  current_handlers=<active_handlers at resume site>
  extras=<computed extras>
  merged_handlers=<final resumed_handlers>
```

### 3. `inject_extra_handlers`

各 return frame について:

```text
InjectExtraHandlers:
  frame_owner=<owner_function>
  frame_owner_eval=<owner_eval_id>
  before=<frame.active_handlers>
  current=<resume site active_handlers>
  after=<merged frame.active_handlers>
```

この trace で、`[outer, H_sub, inner once]` になっているか、`[outer, inner once, H_sub]` になっているかを見る。

---

## Step 2: handler merge order を直す

今の実装が「captured handlers に extras を末尾 push」なら、そこを変える。

### 期待する merge

captured continuation 側:

```text
captured = [outer once, H_sub]
```

resume site 側:

```text
current = [outer once, inner once]
```

期待する merged:

```text
merged = [outer once, inner once, H_sub]
```

つまり、current/resume-site の handler は、captured continuation の inner handlers より **外側** に入る。

### 実装イメージ

```rust
fn merge_resumption_handlers(
    captured: &[CpsHandlerFrame],
    current: &[CpsHandlerFrame],
) -> Vec<CpsHandlerFrame> {
    let mut shared = 0;
    while shared < captured.len()
        && shared < current.len()
        && captured[shared].prompt == current[shared].prompt
        && captured[shared].install_eval_id == current[shared].install_eval_id
    {
        shared += 1;
    }

    let mut merged = Vec::new();

    // shared outer prefix
    merged.extend(captured[..shared].iter().cloned());

    // resume-site handlers that are not already in captured
    for frame in &current[shared..] {
        if !captured.iter().any(|c| {
            c.prompt == frame.prompt
                && c.install_eval_id == frame.install_eval_id
        }) {
            merged.push(frame.clone());
        }
    }

    // captured continuation's inner handler tail
    merged.extend(captured[shared..].iter().cloned());

    merged
}
```

この関数を使う場所は二つ。

```text
1. Resume / ApplyClosure(Resumption) / ResumeWithHandler の resumed_handlers 作成
2. inject_extra_handlers で return frame.active_handlers を更新するところ
```

片方だけだと壊れる可能性が高い。resumed eval の live handler stack と、captured return frame 側の handler stack を同じ merge rule に揃える。

### この修正後の期待 trace

```text
Perform sub::return ... active_handlers=[outer once, inner once, H_sub]
ScopeReturnDispatch prompt=1 matched at eval=8
after JumpOrExit active_handlers should keep [outer once, inner once]
Perform reject ... active_handlers includes prompt=2
```

もしここで `cps:2` まで行くなら、write23 はかなり小さく終わる。

---

## Step 3: write17 pre-force を再試行する。ただし「そのまま戻す」のは危ない

write17 の pre-force helper は、当時 `H_sub.escape_owner_function = each` なのに pre-force eval の `current_function = fold_impl` で owner check が合わず、escape して disabled になった。これは write17 report に明記されている。

write22 で `install_eval_id` は入ったけど、`escape_owner_function == current_function` の owner check はまだ残っている。だから、単に `current_eval_id = top_frame.owner_eval_id` で thunk owner function を直接走らせても、まだ owner check で落ちる可能性がある。

### やってはいけない形

```rust
// 危ない
resume_continuation(
    module,
    thunk_owner_function, // fold_impl
    thunk.entry,
    ...,
    current_eval_id = top_frame.owner_eval_id, // each eval id
)
```

この形だと:

```text
current_function = fold_impl
H_sub.escape_owner_function = each
```

なので `owner_match=no` になりうる。

### やるべき形

pre-force helper は、thunk body の実行結果を **top frame の owner context** で dispatch する。

概念はこう。

```text
Return(Thunk) before consuming F_each_post
  ↓
top_frame = F_each_post
owner_function = each
owner_eval_id = eval=8
  ↓
thunk body を force する
  ↓
もし ScopeReturn が返ったら、
  fold_impl 文脈ではなく
  each / eval=8 / top_frame.active_handlers で handle_scope_return する
```

つまり write17 report の候補 B:

```text
ScopeReturn を pre-force helper 内で受け取って top_frame の文脈で再 dispatch
```

これが write22 後の自然な再試行だねぇ。

---

## Step 4: pre-force の発火条件を絞る

pre-force は広げすぎると危ない。最初はこの条件だけ。

```text
Return terminator の value が Thunk
かつ
return_frames.len() > initial_frame_count
かつ
top own frame の continuation が「受け取った param を即 ForceThunk する」形
```

既存 helper があるはず。

```rust
return_frame_immediately_forces_param(module, top_frame)
```

write17 で残した helper を使う。

さらに最初の試行では trace guard を強める。

```text
ReturnThunkPreForceCandidate:
  current_fn=fold_impl
  top_owner=each
  top_owner_eval=8
  top_cont=cont12
  enabled=yes/no
```

---

## Step 5: pre-force 実装の安全な骨格

擬似コードとしてはこう。

```rust
if return_frames.len() > initial_frame_count {
    if let CpsRuntimeValue::Thunk(thunk) = &value {
        if let Some(top_frame) = return_frames.last() {
            if return_frame_immediately_forces_param(module, top_frame)? {
                let result = force_thunk_with_frames_retained(
                    module,
                    thunk.clone(),
                    top_frame,
                    return_frames.clone(),
                )?;

                match result {
                    CpsRuntimeValue::ScopeReturn { .. } => {
                        return dispatch_scope_return_in_owner_frame_context(
                            module,
                            result,
                            top_frame,
                            return_frames.clone(),
                        );
                    }
                    other => {
                        // ここは雑に value として返さない。
                        // top_frame continuation の rest をどう続けるかが必要。
                    }
                }
            }
        }
    }
}
```

大事なのは `other` の扱い。pre-force で plain value が出た場合、それは「top frame の immediate ForceThunk stmt が値を得た」と同じだから、top frame continuation の rest を続ける必要がある。

だから実装としては、単に thunk body だけを force するより、**top frame continuation 自体を owner context で走らせる方式**のほうが一貫するかもしれない。

### 代替のより自然な形

```rust
resume_continuation(
    module,
    top_owner_function,             // each
    top_frame.continuation,         // cont12
    vec![returned_thunk],           // fold_impl returned thunk
    top_frame.values.clone(),
    top_frame.active_handlers.clone(),
    top_frame.guard_stack.clone(),
    return_frames.clone(),          // F_each_post をまだ保持
    return_frames.len(),            // 全 frames を inherited 扱いにして通常 Return では consume しない
    top_frame.owner_eval_id,        // eval=8
)
```

この形だと、`ForceThunk` は `each` 文脈で動き、`ScopeReturn` も `each` の dispatch macro で処理できる。

ただし注意点がある。

```text
return_frames.clone() に top_frame 自身が残っている
initial_frame_count = return_frames.len()
```

にしないと、top frame を自分で consume して二重再開する危険がある。

この方式を試すなら、trace で必ず見る。

```text
PreForceResumeTopFrame:
  top_owner=each
  top_cont=cont12
  passed_frames_len=1
  passed_initial=1
```

期待:

```text
branch perform の resumption.return_frames に F_each_post が含まれる
```

これが pre-force の本当の目的だよ〜。

---

## Step 6: それでも inner once が消えるなら preserved_handlers を入れる

handler merge order と pre-force をやっても、まだ SR propagation が eval=22 を抜けた時に inner once が消えるなら、write22 report の案 B が必要。

### 追加する概念

`ScopeReturn` に「通過中に保存した handler」を持たせる。

```rust
ScopeReturn {
    prompt,
    target,
    value,
    preserved_handlers: Vec<CpsHandlerFrame>,
}
```

既存 constructor が多いなら helper を作る。

```rust
fn scope_return(prompt, target, value) -> CpsRuntimeValue
```

で `preserved_handlers = Vec::new()` を埋める。

### Propagate 時に集める handler

`handle_scope_return` が matched=no で Propagate する直前、現在 eval が install した handler を集める。

```rust
let local_preserved = active_handlers
    .iter()
    .filter(|frame| {
        frame.install_eval_id == current_eval_id
            && frame.prompt != prompt
    })
    .cloned()
    .collect::<Vec<_>>();
```

この条件で inner once prompt=2 は eval=22 を通過する時に拾える。

### match 時に注入する

H_sub に match したら:

```rust
active_handlers.truncate(index);
merge preserved_handlers into active_handlers;
```

注入後の期待:

```text
active_handlers=[outer once, inner once]
```

ただしこれは大きい変更だよ〜。過剰 preservation が起きる可能性があるから、Step 2/3 の後で必要になった時だけやるのがよさそう。

---

# write23 での判断基準

## 成功パターン A: handler merge だけで直る

trace:

```text
ResumeHandlerMerge:
  captured=[outer,H_sub]
  current=[outer,H_inner]
  merged=[outer,H_inner,H_sub]

after H_sub JumpOrExit:
  active_handlers=[outer,H_inner]

Perform reject:
  matched inner once prompt=2

final CPS=2
```

これなら pre-force / preserved_handlers は不要。

## 成功パターン B: pre-force まで必要

trace:

```text
Return(Thunk) in fold_impl:
  PreForceResumeTopFrame enabled
  top_owner=each
  top_owner_eval=8

Perform branch:
  resumption.return_frames includes F_each_post

Resume k true:
  H_sub matches while inner once still active

Perform reject:
  active_handlers includes prompt=2

final CPS=2
```

## まだ失敗するパターン

```text
ScopeReturnDispatch fn=once eval=22 prompt=1 matched=no Propagate
...
Perform reject active_handlers=[outer only]
```

この場合は preserved_handlers が必要。

---

# 私の優先順位

別LLMに渡すなら、こう書くのが一番誤解が少ないと思うよ〜。

```text
write22 の eval_id strict check は維持する。
write21 の function-name exception は戻さない。

write23 ではまず resumption handler merge order を直す。
resume-site handlers は captured continuation の inner handlers より外側に入れる。
具体例:
  captured=[outer,H_sub]
  current=[outer,H_inner_once]
  merged=[outer,H_inner_once,H_sub]

次に write17 pre-force を再試行する。
ただし thunk.owner_function の文脈で ScopeReturn を dispatch しない。
top return frame の owner_function / owner_eval_id の文脈で dispatch する。
可能なら top frame continuation 自体を owner context で走らせ、
F_each_post を return_frames に保持したまま effects を capture させる。

それでも inner once が消えるなら、
ScopeReturn に preserved_handlers を持たせ、
Propagate で通過した intermediate eval が install した handler を
match 後の active_handlers に注入する。
```

---

# 最後に

write22 は「正しいけど結果が悪く見える」典型だねぇ。`cps:1` は意味論的に早すぎる match の産物で、`cps:0` に戻ったことでようやく **inner once handler をどう保存するか** に問題が絞れた。

次の勝ち筋は、私はかなり強くこれだと思う。

```text
handler merge order の修正
+
top-frame owner context での pre-force
```

それで駄目なら preserved_handlers。
いきなり preserved_handlers から入ると、ScopeReturn の意味論を大きく動かすから、まずは順序と pre-force の小さい修正で trace frontier を動かすのがよさそうだよ〜。
