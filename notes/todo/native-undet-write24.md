読んだよ〜。write23 はかなり大きい前進だねぇ。特に **`Return` terminator が inherited prefix を落としていた**のを直して、`F_each_post` が resumption の captured chain に入るようになったのは本物の進展。`frames=1 → frames=2` になったのは、前まで到達できていなかった層へ入った証拠だよ〜。

ただ、次に見るべきところは write23 report の結論から少しだけ変えた方がよさそう。私の一番大きい指摘はこれ。

> `merge_resumption_handlers` の現状 trace `merged=[inner once, outer once, H_sub]` は、handler stack が outer→inner 順なら意味論的に怪しい。

`active_handlers` は `rposition` で innermost を探しているので、配列順は基本的に **outer → inner** だねぇ。すると、

```text
merged=[p2 inner once, p0 outer once, p1 H_sub]
```

は、`reject` search では `p0 outer once` が `p2 inner once` より内側扱いになる。つまり、仮に work eval に `p2` が伝わっても、順序がこのままだと reject は outer once に取られる危険が高い。

なので write24 の最初は、案 A/C へ飛ぶ前に **merge anchor を導入して `[outer once, inner once, H_sub]` を作る**のが良いと思うよ〜。

---

# 現状整理

write23 で達成済み:

```text
- eval-frame identity は維持
- handler merge helper を導入
- RWH は legacy inject 維持
- Return が full return_frames を continue_return_frames に渡す
- F_each_post が captured chain に入る
- 既存 167 tests pass
- local choice 系 pass
```

ここは良い。`handle_scope_return` の strict 判定も現コードで確認できる。`frame.prompt == prompt && frame.install_eval_id == current_eval_id` で、write21 の function-name loose match は消えている。

残り:

```text
sub::return abort 後、
work cont 1 の eval=7 に inner once H が伝わらない
```

write23 trace では、`Perform reject` 時点で:

```text
active_handlers=[outer once]
```

になっている。だから queue=[k1] を持つ inner once ではなく、queue=[] の outer once が reject を拾って `nil -> 0` になる。

---

# write24 の推奨方針

## 優先順位

```text
1. merge_resumption_handlers の順序を anchor-based に直す
2. それでも work eval に inner once が来ないなら、work の DirectCall を effectful 化する
3. SR.preserved_handlers + walk-based propagation は最後の手段
```

私の感触では、write23 report の「案 A + 案 C が現実的」は半分正しいけど、**A+C だけでは work eval=7 に handler を渡せない可能性が高い**。

理由は単純で、`eval=8` の active_handlers を修飾しても、plain value として `each` が return した後、caller の `work eval=7` の active_handlers は別物だからだねぇ。sync `DirectCall` は caller eval をそのまま生かしているので、child eval 側の handler stack 変更が親に伝わらない。

なので、根本的には **work の post-call continuation を return frame 化する**必要がある。これは案 B、つまり targeted `EffectfulCall` lowering が一番クリーン。

ただしその前に、handler merge order の bug っぽいところを潰すのが安全だよ〜。

---

# Step 1: merge order を anchor-based にする

## 問題

write23 trace:

```text
captured=[p0 outer once, p1 H_sub]
current=[p2 inner once]
merged=[p2 inner once, p0 outer once, p1 H_sub]
```

でも欲しいのは:

```text
merged=[p0 outer once, p2 inner once, p1 H_sub]
```

`p2 inner once` は、outer once branch arm 内で install された recursive handler。意味論的には outer once より内側、resumed continuation の `H_sub` より外側に入るべき。

## 解法

resumption に「どの handler arm で作られた resumption か」の anchor を持たせる。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CpsHandlerAnchor {
    prompt: CpsPromptId,
    install_eval_id: CpsEvalId,
}
```

`CpsResumption` に追加:

```rust
handled_anchor: Option<CpsHandlerAnchor>,
```

`Perform` で handler frame を選んだ瞬間に、選ばれた frame の prompt/eval を保存する。

```rust
let handled_anchor = CpsHandlerAnchor {
    prompt: matched_frame.prompt,
    install_eval_id: matched_frame.install_eval_id,
};
```

## anchor-based merge

```rust
fn merge_resumption_handlers(
    captured: &[CpsHandlerFrame],
    current: &[CpsHandlerFrame],
    anchor: Option<CpsHandlerAnchor>,
) -> Vec<CpsHandlerFrame> {
    let same_frame = |a: &CpsHandlerFrame, b: &CpsHandlerFrame| {
        a.prompt == b.prompt && a.install_eval_id == b.install_eval_id
    };

    let is_anchor = |frame: &CpsHandlerFrame, anchor: CpsHandlerAnchor| {
        frame.prompt == anchor.prompt
            && frame.install_eval_id == anchor.install_eval_id
    };

    if let Some(anchor) = anchor {
        if let Some(anchor_index) = captured.iter().position(|f| is_anchor(f, anchor)) {
            let mut merged = Vec::new();

            // captured prefix through handled handler
            merged.extend(captured[..=anchor_index].iter().cloned());

            // handlers installed at resume site / handler arm body
            for frame in current {
                if !merged.iter().any(|m| same_frame(m, frame))
                    && !captured[anchor_index + 1..].iter().any(|c| same_frame(c, frame))
                {
                    merged.push(frame.clone());
                }
            }

            // captured continuation inner tail
            merged.extend(captured[anchor_index + 1..].iter().cloned());
            return merged;
        }
    }

    // fallback: existing shared-prefix merge
    merge_resumption_handlers_by_shared_prefix(captured, current)
}
```

期待:

```text
captured=[outer, H_sub]
current=[inner]
anchor=outer
merged=[outer, inner, H_sub]
```

これを `Resume` / `ApplyClosure(Resumption)` / `EffectfulApply(Resumption)` と、return frame への injection に同じように使う。

`ResumeWithHandler` は write23 の通り legacy 維持でよい。RWH は rebased semantics なので、ここに混ぜない方が安全。

---

# Step 2: Perform handler search trace を追加

merge order を直す前後で、`reject` がどの frame に捕まるかを必ず見たい。

`CpsTerminator::Perform` の handler search 直後に trace を足す。

```text
PerformHandlerSearch:
  fn=<function>
  eval=<current_eval_id>
  effect=<effect path>
  stack=<summarize_handler_stack(active_handlers)>
  matched_index=<index or none>
  matched_prompt=<prompt>
  matched_install_eval=<eval>
  matched_owner=<owner>
```

特に見る値:

```text
effect=std::undet::reject
stack=[outer, inner]
matched_prompt=inner once prompt=2
```

もし stack が `[inner, outer]` なら、outer が勝つはず。ここで一発で分かる。

---

# Step 3: merge order 修正だけで再テスト

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture

YULANG_CPS_TRACE_FRAMES=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待する trace frontier:

```text
ResumeHandlerMerge:
  captured=[outer,H_sub]
  current=[inner]
  anchor=outer
  merged=[outer,inner,H_sub]
```

もしその後:

```text
Perform reject:
  active_handlers includes inner once
  matched_prompt=inner once
```

まで行けば、かなり勝ち。`cps:2` に届く可能性がある。

届かず、まだ:

```text
Perform reject:
  active_handlers=[outer once]
```

なら、merge order ではなく **work eval に inner once が伝わらない問題**が本体。

---

# Step 4: 次は案 B、targeted EffectfulCall lowering

ここは私は report より強く推す。理由は、sync `DirectCall` のままでは、親 eval の handler stack が child eval の結果で更新されないから。

対象はこの形:

```text
work__mono0 cont 1:
  DirectCall each__mono1(list) -> thunk
  ForceThunk(thunk) -> n
  n > 1
  guard(...)
  Return n
```

これは意味論的には、`each` の effect が work の後続計算、つまり `guard; n` を capture しなければならない。sync `DirectCall` ではなく、post-call continuation を return frame にする必要がある。

## 変更方針

`cps_lower.rs` で、次の pattern を targeted に split する。

```text
DirectCall target returns Thunk
かつ
その値が非 Thunk demand により ForceThunk される
```

今はだいたいこう lower されているはず:

```text
DirectCall each(args) -> t
ForceThunk(t) -> n
... rest ...
```

これを:

```text
EffectfulCall {
    target: each,
    args,
    resume: cont_after_call
}

cont_after_call(t):
  EffectfulForce {
      thunk: t,
      resume: cont_after_force
  }

cont_after_force(n):
  ... rest ...
```

にする。

## 重要な制約

全 DirectCall を effectful 化しない。

最初はこの条件に限定:

```text
- callee return type が Thunk
- call result が現在の式文脈で non-thunk value として demanded
- 既存の `force_if_non_thunk_demand` が ForceThunk を挿入するはずの地点
```

つまり、既存の force 挿入地点を terminator split に置き換えるだけ。

## なぜこれで inner once が届くか

EffectfulCall にすると、work の後続が return frame になる。

```text
F_work_post:
  owner_function=work
  continuation=after_each_force / guard path
  active_handlers=[outer once]
```

これが resumption captured chain に入り、Resume site の inner once を merge/inject できる。

期待:

```text
Resume k true under inner once:
  captured frame F_work_post gets active_handlers=[outer,inner]
  each returns 1
  continue_return_frames resumes work post frame
  guard false → reject
  reject matched by inner once
```

これが今の sync `DirectCall` ではできていない。

---

# Step 5: 案 A+C をやるなら必要条件を明示する

`SR.preserved_handlers + walk-based propagation` を選ぶ場合でも、**work eval へ渡す機構**が必須。

単に `ScopeReturn` に:

```rust
preserved_handlers: Vec<CpsHandlerFrame>
```

を持たせて、match site の `active_handlers` に inject するだけでは足りない。

なぜなら:

```text
match site: each eval=8
caller: work eval=7
```

この二つは別 eval。`each eval=8` の `active_handlers` を増やしても、plain return した時点で `work eval=7` には反映されない。

なので A+C で行くなら、さらに次のどちらかが必要。

## A+C+1: eval return に handler delta を持たせる

`eval_continuations` の返り値を `CpsRuntimeValue` から内部用の outcome に変える。

```rust
struct CpsEvalOutcome {
    value: CpsRuntimeValue,
    exported_handlers: Vec<CpsHandlerFrame>,
}
```

`DirectCall` / `ApplyClosure` / `ForceThunk` は、child outcome の `exported_handlers` を自分の `active_handlers` に merge してから続行する。

これは大きい refactor だねぇ。

## A+C+2: `CpsRuntimeValue` に internal wrapper を作る

```rust
CpsRuntimeValue::WithHandlers {
    value: Box<CpsRuntimeValue>,
    handlers: Vec<CpsHandlerFrame>,
}
```

ただしこれは値 domain を汚す。List/Tuple/Variant に紛れたら事故る。やるなら、call boundary で必ず unwrap して、language value として保存しない invariant が必要。

## 判断

A+C は evaluator-only に見えるけど、実際は「handler delta を親 eval に戻す」仕組みが必要。これは案 B の lowering change より分かりにくくなる可能性があるよ〜。

だから私は、write24 では **案 B を本線**に置く方がいいと思う。

---

# Step 6: pre-force は今は後回し

write17 pre-force は、当時 `current_function=fold_impl` と `H_sub.escape_owner_function=each` が合わず escape した。write17 report にその構造が整理されている。

write23 では Return inherited preservation によって、pre-force なしで `F_each_post` が captured chain に入った。なので、pre-force を再び掘る優先度は下がったと思う。

今は:

```text
pre-force で F_each_post を入れる
```

ではなく、

```text
F_each_post は入った
でも work post continuation が return frame ではない
```

が問題。

だから pre-force より targeted EffectfulCall lowering だねぇ。

---

# `りなに渡す質問` への答え

## Q1. 案 A+C か案 B か

私は **案 B が筋が良い**と思うよ〜。

理由:

```text
work cont 1 は sync DirectCall の caller eval として生きている。
child eval 側で preserved_handlers を作っても、親 eval に自然には反映されない。
```

つまり A+C だけだと、結局「handler delta を parent に返す」機構が必要になる。
それは evaluator semantics をかなり複雑にする。

一方、案 B は effectful computation の普通の CPS 変換に近い。

```text
effectful call の後続計算は return frame にする
```

これで work cont 1 が resumption/captured chain に入る。意味論的に素直だよ〜。

## Q2. `merge_resumption_handlers` の current-first logic は妥当か

今の trace の `merged=[inner, outer, H_sub]` は、私は妥当とは言い切れない。

handler stack が outer→inner 順なら、reject search で outer が inner より勝つ危険がある。欲しいのは:

```text
[outer, inner, H_sub]
```

そのためには shared prefix だけでは足りない。`Perform` で捕まえた handler frame を anchor として保存して、extras を anchor の直後へ入れる必要がある。

## Q3. Return inherited preservation の副作用

これは正しい修正に見える。

`Return` が `split_off(initial_frame_count)` して own frames だけを `continue_return_frames` に渡すと、tail-call chain で inherited prefix が消える。sync caller が alive という仮定は、tail-call/return-frame resume では崩れる。write23 の修正で 167 tests が通っているなら、まず維持でよいと思う。

追加するなら、小さい regression test:

```text
effectful tail-call chain の深い側で Perform して、
outer return frame が resumption に残る
```

これを固定すると安心だねぇ。

---

# 別LLMへ渡す短い指示文

```text
write23 の eval_id strict check と Return inherited preservation は維持する。
write21 の function-name loose match は戻さない。
write17 pre-force も今は戻さない。

まず handler merge order を修正する。
現状 trace の merged=[inner once, outer once, H_sub] は handler stack が outer→inner 順なら危険。
Perform で選ばれた handler frame を CpsResumption.handled_anchor として保存し、
Resume / ApplyClosure(Resumption) / EffectfulApply(Resumption) の merge では、
captured prefix through anchor + current extras + captured tail after anchor
の順にする。

期待:
  captured=[outer once,H_sub]
  current=[inner once]
  anchor=outer once
  merged=[outer once,inner once,H_sub]

Perform handler search trace を追加し、reject が inner once prompt=2 に match するか確認する。

それでも work cont 1 の reject 時に inner once が無いなら、
cps_lower.rs で targeted EffectfulCall lowering を実装する。
対象は DirectCall が Thunk を返し、その直後に non-thunk demand で ForceThunk される形。
DirectCall + ForceThunk を
  EffectfulCall -> cont_after_call
  EffectfulForce -> cont_after_force
へ split し、work の guard 以降を return frame に入れる。

SR.preserved_handlers + walk-based propagation は、handler delta を parent eval に返す機構なしでは不十分。
案 B の targeted lowering を本線にする。
```

---

# 私の次の一手まとめ

最短で行くなら:

```text
1. CpsResumption に handled_anchor を追加
2. merge_resumption_handlers を anchor-based に変更
3. reject handler search trace で order を確認
4. まだ cps:0 なら work の `DirectCall each -> ForceThunk` を EffectfulCall/EffectfulForce 化
```

この順が一番バグを局所化できると思うよ〜。write23 で F_each_post が capture できたから、次は **「inner once を正しい順序で、work の後続計算へ運ぶ」**だけに絞れる。
