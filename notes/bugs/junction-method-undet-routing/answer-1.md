結論から言うと、**主犯は `ResumeHandlerMerge` の順序そのものではなく、`junction__mono3` の handler arm answer と handler-scope escape answer が同じ `merge_cont / cont 2` に潰れているところ**だと思うよ〜。

つまり候補で言うと、強さはこんな感じ。

```text
本命: 3. PromptExit / EscapeTarget / ordinary return frame の分離不足
      ただし実体は「effect handler arm が escape continuation を普通に Continue できる」こと

次点: 2. CPS lowering が fallthrough Unit を handler result として流せる形

薄い: 1. ResumeHandlerMerge の handler stack composition
```

`ResumeHandlerMerge` の trace 自体は、むしろ期待に近い形に見えるねぇ。たとえば

```text
captured=[root, junction prompt 1, all prompt 2]
current=[root, fresh junction prompt 6]
merged=[root, old junction prompt 1, fresh junction prompt 6, all prompt 2]
```

これは「resumed suffix 内の `and/or` は fresh junction に見せたい、でも `sub::return` は all/any の prompt に見せたい」という意味では自然だよ〜。`std::junction` の実装も、`and/or` arm の中で `junction(k true)` / `junction(k false)` を再帰的に呼ぶ形だから、fresh junction を captured outer と captured inner の間に挿すのは筋がいい。

## 何が壊れているか

壊れている形は、たぶんこれだねぇ。

```text
handler arm body answer
  と
handler expression / catch scope answer
  と
handler arm の no-match / fallthrough Unit
```

この3つが、CPS 上で同じ `merge_cont` に合流できている。

`lower_handle` では `InstallHandler` の `escape` に `merge_cont` を渡していて、コメント上も「arm body の non-local return は merge continuation に落ちる」という設計になっている。
さらに `lower_effect_handler_arm_chain` は、effect arm body の値を `ctx.merge_cont` に `Continue` している。arm が尽きた fallback も `Unit` を作って同じ `merge_cont` に流す形だねぇ。

ここが今回の `Unit` 漏れの匂いとかなり一致する。

`std::junction::junction` の `and` arm は表面上こうだよねぇ。

```yulang
and(), k -> case junction(k true):
    true -> junction(k false)
    _ -> false
```

ここで `junction(k true)` の答えは boolean であるべき。なのに trace では `all__mono6` 側の `Unit` が `junction__mono3` の answer として上がっている。これは、`k false` や fold callback の「この iteration は値を出さずに進む」ための `Unit` が、fold / sub / junction の継続で処理されず、handler escape の answer として採用されている形に見える。アップロードされたメモの `cont 7: Literal Unit; Continue 2(Unit)` もこの筋を補強しているよ〜。

## `Perform` 側の危ないところ

`cps_eval.rs` の `Perform` は、handler arm を別 eval で走らせたあと、

```rust
let scope_return = match result {
    CpsRuntimeValue::ScopeReturn { .. } => result,
    other => CpsRuntimeValue::ScopeReturn {
        prompt: frame_prompt,
        target: frame_escape,
        value: Box::new(other),
    },
};
```

という感じで、arm の自然 return を prompt-targeted escape に包む設計だねぇ。

この設計自体はあり。ただしその場合、**handler arm 自身は `frame_escape` に普通の `Continue` をしてはいけない**。

今は lowering 側で arm body が `merge_cont` に `Continue` できる。eval 側でも、arm result を `ScopeReturn(prompt, merge_cont, value)` に包む。つまり `merge_cont` が、

```text
A. handler arm 内の普通の local continuation
B. handler install scope への non-local escape target
```

の二役になっている。ここが「value arm と old handler escape が同じ `cont 2` へ潰れている」の実体だと思うよ〜。

`handler_arm_continues_to_installed_escape` という特別扱いも入っているけど、これは continue-chain を静的にたどるだけで、`and/or` みたいに `Branch` / `DirectCall junction__mono3` / `ForceThunk` を挟む arm には弱い。
しかも `frame.install_eval_id == current_eval_id` 条件があるから、今回みたいに inherited/resumed frame 経由で古い prompt に戻るケースでは、救済が効かない可能性が高いねぇ。

## `threshold=0` の見方

`threshold=0` は「この handler install 時点で outer return frame がなかった」だけで、**handler expression の caller がない証拠ではない**と思うよ〜。

`try_route_scope_return_through_return_frames` は、frame walk で handler を見つけると、その frame の `matched_handler.escape` を復元して走らせる。そこで `threshold` によって `rest_frames` を切る。
この切り方は delimited continuation としては必要だけど、`rest_after=0` だから final answer だ、とは読めない。sync `DirectCall` の caller continuation は return frame ではなく、呼び出し元 eval の `dispatch_scope_return!` 側にまだいる場合があるからねぇ。

ただ、今回の `threshold=0` は主犯というより、**すでに `Unit` になった arm answer を逃がさず露出させている場所**に見える。なので I3 は正しい invariant だけど、最初に直すべき根ではないかなぁ。

## 立てるべき invariant

候補のうち、私は **I1 + I2 を本体、I3 を補助 invariant** にするのがいいと思う。

より強く書くなら、こう。

```text
H1. effect handler arm を Perform から評価したときの自然 return は ArmAnswer である。
    ArmAnswer は handled body answer 型であり、
    handler install scope の value arm / escape continuation を実行済みであってはならない。

H2. handler install scope の escape continuation を走らせる権限は、
    matching prompt を持つ dispatcher だけが持つ。
    lowering された arm body は frame_escape / merge_cont に直接 Continue しない。

H3. no-match / fallthrough Unit は ArmAnswer としても HandlerAnswer としても扱わない。
    到達不能なら unreachable、未処理なら outer handler へ propagate、
    少なくとも merge_cont へ Unit を流さない。

H4. threshold == 0 は final answer 判定ではない。
    prompt-targeted jump 後にも lexical caller continuation が残りうる。
```

これを今回の候補に対応させると、

```text
I1: 採用。いちばん大事。
I2: 採用。Resume(k, true/false) の raw answer と recursive junction answer の境界を守る。
I3: 採用。ただし主犯というより frame-walk 側の安全条件。
```

## 直すならどこか

局所的な `Unit` guard ではなく、まずは **`lower_effect_handler_arm_chain` の出口を変える**のがきれいだと思う。

今の形は概念的にこう。

```rust
let handled = lower_handler_body_expr(arm.body, Some(handler))?;
Continue(ctx.merge_cont, handled)
```

これを、effect arm eval の結果として返す形に寄せる。

```rust
let handled = lower_handler_body_expr(arm.body, Some(handler))?;
Return(handled)
```

その上で、`Perform` 側だけが

```rust
ScopeReturn {
    prompt: matched_prompt,
    target: frame_escape,
    value: arm_answer,
}
```

を作る。

この設計にすると、`merge_cont` は handler install scope の escape target 専用になる。arm body の local merge と handler scope escape が分離されるから、`cont 2` に `Unit` が普通の値として流れ込む構造を潰せるよ〜。

同時に、`lower_effect_handler_arm_chain` の no-arm fallback はこうした方がいい。

```rust
// 悪い: Unit を handler merge に流す
Continue(ctx.merge_cont, Unit)

// まし: arm eval の結果として返す
Return(Unit)

// もっとよい: typed unreachable / unhandled perform
Unreachable("no matching effect handler arm")
```

表面型的に handler arm が total なら、ここは `Unit` fallback ではなく invariant violation として落とす方がバグを早く見つけられるねぇ。通常の `match` fallback `Unit` も同じで、typed exhaustiveness が保証される場所なら `Unit` は危険すぎる sentinel だよ〜。`lower_match` / `lower_handler_body_match` にも fallback `Unit` があるから、少なくとも boolean match や exhaustive pattern の fallback は `Unreachable` 扱いに寄せると、今回みたいな「Unit が bool のふりをして進む」系を早期発見しやすい。

## `handler_arm_continues_to_installed_escape` はどうするか

この関数は、今の二重化した設計のつじつま合わせに見える。arm が `merge_cont` に直接 Continue できない設計へ寄せるなら、基本的には不要になるはず。

移行中はこう扱うのが安全かなぁ。

```text
- true なら最適化/救済ではなく invariant violation として trace する
- branchy arm まで無理に検出範囲を広げない
- Perform 側は「arm answer を包む」だけにする
```

検出を頑張る方向は、また別の「cont graph 解析が漏れたら壊れる」罠になりそうだねぇ。

## 期待する修正後の流れ

`and` arm なら、理想はこう。

```text
Perform(and)
  -> handler arm eval
       Resume(k, true)
       recursive junction handles resumed suffix
       returns Bool
       Branch Bool
       maybe Resume(k, false)
       recursive junction handles resumed suffix
       returns Bool
       arm eval Return(Bool)
  -> Perform dispatcher wraps Bool as ScopeReturn(prompt=old junction, target=old merge)
  -> old junction install scope receives Bool
  -> caller condition receives Bool
```

ここで `k false` の途中で出る `Unit` は、fold/sub の継続の内部値として消費されるべきで、`junction__mono3` の final answer にはならない。もし `Unit` が arm eval の Return まで来たら、それは `Resume` の return-frame chain が fold の残りを失っているという別バグとして扱う、という切り分けができるよ〜。

## 追加すると強い trace / assertion

最後に、原因を確定するならこの3つを入れるとかなり見えると思う。

```text
A. Perform arm eval result:
   fn, effect, matched_prompt, frame_escape, result type/value,
   result came from Return or ScopeReturn

B. Return frame pop:
   prompt_exit の frame を pop した時、
   それが normal body completion 由来か arm escape 由来か

C. merge_cont entry:
   junction__mono3 の escape/merge cont に入る値が Unit のとき、
   直前の caller / prompt / effect / resume site を出す
```

特に A で、`and` arm eval result がすでに `Unit` なのか、`ScopeReturn` 化の後に `Unit` になるのかが分かる。前者なら resume return-frame chain、後者なら escape/value-arm 混線だねぇ。

私の読みでは、直す順番はこれ。

```text
1. effect handler arm の出口を frame_escape 直 Continue から ArmAnswer Return に変える
2. Perform だけが prompt-targeted ScopeReturn を作る invariant にする
3. no-match / fallback Unit を unreachable か typed error に寄せる
4. threshold=0 を final answer 扱いしない assertion を frame-walk に置く
```

この方針なら、`Unit` guard で症状を隠すより、`junction` / `undet.once` / nested handler 全体に効く骨の太い修正になると思うよ〜。
