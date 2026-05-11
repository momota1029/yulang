過去チャット本文そのものは手元に全文で出ていない。だから、ここでは **`notes/todo/native-undet-write18-report.md` までの記録、現在の GitHub コード、write18 コミット差分、標準ライブラリ定義**を根拠にして、次の実装LLMへ渡せる形でまとめるねぇ。

# 結論

次にやるべき本筋は、**`std::undet.once` の branch arm における `loop(k true, std::list::append queue [k])` の「後続計算」と「queue」が、`k true` の resumption replay 後も正しく残るかを trace で確定し、そこで切れている経路を直すこと**だよ〜。

write18 で `fold_impl` の LEFT 側 Thunk を force し忘れる問題は直った。これで `each [1,2,3]` の最初の候補 `1` はちゃんと出て、`guard: n > 1` に reject されるところまで進んだ。でも、その reject を受けた `once` の reject arm が `queue=[]` と見なして `nil` を返し、最終的に `0` になる。write18 の引き継ぎでも、残りは「recursive loop が呼ばれていない」「呼ばれているが queue が空」「reject の発生位置が違う」のどれか、と整理されている。

標準ライブラリの `once` は実際にこう定義されている。

```yu
pub once(x: [_] _) = loop x [] with:
    our loop(x: [_] _, queue) = catch x:
        branch(), k -> loop(k true, std::list::append queue [k])
        reject(), _ -> case std::list::uncons queue:
            std::opt::opt::nil -> std::opt::opt::nil
            std::opt::opt::just (k, queue) -> loop(k false, queue)
        v -> std::opt::opt::just v
```

つまり、`branch(), k -> ...` では **`k true` を走らせる前後で、`k` を queue に保存した状態の recursive loop が意味論上の継続として残っていないといけない**。ここが今回の急所だねぇ。

---

# いま分かっている状態

## 1. `std::undet.once` は統合ターゲットで、単独の小物ではない

設計メモ上でも、`std::undet.once` は branch/reject、multi-shot resumption、resumption queue、recursive handler loop、`fold` / `sub::return`、handler/guard snapshot、handler boundary をまたぐ thunk callback が全部乗っている「統合ターゲット」と扱われている。だから、ここで壊れているのは自然だよ〜。

## 2. write9〜write18 の進展

ざっくり流れはこう。

* write9: `list<resumption>` を扱うため、CPS domain で `ListLen` / `ListIndex` / `ListIndexRangeRaw` を追加した。ただし helper+guard 経由で root thunk leak が出た。
* write10: root/lambda return site に `force_if_non_thunk_demand` を入れて root thunk leak を解消したが、旧 `Aborted` が広すぎて guard 以降を skip する問題が見えた。
* write11: `Aborted` を prompt-aware な `ScopeReturn { prompt, target, value }` に置換し、`InstallHandler.escape` と `inherited` handler frame を入れた。
* write12: `return_frames` と `EffectfulCall` / `EffectfulApply` / `EffectfulForce` を導入し、Perform 時点の caller continuation を resumption に入れ始めた。
* write14: `initial_frame_count` により「sync call は parent frames を継承するが、通常 Return では消費しない」という区別を入れた。
* write15: `std::list::fold_impl` / `std::undet::each` / `std::undet::once` を targeted な higher-order helper として扱い、`EffectfulCall` / `EffectfulApply` 化を進めた。結果は `cps:0 → cps:3`。
* write16: `once` 内の apply を強制的に `EffectfulApply` 化し、`EffectfulApply(Resumption)` の frame order を直した。それでも `cps:3`。
* write17: `Return(Thunk)` pre-force を試したが、`current_function = fold_impl` と `H_sub.escape_owner_function = each` が一致せず、`ScopeReturn` が escape するので無効化した。ここは戻してはいけない。
* write18: `fold_impl` LEFT の `EffectfulCall` 結果 Thunk を force していなかった問題を修正し、`cps:3 → cps:0` へ変化した。最初の candidate `1` と guard reject は正しく動くようになった。残りは queue replay。

write18 の実コミット差分でも、`cps_lower.rs` の higher-order helper `EffectfulCall` path に `force_if_non_thunk_demand(result, &expr.ty)` が戻されている。これが今回の直前修正だねぇ。

---

# 実装LLMにまず伝える禁止事項

ここを破ると、今まで積み上げた意味論が崩れる可能性が高い。

1. **write17 の pre-force path を再有効化しない。**
   `Return(Thunk)` を return frame 消費前に force すると、thunk body が `fold_impl` 文脈で走り、`each` の `H_sub` と owner check が合わず `ScopeReturn` が escape する。これは write17 で確認済み。

2. **`handle_scope_return` の owner check を緩めない。**
   `frame.escape_owner_function == current_function` は、function-local continuation id を安全に使うための防壁だよ〜。ここを緩めると、別 function の continuation id へジャンプする壊れ方が出る。

3. **全 `ApplyClosure` / 全 `ForceThunk` を雑に effectful 化しない。**
   write13〜write16 で何度も見えている通り、Cranelift 側や既存テストへの波及が大きい。targeted な `std::undet::once` / `std::list::fold_impl` 周辺でまず詰めるべき。

4. **Cranelift へ進まない。**
   今は Layer 1 の CPS eval が VM と一致していない。CPS eval の意味論が固まる前に Cranelift を直すと、間違った意味論を backend に移植する羽目になる。

5. **`return_frame_threshold` / `initial_frame_count` を外さない。**
   これらは write14/write15 で local tests を通すために必要になった中核設計だよ〜。外すなら trace で明確に「ここが過剰 truncate」と示してから。

---

# 次に実行する手順

## Step 0: baseline を固定する

まず、現状を実装LLM自身の環境で固定する。

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture

YULANG_CPS_TRACE_FRAMES=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待される現状はこう。

```text
cargo test -p yulang-native
  => pass

debugs_local_choice_caller_rest_eval
  => pass

debugs_local_choice_callback_rest_eval
  => pass

debugs_std_undet_once_skip_eval_layers
  => fail
  => VM: 2
  => CPS eval: 0
```

ここが違うなら、write18 以降の差分が入っている可能性があるから、まず差分確認だねぇ。

---

## Step 1: trace の粒度を上げる

write18 の trace は良い方向だけど、まだ `Variant` が `Discriminant(6)` のように出ていて、`nil` / `just` / queue 長が見えにくい。次は「どの queue がどこで空になるか」を見る trace にする。

### 1. value summary helper を作る

`cps_eval.rs` に、巨大 dump にならない summary を作る。

```rust
fn summarize_cps_value(value: &CpsRuntimeValue) -> String {
    match value {
        CpsRuntimeValue::Plain(v) => format!("Plain({v:?})"),
        CpsRuntimeValue::Thunk(thunk) => {
            format!("Thunk(owner={}, entry={:?})", thunk.owner_function, thunk.entry)
        }
        CpsRuntimeValue::Closure(closure) => {
            format!(
                "Closure(owner={}, entry={:?}, recursive_self={:?})",
                closure.owner_function,
                closure.entry,
                closure.recursive_self,
            )
        }
        CpsRuntimeValue::Resumption(resumption) => {
            format!(
                "Resumption(owner={}, target={:?}, frames={}, handlers={}, guards={})",
                resumption.owner_function,
                resumption.target,
                resumption.return_frames.len(),
                resumption.handlers.len(),
                resumption.guard_stack.len(),
            )
        }
        CpsRuntimeValue::List(items) => {
            let preview = items
                .iter()
                .take(3)
                .map(summarize_cps_value)
                .collect::<Vec<_>>()
                .join(", ");
            format!("List(len={}, [{}])", items.len(), preview)
        }
        CpsRuntimeValue::Tuple(items) => {
            let preview = items
                .iter()
                .map(summarize_cps_value)
                .collect::<Vec<_>>()
                .join(", ");
            format!("Tuple({preview})")
        }
        CpsRuntimeValue::Variant { tag, value } => {
            match value {
                Some(value) => format!("Variant({tag:?}, {})", summarize_cps_value(value)),
                None => format!("Variant({tag:?})"),
            }
        }
        CpsRuntimeValue::ScopeReturn { prompt, target, value } => {
            format!(
                "ScopeReturn(prompt={}, target={:?}, value={})",
                prompt.0,
                target,
                summarize_cps_value(value),
            )
        }
    }
}
```

目的は、`once` reject arm の返り値が本当に `opt::nil` なのか、`std::list::uncons queue` の入力 queue が本当に `len=0` なのかを一目で見られるようにすること。

---

## Step 2: `EffectfulApply` を重点 trace する

いちばん重要なのは、`once` の branch arm にあるこれ。

```yu
branch(), k -> loop(k true, std::list::append queue [k])
```

ここでは `k true` が effectful で、しかもその後に `std::list::append queue [k]` と recursive `loop` が残る。つまり **`k true` の Perform/ScopeReturn の後に、recursive loop を行う post-call continuation が return frame として残っているか**が核心だよ〜。

`CpsTerminator::EffectfulApply` に以下を出す。

```text
EffectfulApply:
  fn=<function>
  cont=<current>
  callable=<Closure | Resumption | Other>
  callable_summary=<...>
  arg=<summary>
  resume=<post_cont>
  return_frames.len.before=<n>
  initial_frame_count=<m>
  active_handlers=<summary>
```

`callable` が `Resumption` の場合は追加で:

```text
resumption.owner=<owner_function>
resumption.target=<target>
resumption.frames=<summary>
resumption.handlers=<summary>
combined_frames=<summary>
combined_frames.pop_order=<末尾から順に owner/cont>
```

`callable` が `Closure` の場合は追加で:

```text
closure.owner=<owner_function>
closure.entry=<entry>
closure.recursive_self=<...>
```

ここで見るべきことはこの3つ。

* `k true` が **sync `ApplyClosure(Resumption)` ではなく `EffectfulApply(Resumption)`** として走っているか。
* `k true` の post frame が、`queue+[k]` を計算して `loop(...)` へ進む continuation を指しているか。
* `EffectfulApply(Resumption)` の combined frame order が `new_frames + adjusted_res_frames` になっているか。

write16 の修正方針では、`continue_return_frames` は末尾から pop するので、captured resumption frames が末尾に来る必要がある。`res_frames + new_frames` に戻っていたら即バグだよ〜。

---

## Step 3: sync `ApplyClosure(Resumption)` が残っていないか確認する

現在の `cps_eval.rs` は、`ApplyClosure` の対象が `Resumption` なら `Resume` として扱う実装を持っている。これは `list<resumption>` から取り出した `k` を呼ぶために必要。ただし、この path は sync 扱いで、post-call frame を新しく push しない。

だから、`once` の branch arm の `k true` がここを通ると危ない。

`CpsStmt::ApplyClosure` にも trace を入れる。

```text
ApplyClosure:
  fn=<function>
  cont=<current>
  callable=<Closure | Resumption | Other>
  arg=<summary>
  return_frames.len=<n>
  initial_frame_count=<m>
```

判定:

```text
もし once branch arm の k true が ApplyClosure(Resumption) で走っている
  => lowering がまだ足りない
  => k true を EffectfulApply terminator にし、post-cont に queue append + loop call を残す必要がある
```

この場合の修正対象は evaluator ではなく `cps_lower.rs` 側。`force_effectful_apply` が `once` に立っているはずなのに、何かの形で `k true` が sync stmt として残っている、という読みになる。

---

## Step 4: list primitive の queue 操作を trace する

write9 では `ListLen` / `ListIndex` / `ListIndexRangeRaw` が CPS domain 対応された。でも、標準 `once` の branch arm は `std::list::append queue [k]` を使う。実際の lowering がどの primitive op に落ちるかを trace で見るべきだよ〜。

`CpsStmt::Primitive` で、list 系だけ trace する。

```text
Primitive:
  fn=<function>
  cont=<current>
  op=<op>
  args=[<summary>, ...]
  result=<summary>
```

特に見る op:

```text
ListLen
ListIndex
ListIndexRangeRaw
ListAppend
ListMerge
ListSingleton
```

分岐:

```text
std::list::append queue [k] の result が List(len=1, [Resumption(...)]):
  => list primitive は正常

append の前から queue len=0, [k] len=1 なのに result len=0:
  => list primitive bug

append の前の k が Resumption ではない:
  => branch arm の handler/resumption capture bug

append 自体が trace に出ない:
  => k true が先に non-local exit して、queue append まで到達していない
```

ここはとても大事。`loop(k true, append queue [k])` は通常の call evaluation order だと、第一引数 `k true` が先に評価される可能性がある。その場合、`k true` が effect を起こす前に `append queue [k]` はまだ実行されていない。だから `k true` の post-cont が「append を実行して recursive loop へ行く」形で return frame に入っている必要がある。

---

## Step 5: `InstallHandler` / `UninstallHandler` と prompt を trace する

write11 以降、`ScopeReturn` は dynamic prompt に基づいて handler scope へ戻る。`InstallHandler` は `escape` continuation を持ち、`inherited` frame は ScopeReturn を解決しない。

ここで見るべきことは、recursive `loop(k true, [k])` が入れた新しい `once` handler が、後続の `guard reject` の時点で active かどうか。

`CpsStmt::InstallHandler`:

```text
InstallHandler:
  fn=<function>
  cont=<current>
  handler=<id>
  prompt=<fresh_prompt>
  escape=<escape_cont>
  return_frame_threshold=<return_frames.len>
  active_handlers.before=<summary>
  active_handlers.after=<summary>
```

`CpsStmt::UninstallHandler`:

```text
UninstallHandler:
  fn=<function>
  cont=<current>
  handler=<id>
  active_handlers.before=<summary>
  active_handlers.after=<summary>
```

`CpsTerminator::Perform`:

```text
Perform:
  fn=<function>
  cont=<current>
  effect=<path>
  resume=<resume_cont>
  handler=<handler_id>
  payload=<summary>
  active_handlers=<summary>
  return_frames=<summary>
  captured_resumption=<summary>
```

判定:

```text
guard reject 時の active_handlers に recursive loop の once handler がある:
  => handler scope は残っている。queue/env 側を見る。

guard reject 時の active_handlers に outer once しかない:
  => recursive loop の handler scope が失われている。
  => k true replay の frames/extras/handler injection を見る。

guard reject が recursive loop install 前に発生:
  => branch arm の post-cont が捕まっていない。
```

---

# 最も疑わしい場所

私の読みでは、第一候補はここ。

## `k true` の「後続」が return frame に入っていない

`once` の branch arm は:

```yu
loop(k true, std::list::append queue [k])
```

ここで `k true` は resumption replay。中で `each` が `sub::return 1` を起こし、caller 側の `guard` が reject する。期待する意味論では、`branch` を見つけた時点で `k` は queue に保存され、recursive `loop` の文脈が次の reject を受ける側になっている。

でも現状は reject arm が `queue=[]` を見ている。つまり、

```text
branch arm:
  k true を走らせる
  その後 queue+[k] で loop する
```

という「その後」の部分が、`k true` の non-local return/replay によって失われている可能性が高い。

この場合の修正は、**`k true` を EffectfulApply terminator にし、その resume continuation に `std::list::append queue [k]` と recursive `loop(...)` の残りを入れること**だよ〜。

擬似的にはこういう形が欲しい。

```text
once branch arm cont:
  EffectfulApply {
    closure: k,
    arg: true,
    resume: cont_after_k_true
  }

cont_after_k_true(k_true_result):
  q1 = std::list::append queue [k]
  loop1 = ApplyClosure(loop, k_true_result)    // curried 1段目
  EffectfulApply {
    closure: loop1,
    arg: q1,
    resume: cont_after_loop
  }
```

実際の lowering は curried apply や thunk wrapping が絡むからこの通りではない。ただし意味論としては「`k true` の post-cont に queue append と loop call がある」ことが必要。

---

# ありうる原因別の修正方針

## Case A: `loop(k true, queue+[k])` が呼ばれていない

trace の特徴:

```text
EffectfulApply/ApplyClosure for k true は出る
でも std::list::append queue [k] が出ない
recursive loop apply が出ない
その後 guard reject が起きる
reject arm は queue=[]
```

この場合は、**argument evaluation の effectful rest capture が足りない**。

実装方針:

* `cps_lower.rs` の `FunctionLowerer.force_effectful_apply` が true の関数、つまり `std::undet::undet::once` 系では、`Apply { callee, arg }` の `arg` 側が effectful な可能性を持つとき、arg 評価を sync stmt として済ませない。
* `arg` の評価が `k true` のような effectful apply なら、`EffectfulApply` terminator を発行し、その post-cont で残りの application を続ける。
* これを global にやらない。まず `force_effectful_apply` の関数に限定する。

実装LLMに渡す表現:

> `loop(k true, append queue [k])` は、第一引数 `k true` が perform しうる。したがって「callee と第二引数と loop apply の残り」を、`k true` の post-call continuation として return frame に入れないといけない。`k true` を単に値として sync に lower してはいけない。

---

## Case B: recursive loop は呼ばれるが queue が空

trace の特徴:

```text
std::list::append queue [k] は出る
recursive loop apply も出る
でも recursive loop の queue param が List(len=0)
```

この場合は、list primitive か argument binding が怪しい。

確認すること:

* `std::list::append queue [k]` の入力:

  * `queue` は `List(len=0)`
  * `[k]` は `List(len=1, [Resumption(...)] )`
* 出力:

  * `List(len=1, [Resumption(...)] )` になるべき
* recursive loop の第二引数:

  * 同じ `List(len=1, ...)` が渡るべき

もし append が壊れているなら、`eval_cps_primitive` に `ListAppend` / `ListMerge` / `ListSingleton` の CPS value 対応を足す。

重要な方針:

```text
resumption / closure / thunk を含む list は VmValue に戻さない。
CpsRuntimeValue::List のまま扱う。
```

現在の evaluator は `CpsRuntimeValue::List/Tuple/Variant` を持ち、`TupleGet` / `VariantTagEq` / `VariantPayload` も CPS value に対応している。だから、list ops もこの方針に揃えるのが自然だねぇ。

---

## Case C: queue len=1 の recursive loop に入るが、reject は outer loop へ行く

trace の特徴:

```text
recursive loop(x, queue=[k]) は呼ばれている
InstallHandler for recursive loop も見える
でも guard reject の Perform 時、active_handlers に recursive handler がない
outer handler だけが残る
```

この場合は、handler frame の継承・注入・消費順が怪しい。

見る場所:

* `EffectfulApply(Resumption)` の `extra` handlers
* `inject_extra_handlers`
* `combined_frames` の順序
* `continue_return_frames` の pop 順
* `ScopeReturnAction::JumpOrExit` 時の `return_frame_threshold` truncate

write12 以降、`Resume` / `ResumeWithHandler` / `ApplyClosure(Resumption)` は resume site にある handler を extras として captured frames に inject する設計になっている。ここで recursive loop の handler が frames に注入されていないと、guard reject が outer once に流れる。

ただし、ここでも owner check を緩めるのは違う。handler が消えた理由を追うべきだよ〜。

---

# 具体的なコード修正候補

ここは実装LLMが trace で Case を確定してから触る順番。

## 候補 1: `eval_cps_primitive` の list ops を完全に CPS value 対応する

もし `ListAppend` / `ListMerge` / `ListSingleton` が VM fallback になっているなら、先にここを直す。`std::undet.once` の queue は `list<resumption>` なので、VM value へ変換できない。

実装方針:

```rust
match op {
    PrimitiveOp::ListAppend => {
        let (list, value) = expect_two(args)?;
        let CpsRuntimeValue::List(items) = list else {
            return Err(...);
        };
        let mut next = items.as_ref().clone();
        next.push(value);
        Ok(CpsRuntimeValue::List(Rc::new(next)))
    }

    PrimitiveOp::ListMerge => {
        let (left, right) = expect_two(args)?;
        let CpsRuntimeValue::List(left) = left else { ... };
        let CpsRuntimeValue::List(right) = right else { ... };
        let mut next = left.as_ref().clone();
        next.extend(right.iter().cloned());
        Ok(CpsRuntimeValue::List(Rc::new(next)))
    }

    PrimitiveOp::ListSingleton => {
        let value = expect_one(args)?;
        Ok(CpsRuntimeValue::List(Rc::new(vec![value])))
    }

    ...
}
```

もし enum 名が違うなら、実際の `core_ir::PrimitiveOp` 名に合わせる。

注意点:

* `CpsRuntimeValue::Resumption` を `VmValue` に変換しようとしない。
* `ListUncons` が直接 primitive としてあるなら、それも CPS value の `Variant(just Tuple(head, tail))` を返す。
* 既存の `ListLen` / `ListIndex` / `ListIndexRangeRaw` と同じ思想に揃える。

---

## 候補 2: `once` 内の effectful argument rest を捕捉する

trace で `k true` 後に append/loop が出ないなら、ここが本命。

`cps_lower.rs` の方針:

```text
FunctionLowerer.force_effectful_apply == true
または higher_order_helper == true の関数内で、
Apply の callee または arg が effectful potential を持つなら、
arg 評価 / apply 自体を terminator split して、残りの call context を post-cont に下げる。
```

実装LLMにはこう指示すると誤解が少ない。

> `loop(k true, append queue [k])` を lower するとき、`k true` を「ただの引数値」として先に評価してはいけない。`k true` は `branch` resumption の resume で、内部で `sub::return` や caller 側の `guard reject` まで進みうる。したがって、`append queue [k]` と recursive `loop` の適用は、`k true` の post-continuation として return frame に保存される必要がある。

これは「`once` の branch arm 専用の call-rest capture」でもよい。最初から一般化しすぎない方が安全。

---

## 候補 3: `EffectfulApply(Resumption)` の frame order を再確認して修正する

write16 の正しい順序は:

```rust
let mut combined_frames = new_frames;
combined_frames.extend(adjusted_res);
```

pop 順は末尾からなので:

```text
resumption frames の innermost
...
resumption frames の outermost
F_post
parent frames
```

もし現コードが何らかの差分でこう戻っていたら修正。

```rust
let mut combined_frames = adjusted_res;
combined_frames.extend(new_frames);
```

これはダメ。post frame が先に pop され、captured continuation の本体より先に queue/loop の後続が走るか、逆に必要な frame が消える。

---

# 追加する test

既存の `debugs_std_undet_once_skip_eval_layers` だけだと大きすぎる。trace と一緒に、小さい regression を足すと別LLMが迷いにくい。

## 1. once branch arm が queue を保持する最小テスト

標準 `each` ではなく、branch/reject だけで queue replay を見る。

```rust
#[test]
#[ignore = "debug: once queue replay after rejected first branch"]
fn debugs_once_queue_replay_after_reject() {
    let source = r#"
use std::undet::*;

my work(): int = {
    my b = branch()
    if b {
        guard false
        1
    } else {
        2
    }
}

case work().once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#;

    run_with_large_stack(|| {
        let module = runtime_module_from_source_with_options(
            source,
            native_default_source_options(),
        ).expect("runtime module");

        crate::cps_compare::compare_cps_module(&module)
            .expect("CPS eval == VM");
    });
}
```

期待は `2`。これが落ちるなら、`fold_impl` ではなく `once` queue replay 単体の問題だと確定する。

## 2. queue に resumption が入る primitive 単体

すでに `compares_resumption_stored_in_list_through_cps_repr_cranelift` があるが、CPS eval だけの小さいテストもあるとよい。

```rust
#[test]
#[ignore = "debug: CPS eval resumption list uncons"]
fn debugs_cps_eval_resumption_list_uncons() {
    let source = r#"
pub act choice:
  pub branch: () -> bool

catch choice::branch ():
    choice::branch (), k -> case std::list::uncons [k]:
        std::opt::opt::nil -> 0
        std::opt::opt::just (r, _) -> if r true: 1 else: 2
    v -> if v: 10 else: 20
"#;

    run_with_large_stack(|| {
        let module = runtime_module_from_source_with_options(
            source,
            native_default_source_options(),
        ).expect("runtime module");

        crate::cps_compare::compare_cps_module(&module)
            .expect("CPS eval == VM");
    });
}
```

目的は、`list<resumption>` の container/primitive が本当に Layer 1 で動いているかを直接見ること。

## 3. append queue `[k]` 専用

```rust
#[test]
#[ignore = "debug: CPS eval appends resumption to queue"]
fn debugs_cps_eval_append_resumption_queue() {
    let source = r#"
pub act choice:
  pub branch: () -> bool

catch choice::branch ():
    choice::branch (), k ->
        case std::list::uncons (std::list::append [] [k]):
            std::opt::opt::nil -> 0
            std::opt::opt::just (r, _) -> if r true: 1 else: 2
    v -> if v: 10 else: 20
"#;

    run_with_large_stack(|| {
        let module = runtime_module_from_source_with_options(
            source,
            native_default_source_options(),
        ).expect("runtime module");

        crate::cps_compare::compare_cps_module(&module)
            .expect("CPS eval == VM");
    });
}
```

これが落ちるなら queue primitive 側。通るなら `once` の call-rest / handler scope 側。

---

# 成功条件

最初の完了条件はこの順番。

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待:

```text
通常テスト: pass
write12 local: pass
write13 local: pass
std::undet.once skip eval layers:
  Layer 1 CPS eval == VM
  VM: 2
  CPS eval: 2
```

その後で Layer 2 の CPS repr eval を見る。Cranelift はその後。

```bash
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

この debug test の内部が Layer 1 → Layer 2 → Layer 3 を順に走る形なら、まず Layer 1 が通ったことをログで確認してから次へ進む。

---

# 実装LLMへ渡す最短指示文

そのまま貼るなら、これでよさそうだよ〜。

> write18 後の残りバグは `std::undet.once` の queue replay。`fold_impl` LEFT Thunk force 漏れは修正済みなので、write17 の pre-force を戻さないこと。`handle_scope_return` の owner check も緩めないこと。
>
> まず `YULANG_CPS_TRACE_FRAMES=1 cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture` を走らせ、`once` branch arm の `loop(k true, std::list::append queue [k])` を event-by-event で追う。
>
> trace では `EffectfulApply` / `ApplyClosure` / `Primitive(list ops)` / `InstallHandler` / `Perform reject` / `continue_return_frames` に、value summary、queue length、resumption owner/target/frames、active handler prompt、frame pop order を出す。
>
> 判定は3つ。
> A: `k true` 後に `append queue [k]` と recursive `loop` が出ないなら、effectful argument/call-rest capture が足りない。`once` 内で `k true` を `EffectfulApply` にし、その post-cont に queue append と loop apply を残す lowering を入れる。
> B: recursive loop は出るが queue が空なら、`ListAppend` / `ListMerge` / `ListSingleton` などを CPS value domain で実装し、`list<resumption>` を `VmValue` に戻さない。
> C: recursive loop queue は len=1 だが reject が outer handler に行くなら、`EffectfulApply(Resumption)` の extras injection / frame order / handler prompt の維持を直す。frame order は `new_frames + adjusted_res_frames` が正しい。
>
> 修正後、通常テスト、write12/write13 local tests、`debugs_std_undet_once_skip_eval_layers` の Layer 1 を通す。Cranelift にはまだ進まない。

---

# 私の予想

いちばん可能性が高いのは **Case A** だと思う。

理由は、`once` の branch arm が `loop(k true, append queue [k])` という形だから。`k true` は「値を作るだけの引数評価」ではなく、内部で `sub::return`、caller の `guard reject`、`ScopeReturn` dispatch まで起こしうる。そこで post-call continuation として `append queue [k]` と recursive `loop` が捕まっていなければ、まさに write18 の観察どおり「reject が再帰前の outer queue=[] で処理される」形になる。

ただし、list primitive 側もまだ完全には安心できない。write9 で対応されたのは主に `uncons` 周辺の `ListLen` / `ListIndex` / `ListIndexRangeRaw` で、`std::list::append queue [k]` がどの primitive に落ちているかは trace で必ず見た方がいい。
