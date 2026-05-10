うん、これはかなり本質的だねぇ。
読んだ限り、**いま当たっている問題は “`std::undet.once` の細部バグ” ではなく、handler の非局所 return をどう scope で止めるか** という、CPS backend の中核設計の問題だと思うよ〜。

報告書の結論はかなり正しい。いまの `Aborted(value)` は「handler arm の結果で現在の stack を抜ける」ためには必要だけど、**root まで一直線に抜けてしまうのが間違い** だねぇ。`sub::return 1` は `each` の中の `sub` handler scope だけを抜けるべきで、`work` の `guard` や outer `once` まで飛ばしてはいけない。報告書でも、VM は `each` が `1` を返したあと `guard` で reject し、backtrack して `2` を返すのに、CPS では `Aborted(1)` が root まで行って `1` になっている、と整理されている。

---

# 結論

## handler-aware `Aborted` を実装するべき

質問 1 への答えは **Yes** だよ〜。
ただし、`Aborted { handler_id, value }` だけでは足りない可能性が高い。

なぜなら、`handler_id` は静的な handler の種類であって、**動的に install された handler scope の一回一回**を識別できないから。`std::undet.once` の `loop` は recursive handler loop なので、同じ handler id の handler frame が何度も install される。ここで static handler id だけを target にすると、内側・外側の同じ handler を取り違える危険があるねぇ。

なので、設計としてはこうがよいと思う。

```rust
CpsRuntimeValue::ScopeReturn {
    prompt: CpsPromptId,
    target: CpsContinuationId,
    value: Box<CpsRuntimeValue>,
}
```

または名前だけ違って、

```rust
CpsRuntimeValue::Aborted {
    prompt: CpsPromptId,
    target: CpsContinuationId,
    value: Box<CpsRuntimeValue>,
}
```

でもいい。

大事なのは、

```text
handler_id ではなく dynamic prompt id を持つ
handler scope を抜ける continuation target を持つ
root ではなく prompt boundary で unwrap する
```

ということだねぇ。

---

# 今の `Aborted` の何が違うか

現在の `Aborted(value)` はこういう意味になっている。

```text
Perform が起きる
handler arm を実行する
handler arm の戻り値を Aborted(value) に包む
DirectCall / ApplyClosure / ForceThunk / Resume が全部それを伝播する
root で unwrap する
```

これは `sub::return` の短絡には効く。
でも短絡範囲が広すぎる。

欲しい意味はこう。

```text
Perform が起きる
対応する handler arm を実行する
handler arm の戻り値を ScopeReturn(prompt, target, value) に包む
DirectCall / ApplyClosure / ForceThunk / Resume がそれを伝播する
その prompt を install した handler scope に戻ったら unwrap して target continuation へ jump
それより外側には普通の値として流れる
```

つまり `sub::return 1` は、

```text
fold callback
  -> fold implementation
    -> each の sub handler scope
       ここで ScopeReturn を捕まえて 1 に戻す
    -> work の guard に進む
```

となるべき。

今は、

```text
fold callback
  -> fold implementation
    -> each
      -> work
        -> once
          -> root
```

まで飛んでしまっている。

---

# すすめる実装方針

## Phase 1: 名前を変える

まず `Aborted` という名前は、今後混乱しやすいと思う。
もし大きな変更が許されるなら、こう変えた方が読みやすい。

```rust
CpsRuntimeValue::ScopeReturn {
    prompt: CpsPromptId,
    target: CpsContinuationId,
    value: Box<CpsRuntimeValue>,
}
```

CPS repr 側も同じ。

```rust
CpsReprRuntimeValue::ScopeReturn {
    prompt: CpsPromptId,
    target: CpsContinuationId,
    value: Box<CpsReprRuntimeValue>,
}
```

`Aborted` のままでもよいけど、その場合も中身は必ず target 付きにする。

---

## Phase 2: dynamic prompt id を導入する

CPS eval 用に prompt id を作る。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CpsPromptId(u64);
```

`eval_continuations` の状態に `next_prompt_id` を持たせるか、関数呼び出しをまたいで一意にする必要があるなら eval module 全体の state に持たせる。

今の `eval_continuations` はかなり引数が増えていると思うので、そろそろ state struct にまとめてもいい。

```rust
struct CpsEvalState {
    next_prompt_id: u64,
}
```

ただし、まず小さくやるなら `Rc<RefCell<u64>>` を渡してもいい。

```rust
type PromptCounter = Rc<RefCell<u64>>;
```

---

## Phase 3: handler frame に prompt と escape target を持たせる

現在の handler frame はたぶんこういう方向だと思う。

```rust
struct CpsHandlerFrame {
    handler: CpsHandlerId,
    owner_function: String,
    guard_stack: Vec<CpsGuardEntry>,
    envs: Vec<CpsEvaluatedHandlerEnv>,
}
```

これをこうする。

```rust
struct CpsHandlerFrame {
    prompt: CpsPromptId,
    handler: CpsHandlerId,
    owner_function: String,
    escape: CpsContinuationId,
    guard_stack: Vec<CpsGuardEntry>,
    envs: Vec<CpsEvaluatedHandlerEnv>,
}
```

`escape` は「この handler scope の結果を受け取る continuation」。
つまり、handler arm body が返した値をここへ渡して、catch expression の外側へ戻す。

---

# `InstallHandler` に escape continuation が必要

ここが大事だよ〜。

現在の `CpsStmt::InstallHandler` はおそらくこう。

```rust
InstallHandler {
    handler,
    envs,
}
```

これでは「この handler scope を抜けたらどこへ戻るか」が分からない。
だからこう変える。

```rust
InstallHandler {
    handler: CpsHandlerId,
    envs: Vec<CpsHandlerEnv>,
    escape: CpsContinuationId,
}
```

あるいは、

```rust
InstallHandler {
    handler,
    envs,
    prompt_return: CpsContinuationId,
}
```

名前はどちらでもいい。

## lowering 側

`lower_handle` では、すでに `value_cont` / `merge_cont` のような continuation を作っているはず。
そこを使う。

イメージ:

```rust
let merge_cont = self.fresh_continuation();

self.current.stmts.push(CpsStmt::InstallHandler {
    handler,
    envs: Vec::new(),
    escape: merge_cont,
});
```

handler scope の body や handler arm が結果を出したら、最終的に `merge_cont(value)` に合流する。

---

# Phase 4: Perform で `ScopeReturn` を作る

現在の `Perform` は handler arm を eval して、その結果を `Aborted(value)` にして返している。報告書にも、今の `Aborted` が root まで伝播するのが問題だと書かれている。

これをこうする。

```rust
let (handler_arm, frame, handler_body_stack) =
    handler_arm_for_stack(...)?;

let result = eval_continuations(
    module,
    handler_owner,
    handler_arm.entry,
    vec![payload, resumption],
    handler_values,
    handler_body_stack,
    guard_stack,
)?;

let result = match result {
    CpsRuntimeValue::ScopeReturn { .. } => result,
    other => CpsRuntimeValue::ScopeReturn {
        prompt: frame.prompt,
        target: frame.escape,
        value: Box::new(other),
    },
};

return Ok(result);
```

重要なのは、nested `ScopeReturn` は上書きしないこと。
内側の handler return がすでに target を持っているなら、それをそのまま伝播する。

---

# Phase 5: internal call site で ScopeReturn を捕まえる

現在は internal call 後に、

```rust
if matches!(result, CpsRuntimeValue::Aborted(_)) {
    return Ok(result);
}
```

のように即 return しているはず。

これを helper にする。

```rust
enum CallResultAction {
    Continue(CpsRuntimeValue),
    Jump {
        target: CpsContinuationId,
        value: CpsRuntimeValue,
        active_handlers: Vec<CpsHandlerFrame>,
    },
    Propagate(CpsRuntimeValue),
}
```

でも最初はもっと単純でいい。

```rust
fn handle_scope_return(
    result: CpsRuntimeValue,
    function: &CpsFunction,
    active_handlers: &mut Vec<CpsHandlerFrame>,
) -> ScopeReturnAction {
    match result {
        CpsRuntimeValue::ScopeReturn {
            prompt,
            target,
            value,
        } => {
            if let Some(index) = active_handlers
                .iter()
                .rposition(|frame| frame.prompt == prompt)
            {
                // handler scope を抜ける。
                // 選ばれた frame とそれより内側の frame は pop。
                active_handlers.truncate(index);

                ScopeReturnAction::Jump {
                    target,
                    value: *value,
                }
            } else {
                ScopeReturnAction::Propagate(
                    CpsRuntimeValue::ScopeReturn {
                        prompt,
                        target,
                        value,
                    }
                )
            }
        }
        other => ScopeReturnAction::Value(other),
    }
}
```

使う側:

```rust
let result = eval_function_with_context(...)?;

match handle_scope_return(result, function, &mut active_handlers) {
    ScopeReturnAction::Value(value) => {
        write_value(&mut values, *dest, value);
    }
    ScopeReturnAction::Jump { target, value } => {
        current = target;
        args = vec![value];
        continue;
    }
    ScopeReturnAction::Propagate(value) => {
        return Ok(value);
    }
}
```

これを入れる対象:

```text
DirectCall
ApplyClosure
ForceThunk
Resume
ResumeWithHandler
```

現在 `Aborted` を伝播している場所すべて。

---

# ここで何が起きるか

`sub::return 1` の場合:

```text
fold callback で Perform sub::return
handler arm result = ScopeReturn(prompt=sub_prompt, target=sub_merge, value=1)
ApplyClosure / DirectCall を伝播
each 関数内の fold call site に戻る
active_handlers に sub_prompt がある
=> catch
=> current = sub_merge
=> args = [1]
=> each は 1 を通常値として返す
```

その後、

```text
work は n = 1 を受け取る
guard: n > 1
=> reject
once が backtrack
=> 2
```

になる。

これが VM と一致するはず。

---

# Phase 6: `eval_function` root で unwrap しない

これも重要。

今の `unwrap_aborted` は root で `Aborted` を剥がしている。
新しい設計では、root に `ScopeReturn` が届いたら、それはほぼ bug。

なので、

```rust
eval_cps_module:
    let value = eval_function(...)
    into_plain_value(value)
```

にして、`ScopeReturn` は `ExpectedPlainValue` か専用 error にする。

できれば error を分ける。

```rust
CpsEvalError::EscapedScopeReturn {
    prompt: CpsPromptId,
    target: CpsContinuationId,
}
```

root で unwrap してしまうと、今回と同じ「たまたま一致」がまた起きる。

---

# Phase 7: CPS repr eval に同じ変更を入れる

CPS eval が通ってから、CPS repr eval に同じものを入れる。

`CpsReprHandlerFrame` にも、

```rust
prompt
escape
```

を持たせる。

`CpsReprRuntimeValue::Aborted` も `ScopeReturn` にする。

```rust
CpsReprRuntimeValue::ScopeReturn {
    prompt: CpsPromptId,
    target: CpsContinuationId,
    value: Box<CpsReprRuntimeValue>,
}
```

同じく DirectCall / ApplyClosure / ForceThunk / Resume / ResumeWithHandler の後で捕まえる。

---

# Phase 8: Cranelift は最後

報告書の質問 3 への答えは、**CPS eval を先に直すべき** だよ〜。
Cranelift は後。

理由は単純で、今は semantic 問題だから。
CPS eval / CPS repr eval が正しい意味を持つ前に Cranelift を触ると、間違った意味を機械語側に写してしまう。

順番はこう。

```text
1. CPS eval
2. CPS repr eval
3. Cranelift JIT
4. object/executable
```

---

# Cranelift 側の方針

Cranelift は少し大変だけど、同じ考え方でいける。

## runtime abort slot を prompt-aware にする

現在はたぶん TLS に abort value だけがある。
それをこうする。

```rust
struct YulangCpsI64Abort {
    prompt: i64,
    value: i64,
}

thread_local! {
    static YULANG_CPS_I64_ABORT: RefCell<Option<YulangCpsI64Abort>> = ...
}
```

helper:

```rust
pub extern "C" fn yulang_cps_abort_i64(prompt: i64, value: i64) -> i64;
pub extern "C" fn yulang_cps_abort_active_i64() -> i64;
pub extern "C" fn yulang_cps_abort_prompt_i64() -> i64;
pub extern "C" fn yulang_cps_abort_value_i64() -> i64;
pub extern "C" fn yulang_cps_clear_abort_i64() -> i64;
```

## handler frame に prompt を持たせる

```rust
struct YulangCpsI64HandlerFrame {
    prompt: i64,
    handler: i64,
    guard_stack: Box<[i64]>,
    envs: Vec<YulangCpsI64HandlerEnv>,
}
```

`install_handler` で fresh prompt を作る。

```rust
pub extern "C" fn yulang_cps_install_handler_i64(handler: i64) -> i64 {
    let prompt = next_prompt();
    push frame { prompt, handler, ... };
    prompt
}
```

ただし、CPS IR の `InstallHandler` に `escape` continuation を持たせるなら、Cranelift lowering 側では install helper の返り値 prompt を SSA value として持つ必要がある。
これが continuation block をまたぐなら面倒になる。

なので Cranelift では最初は helper ベースでこうしてもいい。

```rust
yulang_cps_abort_matches_current_handler_i64(handler_id) -> i64
```

これは TLS handler stack の中で、abort.prompt と一致する frame があり、かつ handler_id が一致するかを見る。

ただし、recursive handler 同士を取り違えないためには、最終的には prompt id 比較が必要。
static handler id だけで catch する設計は避けた方がいい。

---

# 実装規模を抑えるための順序

## Step 1: CPS eval だけ prompt-aware にする

目標:

```text
debugs_std_undet_once_skip_eval_layers:
  Layer 1 CPS eval OK
```

この段階では CPS repr / Cranelift が壊れていていい。

## Step 2: CPS repr eval

目標:

```text
Layer 1 OK
Layer 2 OK
```

## Step 3: Cranelift

目標:

```text
Layer 3 OK
```

---

# 小さい regression を先に足す

`std::undet.once` は大きいので、prompt-aware `ScopeReturn` の最小テストを作るといい。

## 1. sub return 後に後続処理が続く

```yulang
{
    my x = std::flow::sub::sub {
        std::flow::sub::return 1
        999
    }
    x + 1
}
```

期待: `2`

ここで `sub::return` が root まで飛ぶなら `1` になり、正しく sub scope で止まれば `2` になる。

## 2. sub return が block 内の後続文を skip する

```yulang
std::flow::sub::sub {
    std::flow::sub::return 1
    999
}
```

期待: `1`

これは従来の Aborted が必要な理由を固定する。

## 3. each + guard

報告の failing case。

```yulang
my work(): int = {
    my n = each [1, 2, 3]
    guard: n > 1
    n
}

case work().once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

期待: `2`

この3つを順に通す。

---

# 彼にどう伝えるか

以下をそのまま渡していいと思う。

```text
今回の問題は「Aborted が必要か不要か」ではなく、
「Aborted がどこで止まるべきか」の問題です。

現在の Aborted(value) は root まで伝播して unwrap される。
これは sub::return の短絡には効くが、catch / handler の install scope を越えすぎる。
std::undet.each の sub::return 1 は each 内の sub handler scope だけを抜け、
work 側の guard に進む必要がある。root まで飛ばしてはいけない。

実装方針:
1. Aborted を ScopeReturn に変える。
   ScopeReturn は prompt id と escape continuation と value を持つ。
2. InstallHandler は dynamic prompt id を生成し、
   handler frame に prompt と escape continuation を持たせる。
3. Perform が選んだ handler arm の戻り値は
   ScopeReturn { prompt: selected_frame.prompt, target: selected_frame.escape, value }
   に包む。
4. DirectCall / ApplyClosure / ForceThunk / Resume / ResumeWithHandler の後で
   ScopeReturn を受け取ったら、現在の active_handlers に同じ prompt があるか見る。
   - あるなら、その handler scope を pop し、target continuation に value を渡して jump。
   - ないなら、そのまま caller に propagate。
5. root で ScopeReturn を unwrap しない。root に届いたら bug として error。
6. まず CPS eval だけで実装し、debugs_std_undet_once_skip_eval_layers の Layer 1 を通す。
7. 次に CPS repr eval。
8. 最後に Cranelift。Cranelift では abort slot に prompt id を持たせる。

注意:
- handler id だけを target にしない。recursive loop では同じ handler id が複数回 install されるので、dynamic prompt id が必要。
- Perform で Aborted wrap を消さない。それだと sub::return が fold の後続 reject を skip できない。
- eval_function 境界で unwrap しない。scope で catch する。
```

---

# 質問への答え

## 1. handler-aware Aborted を実装すべきか？

**はい。実装すべき。**
ただし handler id だけでなく、dynamic prompt id を使うべき。

## 2. `ScopeReturn` の方が良いか？

**はい。名前としては `ScopeReturn` の方が良い** と思う。
`Aborted` だと「root まで中断する」ニュアンスが強すぎる。
実際には「handler scope まで戻る値」だから、`ScopeReturn` / `PromptReturn` / `HandlerReturn` の方が設計が伝わる。

りななら `ScopeReturn` にするかなぁ。

## 3. CPS eval を先に直すべきか？

**はい。CPS eval が最優先。**
今は意味論の問題なので、Cranelift は後。

## 4. 既存 simple test は怪しいか？

**怪しい。**
報告の通り、`each [1,2,3].once` は最初の値 `1` がそのまま正答なので、root まで飛んでも VM と一致してしまう。
今後は必ず「最初の候補を reject して次へ行く」テストを primary regression にするべきだねぇ。

---

# 最後に

これはいい方向に進んでいるよ〜。
いま見つかった問題は、かなり深いけど、設計としてはきれいに直せる。

合言葉はこれ。

```text
Aborted は root return ではない。
Aborted は prompt / handler scope return。
```

この設計に変えると、`sub::return` も `undet.once` も、かなり自然な意味に戻ると思うねぇ。
