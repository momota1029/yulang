見立てとしては、**catch 全体を provider env として active に積む方向は捨てるのが正解**だと思うよ〜。壊れた理由はかなりはっきりしていて、provider env が「handler の dynamic scope」みたいに振る舞うと、callback hygiene marker が本来ブロックするはずの callback 由来 operation まで、direct route に乗ってしまうからだねぇ。

今の実装はすでに良い部品を持ってる。slot は `Positive / Blocked / UnknownFallback` に分かれていて、operation は lowering に応じて positive / blocked / fallback slot へ落ちる構造になってる。`UnknownFallback` は `ProviderRoute::NeedsEvidenceEnv` へ対応していて、まさに「後から evidence env が来たら direct 化できる」場所だよ〜。

## 結論

`action: [flip] _` はこう解釈するのが自然だと思う。

> この action value は、`flip` 用の handler evidence capability を **明示的な action activation 境界**で受け取れる。
> ただし、その capability は callback / adapter hygiene を突破しない。

つまり「catch の handler が action 内の `flip` を捕捉してよい」ではあるけど、より正確には、

> **callee が action を force/apply する時、その action activation にだけ `fallback(flip) -> handler(flip)` の grant を渡してよい**

だねぇ。
「catch 全体で handler を active にする」ではない。

---

## 1. handler hygiene を保った evidence passing の意味論

意味論は **ambient handler stack** じゃなくて、**typed provider capability passing** に寄せるのがよさそう。

operation 解決は次の順番。

1. 既存の lexical direct route があるなら、それを使う
2. direct がない operation は fallback slot のままにする
3. active な provider capability があり、slot と handler object が一致し、かつ hygiene gate が通る時だけ direct route に昇格
4. hygiene gate が通らない時は request VM に落とす

今の `RuntimeEvidenceRunContext` は、plan 由来の route index、value provider env、operation provider lookup を持っていて、active provider env から route を引く導線もすでにあるねぇ。

ただし、ここに **hygiene gate** が足りない。

今の `effect_route_for_operation_call` は、既存 route が direct でなければ active provider env を見て provider route を返す流れになってる。
このまま provider env を catch 全体へ積むと、callback marker が付いている operation でも direct handler が決まってしまい、`visible_operation_resumptive` 側の marker 判定を通らない。`Direct { handler == catch_expr }` の request は catch 側でそのまま arm に入るからだねぇ。

なので route はこう分けたい。

```rust
enum EvidenceEffectRoute {
    Direct {
        handler: ExprId,
        resumptive: bool,
        execution: EvidenceVmOperationExecutionPlan,
    },
    ProviderCandidate {
        provider_frame: RuntimeEvidenceProviderFrameId,
        handler: ExprId,
        handler_id: u32,
        resumptive: bool,
        execution: EvidenceVmOperationExecutionPlan,
        hygiene: ProviderHygieneGate,
    },
    Unhandled,
}
```

`ProviderCandidate` は、request 作成直前に marker 状態を見て、

* clean なら `Direct`
* callback / adapter marker に遮られるなら `Unhandled`

へ落とす。

最初の実装ならもっと保守的に、

> provider env を導入した時点から、新しい callback/delayed marker が積まれていない時だけ direct 化

で十分だと思うよ〜。これなら `debug_runtime_evidence_run_resumes_carried_callback_markers` の `run roots [6]` は守れる。あの test は、`strip_tick` が callback `f` の `tick::ping()` を横取りしないことを要求しているからねぇ。

---

## 2. provider env を導入・消去する境界

provider env は **catch 全体**ではなく、次の境界で導入するのがよいと思う。

### 導入する境界

| 境界                                  | 何をするか                                                                          |
| ----------------------------------- | ------------------------------------------------------------------------------ |
| `catch action:` の action activation | action の effect contract に従って provider grant を作る                               |
| thunk force                         | `Thunk::Expr` を force する間だけ provider env を active にする                          |
| function apply                      | effectful function argument を apply する間だけ provider env を active にする            |
| function adapter body               | adapter が callback boundary を作らない、または contract 側で明示的に許可された時だけ provider env を流す |
| continuation resume                 | resumptive handler で再開した action continuation 内に provider env を復元する             |

今の runtime は `Closure` / `Thunk::Expr` / `FunctionAdapter` に provider env を載せていて、apply/force の間だけ `with_provider_env` で active stack に積む形になってる。

ただ、`with_provider_env` は今だと push して run して truncate するだけで、request が返った時に continuation へ provider env を閉じ込めていない。
resumptive handler を考えるなら、これは足した方がいいねぇ。

marker frame は request が出た時に marker を continuation 側へ閉じる設計になっている。provider env も同じ扱いにしたい。

```rust
enum EvidenceContinuationFrame {
    ProviderEnv {
        provider_env: RuntimeEvidenceProviderEnv,
        marker_baseline: ProviderMarkerBaseline,
        next: EvidenceContinuation,
    },
    // ...
}
```

そして `with_provider_env` は、

```rust
match result {
    Value(v) => Value(v),
    Request(req) => Request(req.wrap_provider_env(provider_env, baseline)),
}
```

にする。

### 消去する境界

provider env は、

* action force/apply が value で終わったら pop
* request が出たら continuation frame に閉じ込める
* continuation resume が終わったら pop
* handler scope から escape した provider grant は無効化

という扱いがよさそう。

ここで重要なのは、provider env が **runtime value と一緒に無制限に逃げない**こと。逃げてもいいけど、その場合は `provider_scope_id` を持たせて、scope が active でない時は provider route lookup から無視する。

---

## 3. runtime value のどこに evidence capability を載せるか

二種類に分けるのがきれい。

### A. lexical capture evidence

これは今のままでよいと思う。

* `Closure.provider_env`
* `Thunk::Expr.provider_env`
* `FunctionAdapter.provider_env`

value 作成位置で active な handler を capture する用途だねぇ。実装もすでにこの形になっている。

### B. contract-passed evidence

これは closure/thunk の中身に直接混ぜない方がいい。

代わりに、外側 wrapper にする。

```rust
enum RuntimeEvidenceValue {
    Provided {
        value: SharedValue,
        provider_env: RuntimeEvidenceProviderEnv,
        scope: EvidenceProviderScopeId,
        contract: EvidenceContractId,
    },
    // existing values...
}
```

理由は三つ。

1. 同じ thunk/action が別々の handler に渡される可能性がある
2. provider grant は callee の handler scope に依存する
3. closure/thunk 自体へ混ぜると、handler scope を越えて capability が漏れやすい

なので、

* lexical evidence は closure/thunk/adapter の field
* contract evidence は `Provided` wrapper
* 実行中の evidence は continuation frame / active provider frame

に分けるのがいいよ〜。

`action: [flip] _` の actual argument は、callee 側で handler evidence を受け取る時に `Provided(thunk, grant)` へ包む。force/apply は `Provided` を剥がしつつ provider env を active にする。

---

## 4. `action: [flip] _` を runtime evidence object としてどう表すか

annotation は「path 文字列」ではなく、slot id ベースの contract に落とすのが自然。

plan 側にはこういう object がほしい。

```rust
struct EvidenceVmEffectContractPlan {
    id: u32,
    owner: EvidenceContractOwner,
    latent_kind: EvidenceLatentKind, // Thunk | Function | Adapter
    required_slots: Vec<u32>,        // fallback slot ids: [flip]
}

enum EvidenceContractOwner {
    Param { function: ExprId, def: DefId },
    Local { def: DefId },
    Thunk { expr: ExprId },
    FunctionArg { apply: ExprId },
}
```

handler 側 grant はこう。

```rust
struct EvidenceVmProviderGrantPlan {
    contract_id: u32,
    demand_slot_id: u32,     // UnknownFallback(flip)
    provider_slot_id: u32,   // Positive(flip)
    handler_id: u32,
    handler_expr: ExprId,
    execution: EvidenceVmOperationExecutionPlan,
}
```

runtime 側はこう。

```rust
struct RuntimeEvidenceProviderGrant {
    demand_slot_id: u32,
    handler_id: u32,
    route: EvidenceEffectRoute,
    scope: EvidenceProviderScopeId,
    hygiene: ProviderHygieneGate,
}
```

`action: [flip] _` は、

> `UnknownFallback(flip)` を要求する latent computation で、callee は `Positive(flip)` の handler object から grant を作れる

という contract だねぇ。

今の object graph は handler object / operation object / provider plan まである。handler object は positive slot を持ち、operation object は slot と candidate handler を持つ。
さらに provider index は same-family handler candidates を slot ごとに集めている。

この上に `EffectContractPlan` を載せると、path 文字列分岐なしで行ける。

一点、今の `RuntimeEvidenceProviderEnv::provides` は `slot_id` と `handler_id` の一致だけを見る。
ここは `contract_id` / `scope_id` / `hygiene gate` も見る形に拡張したい。

---

## 5. Koka 的 evidence passing に寄せる時、multi-shot continuation と hygiene marker をどこまで残すか

**marker は残す。fallback request VM も残す。**
ここは削らない方がいいねぇ。

削っていいのは、条件が証明できた fast path だけ。

| execution plan         | continuation |      marker scan | 方針                               |
| ---------------------- | -----------: | ---------------: | -------------------------------- |
| `DirectAbortive`       |           不要 | clean grant なら不要 | 最優先 fast path                    |
| `DirectTailResumptive` |   原則不要、または最小 | clean grant なら不要 | tail resume 証明がある時だけ             |
| `YieldFallback`        |           必要 |               必要 | multi-shot / guarded / may-yield |
| `BlockedFallback`      |           必要 |               必要 | hygiene を守る                      |
| `GenericFallback`      |           必要 |               必要 | 既存 VM に逃がす                       |

handler arm classification はすでに `Abortive / TailResumptive / MayYield / Fallback` を持っていて、`DirectAbortive` と `DirectTailResumptive` へ落とす判定もある。

なので Koka 的に寄せるなら、

* `DirectAbortive`: handler body を直接呼ぶ、request continuation を作らない
* `DirectTailResumptive`: `k x` が tail に一度だけ出る証明がある時だけ、continuation object を作らず direct jump
* `MayYield`: continuation object を残す
* callback marker が provider entry 後に増えたら direct をやめる

がよさそう。

特に `DirectAbortive` の最適化はかなり安全に増やせる。今の runtime でも abortive direct request では continuation append を避ける分岐がある。
さらに `Thunk::Effect` 作成時にも direct abortive なら active marker marking を省く分岐がある。

ただし contract provider 由来の direct abortive は、**clean-since-provider-entry** が必要。callback marker が積まれていたら `BlockedFallback` / `Unhandled` に戻す。

---

## 6. direct handler call へ下ろせる条件をどの層で証明するか

三層に分けるのがいいよ〜。

### 型層で証明すること

型層は「この value がどの effect capability を受け取れるか」だけを証明する。

* `action: [flip] _` は latent effect row に `flip` を持つ
* `action` 内の unhandled `flip` は `UnknownFallback(flip)` slot を要求する
* handler は `Positive(flip)` slot を提供する
* callback boundary を越えて勝手に handler を流してはいけない

Koka の row effect 的な部分はここだねぇ。Koka は effect を型に出す設計なので、Yulang でも annotation は runtime ad-hoc ではなく contract object に落とすのが筋だと思う。([arXiv][1])

### plan 層で証明すること

plan 層は direct 化候補を作る。

* slot id の対応
* provider handler object の候補
* operation object の execution plan
* handler arm が `Abortive` / `TailResumptive` か
* delayed boundary / callback boundary を越える可能性
* `ProviderRoute::BlockedByHygiene` を direct lookup 対象から外す

今の plan は operation lowering と execution plan を持っている。
ここに `EffectContractPlan` と `ProviderGrantPlan` を足すのが自然。

### runtime 層で検査すること

runtime は型の再証明をしない。見るのは動的事実だけ。

* provider scope が active か
* provider frame 以後に callback marker が積まれていないか
* active marker が handler を block しないか
* continuation resume 時に provider frame を復元するか
* direct が unsafe なら fallback request に落とす

runtime で path 文字列を見て分岐するのは避けて、`slot_id / handler_id / contract_id / scope_id` で見る。

---

## まず入れるなら、この順番が良さそう

### 1. provider lookup を hygiene-safe に締める

今の `operation_provider_lookups_from_plan` は `DirectHandlerCall` だけ除外し、それ以外は provider candidates から route を作る余地がある。
まずここを絞る。

* `HygieneFallback` は provider env だけで direct 化しない
* `delayed_boundary=true` は direct 化しない
* `GenericFallback` は contract grant がある時だけ候補化
* `BlockedByHygiene` provider route は lookup しても direct へ返さない

### 2. `RuntimeEvidenceProviderFrame` を作る

今の active stack は `Vec<RuntimeEvidenceProviderEnv>` だけ。
これを frame 化する。

```rust
struct RuntimeEvidenceProviderFrame {
    env: RuntimeEvidenceProviderEnv,
    scope: EvidenceProviderScopeId,
    marker_plan_len_at_entry: usize,
    active_add_id_len_at_entry: usize,
    active_handler_frame_len_at_entry: usize,
}
```

provider route lookup は `env` だけでなく、この baseline も見る。

### 3. provider env continuation frame を足す

`with_provider_env` が request を返した時、provider env を continuation に閉じ込める。これをしないと、resumptive handler の `k` 再開後に evidence が落ちる危険がある。

### 4. contract object を plan に足す

`action: [flip] _` から、

```text
contract c0:
  owner action
  latent thunk
  requires [fallback(flip)]
```

を作る。

`catch action:` の handler object から、

```text
grant g0:
  c0 fallback(flip) -> h0 positive(flip)
```

を作る。

### 5. `Provided` wrapper を足す

callee 側で action を force/apply する直前に、

```rust
Provided {
    value: action,
    provider_env: grant_env,
    scope,
    contract,
}
```

へ包む。force/apply は wrapper を剥がして `with_provider_env_frame` する。

### 6. direct fast path は clean frame だけ

最初はこの条件でいいと思う。

```text
provider_frame is clean
AND provider scope active
AND slot_id matches
AND handler_id matches
AND execution is DirectAbortive or DirectTailResumptive
```

callback marker が入ったら direct をやめて fallback。
これで `showcase / nondet` の action-thunk 系は direct 化の入口ができて、callback hygiene regression は守れるはずだよ〜。

---

## かなり短く言うと

`action: [flip] _` は **handler を ambient に増やす宣言**じゃなくて、**その action activation に `flip` provider capability を渡せる契約**。

provider env は catch 全体に積まない。
`Provided(action, grant)` を force/apply する間だけ active にする。
request が出たら provider env を continuation frame に閉じる。
callback marker が provider entry 後に積まれていたら direct 化せず fallback に落とす。

これが一番、Koka 風 evidence passing と Yulang の callback hygiene の折り合いがよさそうだねぇ。

[1]: https://arxiv.org/abs/1406.2061?utm_source=chatgpt.com "Koka: Programming with Row Polymorphic Effect Types"
