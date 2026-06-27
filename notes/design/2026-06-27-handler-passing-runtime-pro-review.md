# Pro review: handler-passing runtime

This file preserves a ChatGPT Pro review of the handler-passing / Koka-style
runtime direction.  The corresponding adopted strategy is summarized in
`notes/design/2026-06-27-handler-passing-runtime.md`.

先に一点だけ。指定のうち

`notes/design/2026-06-27-handler-passing-runtime.md`
`notes/design/2026-06-27-control-vm-performance-pro-review.md`

は、その名前では GitHub 上から取れなかったよ〜。なので、読めた原稿・`ref.update` diagnostics・`performance-localization`・現 runtime 実装を軸に見るねぇ。

## 結論

**Koka-style evidence passing は、Yulang の directed stack weight / hidden evidence にかなり自然に乗る**と思う。
ただし、Koka 風の「effect row に対応する handler evidence を渡す」だけだと足りない。Yulang では **positive evidence** だけでなく、`#id[Empty]` や private tail が表す **negative / hygiene evidence** も runtime evidence に落とす必要がある。

つまり、Yulang 版 evidence passing はこう見るのがよさそうだねぇ。

```text
Koka-ish:
  operation h は evidence[h] を呼ぶ

Yulang-ish:
  operation h は evidence[h] を呼ぶ
  ただし evidence[h] は
    - handler 本体
    - parent forwarding
    - hidden guard/color/blocker
    - callback-origin boundary
    - private residual projection
  を一体で持つ
```

現行の原稿は、static id を runtime color に fresh に写し、同じ scheme instance 内では同じ id が同じ color を指す、という operational interpretation をすでに持っている。さらに operation は color 集合 `κ` を持ち、handler は family が一致し、かつ `κ` が active flow と交わらないときだけ捕捉する、という visibility 定義になっている。これは evidence object に `visible?` と `forward` を持たせる形へほぼそのまま翻訳できるよ〜。

---

## 1. evidence-passing は意味論として自然か

自然だと思う。理由は、原稿の colored semantics がすでに「dynamic handler stack を探す意味論」ではなく、**operation が持つ color と handler 側の visibility 判定**として整理されているからだよ〜。

現在の `Common(L)` は、

```text
Common(L) = ambient(L) ∩ active boundary 全体の effective capability
```

という意味を持ち、protected row は `seed = Empty` の active push により `Common(L)=Empty` になる。つまり「この handler が捕捉してよい family」は静的に `Common(L)` で決まっていて、colored semantics 側ではそれが可視性として実現される。

なので evidence object は単なる handler pointer ではなく、こういうものになる。

```rust
struct Evidence {
    family: EffectFamily,

    // この operation を直接処理する候補
    handler: Option<HandlerEntry>,

    // 捕捉できないときの親 evidence
    parent: Option<EvidenceRef>,

    // directed stack weight / hidden evidence 由来
    hygiene: HygieneRoute,

    // generic VM へ落とす出口
    fallback: Option<FallbackRoute>,
}
```

operation 側はこう。

```text
perform h payload evidence_h =
  evidence_h.invoke(payload, current_continuation)
```

ただし `invoke` は即 handler arm を呼ぶのではなく、

```text
if evidence_h.hygiene.visible_for(h):
    handler(payload, resumption)
else:
    parent.invoke(payload, resumption)
```

に近い。

ここで重要なのは、**stack scan を消しても hygiene 判定は消さない**ことだねぇ。現 VM の marker / guard / active stack scan は runtime 実装の一形態であって、意味論上の本体は color visibility と `Common(L)` にある。だから evidence passing は「marker を消す」ではなく、**marker の意味を persistent evidence route に移す**と見るのが安全だよ〜。

---

## 2. 原稿の意味論に足すべきもの

最小限で足すなら、形式化の優先度はこう。

### 必須

#### evidence parameter

関数型・thunk 型・handler body 型の elaborated core に hidden evidence parameter を足す。

```text
λ(x, ε). e
force thunk[ε]
perform h v using ε_h
```

公開型には出さない。原稿の `generalize` 周辺では id を量化しつつ public scheme に private stack evidence を漏らさない、という方針がすでに重要になっている。`ref.update` diagnostics でも、private evidence が public scheme に漏れたことが問題の本体として整理されている。

#### evidence environment

`ρ` や effect row に対応する hidden environment。

```text
Ε : EffectFamily -> Evidence
```

ただし Yulang では family だけでは足りない。少なくとも次も入る。

```text
Ε : EffectFamily × RouteKey -> Evidence
```

または

```text
Evidence {
  family,
  handler,
  parent,
  blocker_set,
  origin_color_set,
  residual_floor,
}
```

みたいに、route 側に hidden evidence を持たせる。

#### closure / thunk に保存される evidence

ここは必須。callback hygiene の本丸だよ〜。

現行 runtime でも closure は環境を持ち、function adapter は hygiene markers を instantiate して body / arg / ret に分配している。つまり現在の設計でも「関数値を呼ぶときに caller の現在 marker だけを見る」ではなく、adapter が境界を持つ構造になっている。

evidence-passing ではこれを value marker ではなく evidence adapter にする。

```rust
struct Closure {
    code: CodeId,
    env: Env,
    evidence_env: EvidenceEnv,
}

struct FunctionAdapter {
    function: Value,
    arg_evidence_adapter: EvidenceAdapter,
    ret_evidence_adapter: EvidenceAdapter,
    body_evidence_adapter: EvidenceAdapter,
}
```

#### forwarding / yielding

これも必須。`evidence[h]` があっても、その handler が捕捉してよいとは限らないからだねぇ。原稿の colored semantics では、family が一致しても visibility が false なら捕捉できない。

したがって evidence object は必ず

```text
handle or forward
```

を持つ必要がある。

#### resumption object

resumptive handler を扱うなら必須。
local escape だけの prototype なら後回しでいい。

現在の runtime は request に continuation を入れ、handler arm が continuation binder を持つ場合は `request.continuation` を clone して store している。ここが重いし、multi-shot で意味論的にも危ないところだねぇ。

evidence-passing 側の resumption は最低でもこういう形になる。

```rust
struct Resumption {
    frames_or_direct_cont: ContinuationRep,
    evidence_env_at_operation: EvidenceEnv,
    resume_adapter: EvidenceAdapter,
    shotness: Shotness, // OneShot | MultiShot
}
```

`evidence_env_at_operation` を入れないと、resume 後の effect が handler arm 内の evidence で誤捕捉される事故が起きる。

### 後回しでよい

#### generic VM fallback の完全形式化

prototype 段階では、fallback は operational equivalence の対象として別枠に置いてよさそう。

ただし論文・原稿へ入れるなら、いずれ必要になるのは

```text
EvidenceCore ↔ MarkerCore
```

のシミュレーション定理だねぇ。

最初から generic VM fallback を全部形式化すると重すぎる。まずは fallback なしの evidence core を作り、

```text
well-typed evidence elaboration は colored marker core と同じ observable behavior を持つ
```

を主定理にするのがきれい。

---

## 3. `compose` / `sub` callback hygiene はどこで表現するべきか

ここは一番危ない。
結論から言うと、**callback hygiene は evidence object ではなく、function value / function adapter / call boundary に持たせる**のが自然だと思う。

### やってはいけない形

```text
handler の内側で callback f を呼ぶ
  → 現在の evidence_env をそのまま f に渡す
```

これは dynamic scoping になって、callback 由来の effect が内側 handler に捕捉される。現 VM の marker / guard が防いでいる事故そのものだねぇ。

### よい形

```text
f は closure 作成時または引数受け取り時の evidence_env を持つ
handler 内で f v しても、
  f の latent effect は f の evidence_env / adapter 経由で route される
```

言い換えると、関数呼び出し ABI はこう。

```text
call f arg caller_evidence:
  let callee_evidence = adapt(caller_evidence, f.hidden_call_contract)
  f.code(arg, callee_evidence)
```

ただし callback の場合、`adapt` は「内側 handler を追加」ではなく、むしろ **内側 handler を見えなくする blocker を追加**する。

```text
callback adapter =
  evidence_env.with_blocker(
    boundary_id = u,
    allowed = Empty or declared callback row
  )
```

これは原稿上の `take(Empty)` / protected row に対応する。原稿では fresh internal effect variable の positive occurrence が既定で `take(Empty)` として保護され、明示 wildcard annotation を通るときだけ `take(All)` が与えられる。

### `compose` のイメージ

```yulang
compose(f, g)(x) = f(g(x))
```

ここで `f` と `g` の latent effects を、compose 本体の現在 handler に勝手に流し込まない。

evidence IR では、

```text
compose(f, g, ε_compose):
  return closure x with captured:
    ε_f = evidence required by f
    ε_g = evidence required by g
    boundary = callback boundary from function types

closure(x, ε_call):
  y = g.call(x, adapt_callback(ε_call, ε_g_boundary))
  z = f.call(y, adapt_callback(ε_call, ε_f_boundary))
  return z
```

みたいになる。

ポイントは、`ε_call` をそのまま `f` / `g` に渡さないこと。
`f` / `g` の function type に含まれる hidden evidence adapter を通す。

### `sub` のイメージ

`sub` が「handler に渡す computation / callback」を受け取るような形なら、subtyping / adapter がまさに hygiene 変換になる。

既存 VM の `FunctionAdapterHygiene` が body / arg / ret markers を持っているのと同じで、evidence-passing では

```text
FunctionAdapterHygiene
  marker list
```

を

```text
FunctionAdapterEvidence
  body_evidence_transform
  arg_evidence_transform
  ret_evidence_transform
```

に置き換える感じだねぇ。

---

## 4. `ref.update` はどう扱うべきか

`ref.update` は最初から evidence-passing の direct path に入れない方がいい。
これは std のただの特殊 primitive ではなく、**callback hygiene の canary** だからだよ〜。

diagnostics では、問題の最小因子が

1. data-position effectful function
2. local wildcard handler
3. handler arm 内 callback

の三つだと切り分けられている。

さらに、private にすべき単位は public effect variable `e` ではなく、data 内 function arrow の latent return-effect boundary だと整理されている。`κ` は field return 専用 private tail、`s` は private stack id、`erase(κ)=e` は ordinary row だけの対応で、`κ` と `e` の双方向 alias は張らない、という設計だねぇ。

だから evidence-passing でも、`ref.update` をこう扱うと危ない。

```text
ref.update(f):
  state handler evidence の内側で f を呼ぶ
```

これは callback effect を state handler が拾う方向へ寄る。

安全な形はこう。

```text
ref.update(ref, f):
  old = get(ref)        // local state evidence
  new = f.call(old)     // f 自身の callback evidence route
  put(ref, new)         // local state evidence
```

`f.call(old)` は state handler の evidence ではなく、`f` の closure / adapter が持つ evidence route で呼ぶ。ここが実装できるまでは、`ref.update` は generic fallback に残すのがよさそう。

現 runtime でも `ref_update` は `request_is_ref_update` で特別扱いされ、request continuation を assigned value で resume している。つまり今の `ref.update` は普通の local state primitive というより、request/resume と深く結びついた高階 primitive になっている。

私ならこう切る。

```text
Phase A:
  get / put / local cell だけ evidence direct 化

Phase B:
  callback evidence adapter が完成

Phase C:
  ref.update を direct primitive 化

それまでは:
  ref.update は generic VM fallback
```

---

## 5. native backend を先に進めても高速化は限定的か

うん、限定的だと思う。
「native 化で interpreter dispatch は減る」が、「generic control VM の構造的コスト」は残る。

現 runtime は effect request ごとに `Request` を作り、`guard_ids`、`carried_guards`、`handler_boundary`、payload、continuation を持たせ、その後 active markers で request を marking している。

さらに request marking は `active_add_ids` を走査し、path prefix や carried guard を見て request に guard を積む。

continuation 側も、capture clone / invoke clone / frame clone の統計があり、frame 数や marker scope 数を数えている。これは native backend にしても、同じ抽象表現を使う限り消えない費用だねぇ。

リポジトリの performance-localization でも、runtime の太い項目として `active_add_ids` 全走査、resume step ごとの marker scope touch、continuation snapshot clone、request ごとの guard / carried marker construction が挙がっている。

なので順序としては、

```text
native backend
  < evidence-passing / direct-style lowering 設計
```

だと思うよ〜。

もちろん native backend を完全に止める必要はない。けれど「現 generic VM の native 化」は、VM のまま速くする話で、設計上は `request / marker / continuation` の高コストモデルを固定化しやすい。

performance-localization でも direct-style / pure island は後回し扱いながら、方向としては effect-free region を direct-style SSA/register VM へ落とし、control region だけ handler VM に残す、と書かれている。native backend はその後に戻す方針だねぇ。

---

## 6. 現実的な実装順

私ならこう切る。

## Phase 0: oracle / fallback を固定

現行 control VM は残す。
役割は二つ。

```text
1. behavior oracle
2. unsupported effect の fallback
```

この段階で performance gate に

```text
- public signature canary
- callback hygiene canary
- ref.update canary
- nondet/parser canary
- marker-heavy workload
```

を入れる。既存の performance plan でも、release gate で public signature canary、runtime smoke、marker-heavy workload、continuation clone 系 metric を見る方針がある。

## Phase 1: Evidence IR だけ作る

まだ速くしない。
mono/control IR の横に evidence IR を生やす。

```rust
struct EvidenceFunction {
    code: CodeId,
    value_params: Vec<Param>,
    evidence_params: Vec<EvidenceParam>,
    body: EvidenceExpr,
}

enum EvidenceExpr {
    Perform {
        family: EffectFamily,
        op: OperationId,
        payload: ExprId,
        evidence: EvidenceSlot,
    },
    Handle {
        family: EffectFamily,
        body: ExprId,
        handler_evidence: EvidenceSlot,
        parent_evidence: EvidenceSlot,
    },
    Call {
        callee: ExprId,
        arg: ExprId,
        evidence_args: EvidenceArgList,
    },
    FallbackToVm {
        reason: FallbackReason,
        expr: ExprId,
    },
}
```

最初の成功条件は「現行 VM と同じ結果になる」ではなく、

```text
どの operation site がどの evidence slot を要求するか dump できる
```

で十分。

## Phase 2: callback boundary evidence adapter

ここを先にやる。
local escape より前でもいいくらい。

`FunctionAdapterHygiene` 相当を evidence adapter に落とす。

```rust
struct EvidenceAdapter {
    blockers: Vec<Blocker>,
    projections: Vec<PrivateProjection>,
    parent_links: Vec<ForwardingLink>,
}
```

この段階で `compose` / `sub` / parser choice / nested handler residual の public canary を固定する。performance plan でも public canary と `apply` / `compose` / parser choice / nested handler residual を固定する方針が出ている。

## Phase 3: local escape

最初に direct 実行する subset は **local escape** がいいと思う。

理由は単純。

```text
- resumption object が不要
- multi-shot continuation が不要
- handler evidence の direct call だけ検証できる
- callback hygiene と分離しやすい
```

形はこう。

```text
perform escape(v, ε_escape)
  → ε_escape.exit(v)
```

この subset では `Request` を作らない。
`marker scan` もしない。
continuation capture もしない。

## Phase 4: first-order local state

次に `get` / `put` のような first-order local state。

```rust
struct StateEvidence<T> {
    cell: Cell<T>,
    parent: Option<EvidenceRef>,
    hygiene: HygieneRoute,
}
```

ここでは `update(f)` はまだ入れない。
`get` / `put` だけで

```text
local handler evidence
operation direct call
parent forwarding
generic fallback boundary
```

を試せる。

Koka は row-polymorphic effect types と Hindley–Milner style inference を持ち、state effect の安全な encapsulation も扱う、という意味では local state evidence の先行例として近い。ただし Yulang は hidden directed evidence を持つので、Koka の public row evidence だけでは callback-origin hygiene までは表せない、という差がある。([arXiv][1])

## Phase 5: one-shot resumption

state handler や parser の一部を one-shot に制限して、resumption object を導入する。

```rust
struct OneShotResumption {
    cont: MovedContinuation,
    evidence_at_perform: EvidenceEnv,
}
```

one-shot なら clone を避けやすい。
ここで初めて continuation representation の設計に入る。

## Phase 6: multi-shot nondet / parser

最後。
nondet/parser は高速化インパクトが大きいけど、最初に触るには危ない。

理由は、

```text
- continuation clone / sharing / replay が本質
- evidence_env も continuation と一緒に複製される
- state evidence と混ぜると linearity / multi-shot safety が難しい
- fallback と direct path の混在バグが出やすい
```

現行 runtime でも multi-shot 的な continuation clone が統計対象になっているので、ここは最後に専用設計で攻める方がいい。

## Phase 7: `ref.update`

`ref.update` はここ。
理由は、`ref.update` が

```text
local state
+ data-position effectful function
+ callback evidence routing
+ private tail projection
```

を同時に踏むからだねぇ。

diagnostics でも、`κ <: e` / `e <: κ` の普通の alias ではなく、scope-close 時の projection が必要だと整理されている。evidence runtime でも同じで、private evidence を public evidence env に alias してはいけない。

---

## 形式化するなら、この形が一番きれい

原稿に足す章案としてはこう。

```text
Section A: Evidence Core
  values V ::= closure(code, env, Ε) | thunk(e, env, Ε) | ...
  evidence Ε ::= family ↦ ev
  ev ::= handler(parent, hygiene, arm) | forward(parent) | fallback(vm_scope)

Section B: Evidence Elaboration
  directed stack weight L/R から EvidenceAdapter を作る
  PWeight(L,T) は evidence route に blocker/guard を追加
  NWeight(R,T) は resume / escaping route に blocker を追加
  Filter は static check 後に消す

Section C: Operation
  perform h v under Ε:
    invoke Ε[h] with payload v and current continuation

Section D: Handler
  handle h body with arm:
    parent = Ε[h]
    Ε' = Ε[h ↦ handler(parent, hygiene_from_Common, arm)]
    eval body under Ε'

Section E: Function / thunk
  closure は Ε_def を保存
  call は caller Ε をそのまま渡さず、function type adapter で Ε_call を作る

Section F: Resumption
  resumption は continuation + evidence_at_perform + resume_adapter

Section G: Simulation
  evidence core の評価は colored marker core と同じ observable operation/return を持つ
```

この章で一番大事な定理はたぶんこれ。

```text
Theorem: Evidence hygiene soundness

source typing が directed stack weight constraints を満たし、
その elaboration が evidence core を生成するなら、
callback-origin effect は hidden boundary が許す handler にだけ捕捉される。
```

証明は既存の colored semantics をかなり使えるはず。
`Common capturability` は、handler が捕捉できる family が `Common(L)` と同値だと示している。
weighted row split も、捕捉可能な最大 head が `K ∩ Common(L)` だと整理されている。

つまり evidence-passing 側で示すべきなのは、

```text
evidence adapter が作る blocker/forwarding route は
colored marker の guard/paint と同じ visibility を実現する
```

という lemma だねぇ。

---

## 危険な落とし穴

### 1. evidence をただの handler pointer にする

これは壊れる。
Yulang では handler pointer だけでなく、

```text
この callback 由来 effect をこの handler が捕捉してよいか
```

が hidden evidence に入っている。

### 2. closure に evidence env を保存しない

これも callback hygiene が壊れる。
関数呼び出し時の current evidence をそのまま使うと、dynamic scoping になる。

### 3. private tail を public tail と alias する

`κ <: e` と `e <: κ` の普通の alias は避けるべき。diagnostics でも、必要なのは scope-close 時の projection であって solver graph 上の恒久 equality edge ではない、と明記されている。

runtime evidence でも同じで、

```text
private evidence route κ
public evidence route e
```

を同じ object にしてはいけない。

### 4. `All` / wildcard を「何でも捕捉可能」に潰す

明示 wildcard と protected callback boundary は別物。
`take(All)` は公開された wildcard annotation 由来、`take(Empty)` は callback hygiene の保護境界。ここを同じ evidence にすると壊れる。

### 5. fallback 境界で recolor / reblock しない

direct evidence path から generic VM に落ちるとき、current hidden blockers を VM request marker に変換する必要がある。逆に VM から direct evidence に戻るときも evidence route を再構成する必要がある。

### 6. multi-shot continuation に mutable evidence を持たせる

nondet/parser で continuation を複数回 resume するなら、evidence env は persistent / clone-safe である必要がある。local state evidence をそのまま mutable cell として持つと、multi-shot で状態共有事故が出る。

---

## native 化より先に evidence-passing を設計すべきか

**設計は evidence-passing が先。実装は小さい subset から。**

native backend を先にすると、現 VM の

```text
Request
marker scan
guard construction
continuation clone
generic resume loop
```

を native に固定しやすい。
今ほしいのは「Rust interpreter を C/LLVM に移す」ではなく、**effect operation の実行モデルを stack search から evidence call に変えること**だと思うよ〜。

ただし direct-style / pure island 全体を先にやる必要はない。
最小 prototype はこれで十分。

```text
1. evidence IR dump
2. callback evidence adapter
3. local escape direct runtime
4. first-order local state direct runtime
5. fallback bridge
6. one-shot resumption
7. multi-shot nondet/parser
8. ref.update
```

一番小さく勝つなら、

```text
local escape + no-resume handler
```

が初手。
一番 Yulang らしい canary を守るなら、

```text
callback evidence adapter
```

を最初に入れる。
一番 runtime speed に効くのは nondet/parser だけど、これは最後でいい。焦って触ると continuation と hygiene を同時に壊しやすい。

私の推し順は、

```text
callback evidence adapter
→ local escape
→ first-order local state
→ fallback bridge
→ one-shot resumption
→ nondet/parser
→ ref.update
```

だねぇ。

[1]: https://arxiv.org/abs/1406.2061?utm_source=chatgpt.com "Koka: Programming with Row Polymorphic Effect Types"
