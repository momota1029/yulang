# 結論

うん、**別物ができている**。

現行 `control-vm` は、archive の control-VM を新しい `mono` IR 上へ移植したものではない。実態は、

> **`mono-runtime` の closure-CPS 型 oracle evaluator を、式だけ `ExprId` arena 化した interpreter**

になっている。

6月13日の契約書は「旧 `yulang-vm` の IR を仕様元にしない」と明記していて、6月14日の最初の runner 実装では、元の stub にあった「control lowering と frame machine を移す」という方針自体が、「`ExprId` で参照する軽量表現を読む」へ差し替わっている。意味論だけ旧作を参考にし、旧作の高速な実行構造を移植しなかった、という経緯だねぇ。

しかも `mono-runtime` は自分自身を「契約検証用の oracle runtime」で、最適化は `control-vm` 側の仕事だと明記している。その oracle と同じ `Rc<dyn Fn>` continuation 表現が、現行 control-VM にほぼそのまま残っている。

これは「堅牢にしたから遅い」わけではないよ〜。検証、構造化エラー、`unsafe` 禁止は主犯ではない。**実行時 continuation の表現を oracle 用のまま本番 VM に持ち込んだこと**が主犯だねぇ。

---

# 何が違うのか

| 項目           | 現行 control-VM                                              | archive control-VM                                |
| ------------ | ---------------------------------------------------------- | ------------------------------------------------- |
| IR           | `ExprId` だけ arena 化。`String`、`Type`、`Pat`、arms、blocks は所有値 | symbol/name/type/list/arms/block/record まで専用 ID 化 |
| 式 dispatch   | `EvalExpr::from_expr` で payload を clone して match           | `ControlExprKind: Copy` をそのまま match               |
| continuation | `Rc<dyn Fn>` の入れ子                                          | `VecDeque<ControlFrame>`                          |
| request 通過   | 古い resume を包む新しい closure を作る                               | `ControlFrame` を一個 push                           |
| resume       | closure chain を仮想呼び出ししながら再生                                | tight loop で frame を pop                          |
| handler      | closure と複数の global active stack                           | handler frame を continuation 内に保持                 |
| call         | 基本は value 化して汎用 `apply_value`                              | known callee・二項 primitive の直呼び fast path          |
| 静的データ        | 実行中にも `Vec`、`String`、`Type` を clone                        | table ID を frame に保持                              |
| local env    | `Rc<HashMap<DefId, Value>>`                                | dense な `ControlLocalId` と COW slots              |

旧作は static payload を別 table に入れ、`ControlExprKind` を `Clone + Copy` にしている。式を読むだけなら heap object を clone しない。

一方、現行 IR は `ExprId` を持っていても、その中に `Vec<String>`、`Type`、`Pat`、`Vec<CaseArm>`、`Block` などが直接入っている。

---

# 一番遅い理由：continuation が heap closure の鎖

現行 runtime の核心はこれだねぇ。

```rust
type Continuation<'a> =
    Rc<dyn Fn(&mut Runtime<'a>, Value) -> RuntimeResult<'a> + 'a>;
```

`Request` 自体がこの closure を持ち、pattern bind 用にも別種の `Rc<dyn Fn>` が複数ある。

途中計算が effect request を返すたび、`continue_with_request` は以前の resume closure を捕捉して、さらに新しい closure で包む。

```rust
resume: Rc::new(move |runtime, value| {
    let resumed = request_resume(runtime, value)?;
    runtime.continue_with_rc(resumed, continuation.clone())
})
```

同じ構造が通常評価、pattern bind、bind-result、value-to-bind に重複している。

したがって、effect が出るまでに未完了だった処理が十個あれば、request は十段の closure chain を持つ。さらに marker frame や catch を通過するたびに別の wrapper が増える。

nondet のような multi-shot continuation では、同じ鎖を枝ごとに何度も踏む。だいたい、

[
\text{cost}
\approx
\text{resume 回数}
\times
\text{未完了 continuation の深さ}
]

となる。これが `(each 1..20 + each 1..20)` で爆発的に見える理由だよ〜。

実測でも `showcase` では、一時点で次の回数が出ている。

* `continue_with_request`: 127,268
* `marker_frame_calls`: 117,802
* `marker_frame_request_closes`: 64,493
* `marker_frame_resume_steps`: 63,554

primitive apply より先に continuation と marker を見るべきだ、とリポジトリ自身の測定にも残っている。

---

# 二番目：marker frame が request のたびに再構築される

現行 marker frame は次の流れになっている。

1. `guard_ids`
2. `active_frames`
3. `active_add_ids`
4. `active_marker_plans`

という四本の global vector に state を push
5. body を実行
6. 全 vector を truncate
7. request なら新しい resume closure を作る
8. resume 時に同じ marker plan をもう一度 push
9. resume 後にまた request が出れば、さらに繰り返す

現在のコードでも、request close はまだ `Rc::new` で resume を包み、その closure 内で marker plan を再導入している。

ここは局所最適化が非常によく効いていて、逆に主犯であることが実証済みだねぇ。

2026年6月18日の改善では、

* scalar value の不要な marker 処理を省略
* value 経路では continuation を `Rc` 化しない
* catch arm path を cache
* path prefix を ID 比較化
* live guard 後の marker check を省略
* multi-shot resume 用 marker plan だけ `Rc<[ValueMarker]>` で共有
* resume marker plan の再正規化を省略

という順で削っている。最新の記録では、

* `nondet_20_discard`: 140〜150ms台 → 107〜118ms
* `showcase`: 350ms台 → 261〜294ms

まで落ちている。counter が変わらないのに時間だけ落ちた部分もあり、marker plan の allocation・clone・正規化が実コストだったことが分かる。

ただし、closure wrapper の**個数そのもの**はまだ残っている。局所最適化で枝葉を軽くしても、木の形は変わっていない。

---

# 三番目：`expr_clones == 0` は正しいが、かなり誤解を誘う

`RuntimeStats` は「full `Expr` clone がゼロ」と記録している。

ところが `eval_expr` は `Expr` を借用したまま処理せず、`EvalExpr::from_expr` という所有 view へ変換している。その変換では、

* `Lit`
* `PrimitiveContext`
* effect path
* `Type`
* `FunctionAdapterHygiene`
* `Pat`
* tuple item vector
* record fields
* variant tag/payload vector
* case arms
* catch arms
* block 全体

を clone している。

だから counter の意味は、

> 大外の `Expr` enum を丸ごと clone していない

だけで、

> 式の静的 payload を clone していない

ではない。

ここは counter 名を `full_expr_clones` に変え、別に次を数えるとよさそうだねぇ。

```text
eval_static_payload_clones
eval_type_clones
eval_pattern_clones
eval_arm_list_clones
eval_block_clones
eval_path_clones
```

本質的な修正は counter 追加ではなく、archive のように payload を ID table 化して `ExprKind` を Copy にすることだよ〜。

---

# 四番目：aggregate 評価が毎ステップ状態全体を clone する

たとえば tuple 評価は、要素を一個評価するたびに closure 内で、

```rust
let mut values = values.clone();
values.push(value);
runtime.eval_tuple_items(items.clone(), env.clone(), values, index + 1)
```

を行う。

record、polyvariant も同じ形だねぇ。

block も各 statement で `stmts.clone()` と `env.clone()` を continuation に捕捉する。

case では arm、scrutinee、arms 全体、env を次 arm 用に clone する。catch request pass-through でも request、arms、env を closure へ持ち直す。

通常 value 経路だけなら optimizer が多少救える箇所もあるけれど、request が出た瞬間に closure が state を所有しなければならず、clone と allocation が実体化する。

archive では、

```rust
ControlFrame::Tuple {
    done,
    items: ControlExprListId,
    next_index,
    env,
}
```

のように、静的 item list は ID、動的 state だけを frame に入れる。

---

# 五番目：環境は改善済みだが、まだ太い

現行 `CapturedEnv` は `Rc<HashMap<DefId, Value>>` の COW になっている。これは良い変更で、以前の clone-everywhere から `showcase` VM eval を約 0.67〜0.70秒から0.39〜0.48秒へ落としている。

ただし、

* lookup のたびに `Value` を clone
* shared env に insert すると HashMap 全体を COW clone
* closure ごとに HashMap handle
* hash lookup
* `Value` が大きな所有 enum

という費用は残る。

instance cache hit も cached `Value` を clone して返す。

ここは archive の `Rc<Vec<(LocalId, Value)>>` をそのまま戻すだけでは不十分だねぇ。旧作も reverse-linear lookup と COW vector clone を持つ。

新実装では、

```rust
struct EnvFrame {
    parent: Option<Rc<EnvFrame>>,
    slots: Box<[Value]>,
}
```

のような lexical frame chain か、persistent slot array が合う。

lower 時に `DefId -> LocalSlot` を確定し、

```rust
env.get(depth, slot)
```

か dense index で読む。binding 一個の追加で HashMap 全体を複製しない形がよいよ〜。

---

# 六番目：pattern binder がかなり重い

現行 binder には分かりやすい二次ボトルネックがある。

## `remove(0)`

```rust
let (pat, value) = entries.remove(0);
```

は残り要素を毎回 shift する。そのうえ continuation は `entries.clone()` を捕捉する。長さ (n) の pattern sequence では、最悪で二次的なコピーになる。

これは即座に、

```rust
bind_pat_sequence(entries, index, env)
```

へ変えられる。

## record pattern

record pattern は各 field ごとに、

* `fields.remove(0)`
* `record_fields` の線形検索
* `HashSet<usize>` の clone
* fields / spread / record_fields / markers / used / env の closure capture

を行う。

spread では未使用 field を再構築し、field name と value を clone する。

ここは frame runtime 後に、

```rust
Frame::BindRecord {
    pattern: RecordPatId,
    field_index: u32,
    value: RecordValue,
    used: SmallBitSet,
    env,
}
```

へ移すとよいねぇ。

---

# 七番目：record 表現と field projection

現行 record は `Vec<ValueField>` で、field projection は末尾から線形検索し、見つけた value を clone する。

同じ field を loop 内で何度も読むコードでは、その都度 O(field count)。

理想は、

```rust
RecordValue {
    shape: RecordShapeId,
    values: Box<[Value]>,
}
```

で、`RecordShape` が `NameId -> offset` を持つ形だねぇ。

重複 field の「後勝ち」規則は lower 時に layout へ反映できる。runtime では offset 一発になる。

archive は `BTreeMap` なので現行より lookup は改善するが、文字列比較と木構造が残る。旧作をそのまま写すより shape record の方がよいよ〜。

---

# 八番目：汎用 call path を踏みすぎる

初期計測では、

* `apply_value`: 90,247
* `apply_marked`: 38,784
* `apply_closure`: 32,836
* `apply_primitive`: 13,158
* `force_thunk`: 23,126

となっている。

現行では、既知 primitive であっても、

1. primitive value を作る
2. 一引数ずつ apply
3. `Vec<Value>` に引数を追加
4. arity を確認
5. 完成時に primitive match

という curried generic path を通りやすい。

archive には、

* `direct_known_callee`
* `direct_binary_primitive_apply`
* `eval_direct_binary_primitive`
* direct closure body entry

があり、既知の二項 primitive なら中間 primitive object を避ける。

ただし、これは continuation rewrite より後でいい。現状は primitive 本体より、その周囲の marker・force・resume の方が太い。

---

# 九番目：active stack scan

request emission のたびに、

* active add-id
* active handler/frame
* guard ID
* path prefix

を走査する。

path interningとprefix ID化で segment comparison はゼロまで落ちたが、wall time は大きく変わらなかった。つまり文字列比較ではなく、**走査回数と continuation 再導入そのもの**が残っている。

marker、handler、blocked effect を同じ continuation frame stack に置けば、global vector を毎回復元・走査する必要が薄くなる。

さらに prompt frame に「直前の handler prompt」「直前の active blocker」への link を持たせれば、request propagation の全 frame reverse scanも避けられる。

---

# 十番目：continuation table が実行中に増え続ける

handler continuation は `ContinuationId` を発行し、`HashMap` へ `Rc<dyn Fn>` を保存する。呼び出し時は `get().cloned()` で、保存側は insert のみだねぇ。

リポジトリ全体で `continuations.remove` は見つからないので、少なくとも一実行中は continuation table が単調増加するように見える。

multi-shot continuation なので一回呼んだら削除、とはできない。ただし frame 化後は、

```rust
Value::Continuation(Rc<ContinuationData>)
```

として continuation value 自身に snapshot を持たせられる。global HashMap lookup と run-lifetime retentionを避けられるよ〜。

arena ID が必要なら、generation付き slabと参照管理にする手もある。

---

# 細いが明確な問題

主犯ではないけれど、frame rewrite 後には見えてくる。

* `BigInt -> i64` が `to_string().parse()`。数値変換としてかなり遠回り。`ToPrimitive::to_i64` 相当を使う方がよい。
* `StringLen`、index、slice が `.chars()` ベースなので、Unicode index は O(n)。仕様として code point index が必要なら index cache や rope/string-tree を検討。
* string splice は prefix/suffixを別々に再構築して `format!`。
* `Value::Marked` は `Box<Value> + Vec<ValueMarker>` なので、小さな値でも wrapper heap allocationが起きる。ただし scalar marker fast pathでかなり軽くなった。
* `run_program` は毎回 `validate(program)` を走らせる。artifact load時に一度検証済みなら、`ValidatedProgram` 型を作って再実行時の validationを省ける。とはいえ VM本体より先に触る場所ではない。

---

# 最短の改善方法：旧作の「continuation 部分」をまず移植する

全部を bytecode VM に作り替える必要はないよ〜。

archive control-VM も、通常 value 経路は再帰 evaluator だ。違いは、**request が出たときだけ未完了計算を data frame にする**ところ。

旧作の continuation はこうなっている。

```rust
struct ControlContinuation {
    frames: VecDeque<ControlFrame>,
    guard_stack: GuardStack,
    lookup_stack: GuardStack,
}
```

`ApplyCallee`、`ApplyArg`、`Tuple`、`Match`、`Block`、`Handle`、`Coerce` などが enum frameとして並ぶ。

resume は単純な loop だねぇ。

```rust
while let Some(frame) = continuation.frames.pop_back() {
    match apply_frame(frame, value)? {
        Value(next) => value = next,
        Request(req) => {
            prepend remaining frames;
            return propagate_request(req);
        }
    }
}
```

実際の旧コードもこの構造になっている。

## 現行からの対応表

```text
continue_with_request
    -> Frame::Then(...)

eval Apply の callee 後
    -> Frame::ApplyCallee { arg, env }

eval Apply の arg 後
    -> Frame::ApplyArg { callee }

eval_tuple_items
    -> Frame::Tuple { items_id, index, done, env }

eval_record_fields
    -> Frame::Record { record_id, index, done, env }

eval_block_step
    -> Frame::Block { block_id, next_index, env }

eval_case_arm
    -> Frame::Case { arms_id, next_index, scrutinee, env }

continue_bind_result
    -> Frame::BindSequence / BindRecord / BindOr

adapt_value
    -> Frame::AdaptValue { source_type_id, target_type_id }

with_marker_plan
    -> Frame::MarkerScope { marker_plan_id, previous_state }

handle_catch_result
    -> Frame::CatchPrompt { arms_id, env, prompt_id }
```

重要なのは、**一部だけ frame 化しないこと**。

すでに試した「`Request.resume` を残したまま `Vec<RequestFrame>` を足す」hybrid は、

* resume steps は35k → 13k
* 20x20では一部改善
* `showcase` は400ms台へ悪化

となって棄却済みだねぇ。closure chain と frame list の両方を維持するので、所有 stateが二重化する。

`Rc<dyn Fn>` を一個も残さず、通常 continuation、bind、marker、handlerを全部 frameへ落とす必要がある。

---

# 推奨する frame runtime の形

```rust
enum EvalResult {
    Value(Value),
    Request(Request),
}

struct Request {
    operation: EffectPathId,
    payload: Value,
    continuation: Continuation,
    guards: GuardSet,
}

struct Continuation {
    frames: FrameStack,
    guard_state: GuardState,
}

enum Frame {
    ApplyCallee {
        arg: ExprId,
        env: Env,
    },
    ApplyArg {
        callee: Value,
    },
    ForceValue,
    AdaptValue {
        source: TypeId,
        target: TypeId,
    },
    Tuple {
        items: ExprListId,
        index: u32,
        done: Vec<Value>,
        env: Env,
    },
    Record {
        record: RecordExprId,
        index: u32,
        done: Vec<Value>,
        env: Env,
    },
    Block {
        block: BlockId,
        next_stmt: u32,
        env: Env,
    },
    Case {
        arms: CaseArmsId,
        next_arm: u32,
        scrutinee: Value,
        env: Env,
    },
    CatchPrompt {
        id: PromptId,
        arms: CatchArmsId,
        env: Env,
        guard_state: GuardState,
    },
    MarkerScope {
        plan: MarkerPlanId,
        previous: GuardState,
    },
}
```

## multi-shot 用 stack

archive の `VecDeque<Frame>` をそのまま clone しても、現行 closure chainよりはかなり良くなるはず。ただし nondet は continuationを何度も複製するので、最終的には persistent chunk stack が合う。

```text
FrameStack
  hot tail: 小さな可変 Vec<Frame>
  parent: Rc<FrameChunk>

FrameChunk
  frames: Box<[Frame]>
  parent: Option<Rc<FrameChunk>>
```

resume用 continuation clone は `Rc` handle cloneだけ。pushが必要になったら hot tailへ追加し、必要時だけ chunk化する。

frame一個ごとの linked `Rc<Node>` は allocation数が増えるので避けたい。**chunk単位の永続化**がよさそうだねぇ。

handler promptの位置も各 chunkに linkを持たせると、continuation splitが全 frame scanではなくなる。

---

# 次に IR を本当に control IR にする

frame runtimeだけで最大の差は埋まるはず。ただ、旧作の10ms前後へ近づけるには、現行の「式だけID化」も卒業する必要がある。

追加する ID はこの辺り。

```text
SymbolId
NameId
EffectPathId
TypeId
PatternId
ExprListId
RecordExprId
CaseArmsId
CatchArmsId
BlockId
MarkerPlanId
RecordShapeId
```

そして hot expression を Copy にする。

```rust
#[derive(Clone, Copy)]
enum ExprKind {
    Local(LocalSlot),
    Lit(LitId),
    Primitive(PrimitiveOp),
    Apply { callee: ExprId, arg: ExprId },
    Tuple(ExprListId),
    Record(RecordExprId),
    Case { scrutinee: ExprId, arms: CaseArmsId },
    Catch { body: ExprId, arms: CatchArmsId },
    ...
}
```

これなら `EvalExpr::from_expr` 自体が消える。

`control_lower` は現在 sub-ms なので、lowering処理を速くする必要はない。**実行時の静的 payload cloneとキャッシュ局所性を改善するためのIR変更**だねぇ。

---

# frame runtime 後の fast path

次の順がよさそうだよ〜。

1. **known primitive saturation**

   * `(+ a b)` を generic curried primitiveではなく `Prim2(IntAdd, a, b)` 相当へ
2. **known closure call**

   * global instanceが lambdaなら closure object生成を省いてbodyへ直接入る
3. **constructor saturation**

   * arity既知なら中間 `ConstructorFunction` を避ける
4. **tail call**
   -現在の continuation topを置換し、新 frameを積まない
5. **force/value fast path**

   * `Thunk::Value` や非thunk既知なら dispatchを省略
6. **record shape projection**

   * field offsetをlower時に確定

旧作は最初の二つをすでに持っている。

---

# CLI 全体が遅い理由は VM だけではない

VMを直しても、`yulang run` 全体には compiler側の太い区間が残る。

2026年6月17日の基準では、

* `collect + load`: 70〜85ms
* `infer`: 270〜350ms
* `showcase build_poly`: 330〜420ms
* `specialize`: 20〜30ms
* `control_lower`: sub-ms

だった。

6月18日の infer最適化後は warm sampleで約254〜273msまで落ちているが、依然太い。主に generalize/quantify、constraint drain、typeclass selection後のSCC routingが残る。

source側は、

* module discoveryの二重full parse回避で collect 39〜41ms → 約8ms
* embedded std loaded-prefix cacheで warm load-only 168ms → 3.17ms

まで改善済み。ただし build全体は約1.17倍しか改善せず、inferが残ることも確認済みだねぇ。

したがって compiler側の次の本命は、parserの小手先ではなく、

> **dependency SCC単位の persistent compiled-unit cache**

になる。

unchanged std / dependencyについて、

```text
LoadedFile
-> inferred typed surface
-> role/impl/effect surface
-> poly
-> specialized instances
-> control artifact
```

を段階的にimportできれば、毎回のinferとruntime loweringを飛ばせる。

---

# 今までの改善で残すもの

これらは正しい方向なので、frame rewriteでも捨てない方がよいよ〜。

* `CapturedEnv` の COW
* scalar marker fast path
* value経路のcontinuation非`Rc`化
* catch arm operation key cache
* effect path interning
* path ID prefix判定
* live guard後のmarker check skip
* resume marker planの限定的共有
* resume marker plan再正規化の省略
* 詳細なruntime counters
* `nondet_20_discard` benchmark

特に marker planの限定共有は、「何でも `Rc` にすれば速い」ではなく、**multi-shotで繰り返しcloneされる箇所だけ共有する**という良い切り方だねぇ。

---

# やらない方がよいもの

## path比較のさらなるmicro-opt

segment比較をゼロにしても大差がなかった。ここを掘り続けても主幹には届かない。

## closure chainを残したhybrid frame

実測で回帰済み。完全移行まで入れない方がよい。

## marker state全体の広い`Rc`化

active marker plan全体の共有は悪化した記録がある。resume用multi-shot pathだけ共有する現在の切り分けが良い。

## `HashMap`のhasher交換だけ

env architectureが支配的なので、数％の話で終わる可能性が高い。

## control lowerの高速化

sub-ms。触る理由がない。

## unsafe dispatch、computed goto

今はdispatch costよりallocation、clone、resume再構築の方が圧倒的。`#![forbid(unsafe_code)]` は維持してよい。

## archive環境表現の丸写し

旧作のenvもlinear lookupとCOW Vec。continuation architectureは移す価値が高いが、envは新しくdense lexical frameとして作った方がよい。

## inferの単純batching

queueをまとめる実験はwork量を増やして悪化した記録がある。生成・replay・再compactそのものを減らす方が筋だねぇ。

## validationを外して速度を稼ぐ

堅牢性を落とす割に主因ではない。検証済みartifact型を作り、二回目以降だけ飛ばす方がよい。

---

# 実装順

### 第1段階：frame runtimeを完成させる

* `Frame`
* `Continuation`
* `Request`
* `resume`
* `apply_frame`

を追加し、通常評価・bind・marker・catchの全closure continuationを置換する。

この段階では現行IRとValue/Envをそのまま使ってよい。

**完了条件**

```text
grep -R "Rc<dyn Fn" crates/control-vm/src
```

がゼロになること。

### 第2段階：marker / handlerをframe stackへ統合

* parallelなactive vectorsを廃止
* prompt frameとblocked frameを導入
* request propagationをframe stack上で行う
* continuation splitをprompt位置で行う

### 第3段階：静的payloadのID化

* arms / block / patterns / types / paths / record layoutsをtableへ
* `EvalExpr`を廃止
* hot `ExprKind`をCopy化

### 第4段階：envとValueの小型化

* dense local slots
* lexical env frames
* scalar inline、heap objectは`Rc`
* continuationをValueが直接保持
* record shape化

### 第5段階：known-call fast path

* direct primitive
* direct closure
* constructor saturation
* tail calls

### 第6段階：compiled-unit cache

* stdとdependency SCCのtyped/runtime surface import
* control artifactのpersistent cache
* validation済みartifact API

---

# ベンチの完了判定

最低でもこの五系統を別々に見るとよさそうだねぇ。

1. `bench/nondet_20_discard.yu`

   * continuation・marker・multi-shot
2. `examples/showcase.yu`

   * 総合
3. pure integer recursion

   * call・primitive・env
4. record / tuple / pattern-heavy

   * aggregate clone・binder
5. ref update / nested handler

   * guard・blocked effect・continuation split

既存 scriptはreleaseが既定で、runtime countersまで拾える。

記録する値は、

```text
median / p90 vm_eval
effect_requests
frame_pushes
frame_steps
frame_stack_clones
frame_clone_count / bytes
max_frame_depth
env_cow_clones
env_cow_entries
value_clone_by_variant
handler_scan_distance
record_field_probes
heap allocation count / bytes
```

がよい。

当面の段階目標としては、

* frame rewrite直後: `nondet_20_discard` 50ms未満
* compact IR・direct calls後: 10〜20ms帯
* `showcase vm_eval`: 100ms未満

あたりを置ける。ただしこれは予測値で、10ms到達を保証する数字ではないよ〜。旧作との入力IR・marker契約・生成コード量が違うので、frame化だけで旧作値まで落ちるとは限らない。

---

# 最終診断

現行の遅さは、主にこの順だねぇ。

1. **`Rc<dyn Fn>` continuation chain**
2. **marker frameのrequest close / resume再構築**
3. **multi-shotによるclosure chainの反復**
4. **式の静的payload clone**
5. **aggregate stateの再帰clone**
6. **HashMap envと巨大な所有`Value`**
7. **pattern binderの二次的コピー**
8. **汎用call・primitive path**
9. **active marker / handler scan**
10. **record線形lookup**
11. **compiler側のinfer再実行**

一番大事なのは、今ある runtime を少しずつ磨き続けないこと。

**現行IRを一度維持したまま、runtime continuationだけをarchive型のdata frameへ完全移行する。**
これが最短で、意味論変更も最小で、現在の測定結果とも完全に整合する道だよ〜。
