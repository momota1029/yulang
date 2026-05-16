かなり筋が見えてると思うよ〜。
この症状は **「cast が悪い」じゃなくて、「semantic value の型制約」と「render / Display / Debug / statement sink の制約」が同じ unification レーンに乗っている」** 匂いが強い。

結論から言うと、主戦場は **1 + 3 + 4** だねぇ。
**2 は原因切り分け用の verifier として入れる価値が高い**けど、根本の不変条件ではなさそう。

---

## 結論: 切るべき invariant

一番大事な invariant はこれ。

> **branch join / handler value arm / fold result の result type は semantic type だけで決める。**
> `Display` / `Debug` / render / test-output / statement-discard は、join の外側にある sink adaptation として扱う。

ただし、ここは雑に

> `std::bytes::bytes` を semantic branch result に入れてはいけない

とは切らないほうがいいよ〜。
ユーザーコードが本当に bytes を返す branch は合法なはずだからねぇ。

正確にはこう。

> **render-origin の `std::bytes::bytes` 制約を semantic branch result に流してはいけない。**
> bytes 型そのものではなく、**bytes に至った origin** が問題。

つまり `bytes` にラベルを付けるというより、**constraint / evidence に origin を持たせる**のが筋だと思う。

---

## 4 つの質問への答え

### 1. origin 分離で見るべきか

うん、ここが第一候補だよ〜。

でも invariant はこう切るのが安全。

```text
Ty::Bytes is allowed as a semantic type
only when it is demanded by semantic constraints.

Ty::Bytes produced by Render / Display / Debug evidence
must not constrain semantic branch joins.
```

たとえばこの 2 つは完全に別物として扱う。

```text
semantic:
  branch result type = std::bytes::bytes
  because both arms explicitly produce bytes

render:
  value type = T
  render obligation: Display(T) => std::bytes::bytes
```

後者で `T ~ std::bytes::bytes` を立てると壊れる。
`Display(T)` は **T を bytes に変える semantic cast** じゃなくて、**render sink が T を bytes として出力するための evidence** だねぇ。

---

### 2. generic specialization の mono signature 検証は必要か

必要。ただし **主修正ではなく、爆発を早く検出するための backstop** だと思う。

generic fold / junction / handler が絡むなら、mono 化後にこれを assert したい。

```text
mono_signature == normalize(subst(scheme_signature))
```

もう少し細かく言うと、

```text
forall quantified vars αᵢ in scheme:
  instantiate αᵢ -> fresh βᵢ

after solving:
  mono params/result must be a single substitution instance
  of the original scheme signature
```

ここで検出したいのはこういう汚染。

```text
scheme:
  fold : ∀A B. List<A> -> B -> (B -> A -> B) -> B

bad mono:
  fold : List<X> -> Unit -> (...) -> Bytes
```

あるいは、

```text
junction : ∀T. ... -> T
```

の `T` に対して、semantic に必要ない `Display(T) -> bytes` や statement `unit` expectation が混ざるケース。

ただ、mono signature verifier は **漏れた後に気づく仕組み**。
漏れそのものは context / evidence の分離で止めるほうがいいねぇ。

---

### 3. implicit cast / Display / Debug evidence をどう保持するか

ここはかなり大事。

`principal_unify` の中で全部を runtime expr に即時適用しないほうがいい。
特に今回の stale cast application は、たぶん

```text
未正規化の型変数に対して cast evidence を作る
↓
後で substitution が進む
↓
古い from/to のまま runtime expr に cast を巻く
```

みたいな流れが起きている可能性が高い。

おすすめは evidence を 4 種類くらいに分けること。

```rust
enum EvidenceKind {
    SemanticCoerce, // T -> U。意味論上の型変換
    Render,         // T -> bytes。表示 sink 専用
    Discard,        // T -> unit。statement sink 専用
    Join,           // arms -> common semantic type
}
```

より厳密には `Display` / `Debug` は `Render` の中で使う trait evidence であって、`SemanticCoerce` ではない。

```rust
enum RenderFlavor {
    Display,
    Debug,
    Repr,
    TestOutput,
}
```

そして `principal_unify` はこういうものを返す。

```text
PrincipalResult {
  subst,
  typed_ir_with_semantic_types,
  evidence_obligations,
}
```

この段階では runtime expr へ直接 cast を巻かない。
後段の elaboration で、substitution を正規化してから evidence を具体化する。

```rust
fn elaborate_evidence(ev: Evidence, subst: &Subst) -> LoweredEvidence {
    let from = subst.normalize(ev.from);
    let to   = subst.normalize(ev.to);

    match ev.kind {
        EvidenceKind::SemanticCoerce => {
            // from/to が semantic に妥当な cast なら runtime expr へ巻く
        }
        EvidenceKind::Render => {
            // render sink の場所でだけ bytes-producing expr を作る
        }
        EvidenceKind::Discard => {
            // statement sink の場所でだけ unit-producing expr を作る
        }
        EvidenceKind::Join => {
            // semantic join の型一致だけを見る
        }
    }
}
```

ここで重要なのは、

```text
Render(T) produces bytes,
but it does not change the semantic type of the original expression.
```

という扱い。

---

### 4. branch join / handler value arm / fold result のどこで止めるか

漏れ止めは **複数層で置く**のがいいと思うよ〜。
ただし主 invariant は一つ。

```text
semantic result を決める層では render/discard evidence を見ない
```

#### A. branch join

branch join はこうあるべき。

```text
arm₁ : A
arm₂ : A
----------------
if ... then arm₁ else arm₂ : A
```

statement context で使われているからといって、

```text
arm₁ : unit
arm₂ : unit
```

を先に押し込むと危ない。

代わりに、

```text
if ... then arm₁ else arm₂ : A
discard(if ... then arm₁ else arm₂) : unit
```

にする。

CPS ならこういう形。

```text
lower_expr(e: A, k: K<A>)
lower_stmt(e: A, k_unit: K<Unit>) =
    lower_expr(e, KDrop(k_unit))
```

render も同じ。

```text
lower_render(e: A, k_bytes: K<Bytes>) =
    lower_expr(e, KRender(Display, k_bytes))
```

つまり、

```text
K<Unit>    // statement continuation
K<Bytes>   // render continuation
K<A>       // semantic continuation
```

を混ぜない。

今回の

```text
branch result type mismatch: expected unit, got std::bytes::bytes
```

は、まさに `K<Unit>` と `K<Bytes>` のどちらか、または両方が branch arm の semantic continuation として扱われている感じがあるねぇ。

---

#### B. handler value arm

effect handler は特に危ない。

handler はだいたいこういう型構造になる。

```text
handle body with
  value x -> value_arm
  op ...  -> op_arm
```

ここで invariant はこれ。

```text
value_arm result type == handler expression result type
op_arm result type    == handler expression result type
```

ただし、`op_arm` の中に `resume` や logging / debug / render があっても、それらは handler result type を決めてはいけない。

危ない形はこれ。

```text
value_arm : T
debug(value_arm) : bytes
handler result accidentally becomes bytes
```

正しくは、

```text
handler : T
render(handler) : bytes
```

---

#### C. fold result

generic fold では accumulator / result type を sealed にするとよさそう。

```text
fold<A, B>(
  xs: List<A>,
  init: B,
  step: B -> A -> B
) -> B
```

この `B` に対して、render や statement の期待型が unify し始めると終わる。

なので fold body の検査では、

```text
step result must be B_semantic
fold result is B_semantic
```

を固定して、外側の context は後段で adapt する。

```text
fold(...) : B
discard(fold(...)) : unit
render(fold(...))  : bytes
```

`fold(...) : unit` や `fold(...) : bytes` に直接寄せないほうがいい。

---

## かなりおすすめの設計: `Expected<Ty>` を生の `Ty` にしない

今回のバグの根っこは、たぶん expected type がこうなっていること。

```rust
expected: Option<Ty>
```

これだと、

```text
statement context -> expected unit
render context    -> expected bytes
semantic context  -> expected T
```

が全部同じ `Ty` として流れる。

ここをこう変えるとだいぶ安全。

```rust
enum Expectation {
    InferValue,
    Value(Ty),              // semantic expectation
    StatementSink,          // produce unit by discard
    RenderSink(RenderFlavor), // produce bytes by render
}
```

あるいは、

```rust
struct Expected {
    mode: ExpectedMode,
    ty: Option<Ty>,
    origin: Origin,
}

enum ExpectedMode {
    SemanticValue,
    StatementSink,
    RenderSink,
}
```

そして rule はこれ。

```text
ExpectedMode::SemanticValue
  -> unification constraints を作ってよい

ExpectedMode::StatementSink
  -> semantic type を infer した後、Discard evidence を作る
  -> T ~ unit は作らない

ExpectedMode::RenderSink
  -> semantic type を infer した後、Render evidence を作る
  -> T ~ bytes は作らない
```

この変更が一番「原因に近い層」だと思う。

---

## `principal_unify` での具体的な invariant

`principal_unify` にはこういうガードを入れるといい。

```text
Semantic unification may consume only semantic constraints.

Render / Display / Debug obligations are not equality constraints.
Statement unit expectations are not equality constraints.
```

疑似コードだとこう。

```rust
fn add_constraint(c: Constraint) {
    match c.origin.kind {
        OriginKind::Semantic
        | OriginKind::Annotation
        | OriginKind::GenericInst
        | OriginKind::BranchJoin
        | OriginKind::HandlerJoin
        | OriginKind::FoldStep => {
            constraints.push(c);
        }

        OriginKind::Display
        | OriginKind::Debug
        | OriginKind::Render
        | OriginKind::TestRender => {
            render_obligations.push(RenderObligation {
                value_ty: c.source_ty,
                flavor: c.origin.render_flavor,
                sink: c.origin.sink,
            });
        }

        OriginKind::StatementUnit
        | OriginKind::Discard => {
            discard_obligations.push(DiscardObligation {
                value_ty: c.source_ty,
                sink: c.origin.sink,
            });
        }
    }
}
```

もちろん実際には `Constraint` の形が違うと思うけど、思想はこれ。

**`Display(T)` は `T == bytes` ではない。**
**statement context は `T == unit` ではない。**

ここを守ると、今回の `unit` と `bytes` の衝突はかなり自然に消えるはずだねぇ。

---

## stale cast application は「削る」じゃなくて「正規化後に再分類」

cast を削ると `["1"]` になるという観察はかなり重要。
それは、その cast の一部が本当に semantic に必要ということを示していると思う。

だからやるべきことは、

```text
stale cast を消す
```

ではなく、

```text
evidence を保持する
substitution 後に from/to を normalize する
その時点で semantic cast / render / discard / identity を再分類する
```

だねぇ。

たとえばこう。

```rust
struct Evidence {
    expr_id: ExprId,
    from: Ty,
    to: Ty,
    kind: EvidenceKind,
    origin: Origin,
}

fn finalize_evidence(ev: Evidence, subst: &Subst) -> FinalEvidence {
    let from = subst.normalize(ev.from);
    let to = subst.normalize(ev.to);

    match ev.kind {
        EvidenceKind::SemanticCoerce => {
            if from == to {
                FinalEvidence::Identity
            } else {
                FinalEvidence::RuntimeCast { from, to, origin: ev.origin }
            }
        }

        EvidenceKind::Render => {
            FinalEvidence::Render {
                input_ty: from,
                output_ty: Ty::Bytes,
                origin: ev.origin,
            }
        }

        EvidenceKind::Discard => {
            FinalEvidence::Discard {
                input_ty: from,
                output_ty: Ty::Unit,
                origin: ev.origin,
            }
        }

        EvidenceKind::Join => {
            FinalEvidence::Join {
                ty: to,
                origin: ev.origin,
            }
        }
    }
}
```

これなら stale な wrapper をそのまま使わず、でも必要な意味論上の cast は残せる。

---

## runtime lowering / validation 側での assert

runtime lowering は根本修正の場所ではないけど、assert を置く価値は高い。

### branch lowering 直前

```text
for branch join:
  join_ty must be semantic
  arm result tys must equal join_ty after semantic coercions
  render evidence must not appear inside join evidence
  discard evidence must not appear inside join evidence
```

### statement lowering

```text
statement expr:
  lower expr with its semantic type A
  then route through Discard(A -> unit)
```

### render lowering

```text
render expr:
  lower expr with its semantic type A
  then route through Render(A -> bytes)
```

### generic mono lowering

```text
mono signature must be subst instance of scheme signature
no render-origin obligation may constrain quantified result vars
```

この assert が落ちたら、かなり原因位置に近いログが取れる。

---

## ログに出すと一気に見える情報

今回の失敗なら、次の trace があると一発で「最初の悪い edge」が見えると思う。

```text
expr_id
node kind: branch / handler / fold / junction / render / stmt
semantic_ty before subst
semantic_ty after subst
expected mode: SemanticValue / StatementSink / RenderSink
constraint origin
evidence kind
from_ty -> to_ty
```

特に探すべきなのはこの 2 種。

```text
BranchJoin result R ~ bytes
  origin = Display / Debug / Render / TestRender
```

または、

```text
BranchJoin result R ~ unit
  origin = StatementUnit / Discard
```

このどちらかが出たら、そこが漏れ口だねぇ。

---

## たぶん今回の直接原因として一番ありそうな形

症状から見ると、こんな流れがかなりありそう。

```text
junction / handler / fold の result type R がある
↓
テスト harness か display path が R を表示しようとする
↓
Display(R) evidence が必要になる
↓
それが RenderObligation ではなく R ~ bytes として principal_unify に混ざる
↓
一方で branch / handler / statement lowering は unit continuation を期待する
↓
runtime validation:
  expected unit, got bytes
```

あるいは statement context 側から見ると、

```text
branch expression used as statement
↓
expected unit が arm に押し込まれる
↓
その arm の中で display/render が bytes を作る
↓
branch join が unit と bytes の混合になる
```

どちらでも、修正方針は同じ。

```text
branch / handler / fold は semantic result を返す
statement は discard sink
render は render sink
```

---

## 優先順位つき修正案

### 1. `Expected` を mode つきにする

最優先。

```rust
enum ExpectedMode {
    Semantic,
    StatementSink,
    RenderSink,
}
```

`StatementSink` で `expected = unit` を渡さない。
`RenderSink` で `expected = bytes` を渡さない。

---

### 2. evidence を semantic / render / discard に分ける

`Display` / `Debug` を `Cast` と同じ箱に入れない。

```text
SemanticCoerce: changes semantic type
Render: observes semantic value and produces bytes at sink
Discard: observes semantic value and produces unit at sink
```

---

### 3. branch join の evidence から render/discard を締め出す

branch join の common type は semantic constraints だけで決める。

```text
JoinEvidence may contain SemanticCoerce
JoinEvidence must not contain Render
JoinEvidence must not contain Discard
```

---

### 4. handler / fold result type を semantic に seal する

handler value arm と fold accumulator/result は、外側の sink から切り離す。

```text
handler : H
fold    : B
```

その後に、

```text
discard(handler) : unit
render(fold)     : bytes
```

を付ける。

---

### 5. mono signature verifier を入れる

generic specialization 後に、

```text
mono_sig == subst(scheme_sig)
```

を assert。

これは根本修正というより、再発防止と原因特定用の強い番犬だねぇ。

---

## 最小パッチっぽく始めるなら

大改造の前に、まずこの 3 つの assert を入れるのがよさそう。

```text
assert no Render-origin equality constraint reaches principal_unify
assert no StatementUnit-origin equality constraint reaches branch join
assert mono signature is a single substitution instance of scheme signature
```

それから `Display` / `Debug` evidence を cast list から分離する。

一番避けたいのは、

```text
if cast looks stale, drop it
```

という修正。
これは今見えている通り、意味論上必要な cast まで落として `["1"]` みたいな別バグになる。

---

## まとめると

今回の invariant はこう切るのが一番きれいだと思うよ〜。

```text
Semantic IR:
  branch / handler / fold / junction result type is semantic only.

Evidence:
  semantic cast is allowed to affect semantic type.
  Display / Debug / render is not a semantic cast.
  statement unit is not a semantic expected type.

Lowering:
  semantic expr lowers to K<T>.
  statement context wraps K<T> with Drop -> K<Unit>.
  render context wraps K<T> with Render -> K<Bytes>.
```

なので、問いへの答えを一行ずつにするとこう。

```text
1. yes。ただし bytes 型禁止ではなく render-origin bytes の semantic join 流入禁止。
2. yes。generic mono signature verifier は入れる。根本修正というより漏れ検出。
3. Display/Debug は cast ではなく render evidence。principal_unify では保持し、subst 後に elaboration。
4. branch join / handler value arm / fold result では semantic type だけを見る。unit/bytes への変換は外側の sink で行う。
```

この設計だと、cast を消さずに stale application だけ潰せるし、`unit` と `bytes` の衝突もかなり原因に近い場所で止められるはずだねぇ。
