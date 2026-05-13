# Hidden Effect Evidence

この文書は、Yulang の effect handler hygiene を支える hidden evidence の実装仕様をまとめる。
リファレンス向けの説明は `web/docs/reference/type-theory.md` と
`web/docs/ja/reference/type-theory.md` に置く。この文書は、実装名と実装上の責務境界を追う
ための補遺である。

焦点は次の 2 点である。

- handler が、関数引数や thunk から発生した effect を勝手に捕捉しないように推論すること。
- そのための内部制約や runtime evidence を、通常の型表示や hover に漏らさないこと。

より理論寄りの背景は `notes/design/handler-row-subtraction.md` に置く。この文書は、現在の
実装でどの層が何を持つかを追えるようにするための仕様である。

## 基本方針

公開される effect row は、通常の row 型だけである。

```text
α [io, state | ε] -> [ε] β
```

`[; ε]`、`shift`、`peel`、`handler_match` は公開型ではない。これらは型構文ではなく、
推論器・typed IR evidence・runtime/native control evidence の間でだけ使う内部情報である。

```text
Type / CompactType / hover:
  ordinary row only

Solver:
  HandlerMatchEdge(actual, keep, handled, residual)

typed IR:
  PrincipalEvidence.handler_matches

Runtime IR:
  LocalPushId / PeekId / FindId / AddId

Native CPS:
  FreshGuard / PeekGuard / FindGuard / AddThunkBoundary
```

この分離により、推論上は boundary hygiene を保持しつつ、表層型は従来の simple-sub row として
読める。

## Keep

handler body が thunk / 関数引数由来の computation を見るとき、その effect row のどの表層
effect を handler から見えるままにするかを `keep` と呼ぶ。

```rust
pub enum ShiftKeep {
    None,
    Surface,
    Set(Vec<Path>),
}
```

意味は次の通り。

| keep | 意味 |
| --- | --- |
| `None` | 未注釈引数。表層 effect も handler から隠す。 |
| `Surface` | `[_]` 注釈。すでに表層にある effect だけ handler から見える。 |
| `Set(paths)` | `[io, state]` のような注釈。指定された表層 effect だけ handler から見える。 |

`Surface` は「boundary を消す」ではない。すでに奥にある effect を表層へ戻さない。runtime の
dispatch でも、すでに blocked な effect は外側の `Surface` boundary を通っても再露出しない。

## 推論で何をするか

`catch` lowering は、handler が処理する effect を見つけても、handler body の effect row を
直接 `[handled | rest]` の形へ開かない。

代わりに、残余 effect 用の fresh row 変数を作り、横の制約として `handler_match` を記録する。

```text
actual   = handler body の effect row
handled  = handler arm が処理する effect atom
residual = handler を抜けた後の残余 effect row
keep     = actual に登録されている boundary keep

record_handler_match(actual, keep, handled, residual)
```

実装上の入口は `crates/yulang-infer/src/lower/expr/catch.rs` の catch lowering である。
`record_handler_match` は `crates/yulang-infer/src/solve/constrain/handler_match.rs` にある。

`keep` は effect row の型変数に紐づく side table として記録される。

```rust
effect_boundary_keeps: FxHashMap<TypeVar, ShiftKeep>
```

未登録の場合は `Surface` として扱う。これは普通の直接 computation では handler が表層
effect を処理してよい、という通常規則に対応する。

## HandlerMatchEdge

solver 内部の hidden 制約は次の形である。

```rust
pub struct HandlerMatchEdge {
    pub actual: TypeVar,
    pub keep: ShiftKeep,
    pub handled: Vec<NegId>,
    pub residual: TypeVar,
    pub cause: ConstraintCause,
}
```

概念的には、これは次の関係を表す。

```text
residual = actual から handler が捕捉できる表層 handled effect だけを除いた row
```

ただし、`actual` が naked type variable の場合、solver は row を発明しない。

```text
handler_match(ε, Surface, {io}, ρ)
```

ここから次のように開いてはいけない。

```text
ε = [io | rest]
ρ = rest
```

これは simple-sub の graph に「表層に `io` がある」という情報を勝手に足すことになる。
この発明が thunk hygiene の破綻につながる。

## 解く条件

現在の実装は保守的である。

`HandlerMatchEdge` は、`actual` の positive lower bound として closed row が見えたときだけ、
その row の表層 item を走査して解く。

```text
actual lower = [io, state]
keep         = Surface
handled      = {io}

residual lower = [state]
```

このとき solver は、消した item と handler 側 atom の型引数も同じ制約で合わせる。

`keep = None`、または `handled` が空、または `keep` と `handled` が交わらない場合は、
handler は何も捕捉できないので、`actual <= residual` として同一方向へ流す。

一方、次のものは現在の solver では無理に解かない。

- `actual` が naked type variable の場合。
- `actual` が upper bound や compact view としてだけ見えている場合。
- `Set(paths)` の selective keep。
- open tail を含む row から residual を部分構成する場合。

これらは hidden evidence として残る。今の実装は、推論を鋭くしすぎるより、row shape を
発明しないことを優先する。

## typed IR evidence

`handler_match` は型には入れないが、機械向け metadata として typed IR に残す。

```rust
pub struct PrincipalEvidence {
    pub expected_edges: Vec<ExpectedEdgeEvidence>,
    pub expected_adapter_edges: Vec<ExpectedAdapterEdgeEvidence>,
    pub derived_expected_edges: Vec<DerivedExpectedEdgeEvidence>,
    pub handler_matches: Vec<HandlerMatchEvidence>,
}

pub struct HandlerMatchEvidence {
    pub id: u32,
    pub source_range: Option<SourceRange>,
    pub actual_effect: TypeBounds,
    pub keep: DelimiterKeepEvidence,
    pub handled: Vec<TypeBounds>,
    pub residual_effect: TypeBounds,
    pub closed: bool,
    pub informative: bool,
    pub runtime_usable: bool,
}
```

`handler_matches` は debug evidence ではなく、principal evidence の一部として export される。
ただし、通常の型表示はこれを読まない。これは module import、runtime lowering、debug tooling
のための machine metadata である。

## どのように隠すか

hidden evidence は、次の経路から意図的に外す。

- `Type`
- `Scheme`
- compact type
- hover 表示
- 通常の `check` 出力
- 通常 diagnostics

表示側が見るのは、ordinary type graph と solved substitution だけである。

```text
solved:
  residual = [state]
  -> 表示に反映してよい

pending:
  handler_match(ε, Surface, {io}, ρ)
  -> 表示には出さない
```

pending の `handler_match` を表示しない理由は、ユーザーが書いた型ではないからである。
公開型に出すと、`[; ε]` や `handler_match(...)` のような内部 artifact が言語仕様に見えて
しまう。

その結果、内部的には違う hidden evidence を持つ 2 つの関数が、同じ表層型を持つことがある。
これは正常である。表層型は「値と通常 row の関係」を表し、hidden evidence は「handler から
どの boundary が見えるか」を別に表す。

## 例: 表層型は同じで hidden evidence が違う場合

```yulang
my compose_plain f g x = f(g x)
my compose_surface f (g: _ -> [_] _) x = f(g x)
```

どちらも公開型は同じ形になりうる。

```text
compose_plain   : (α [γ] -> [δ] β) -> (ε -> [γ] α) -> ε -> [δ] β
compose_surface : (α [γ] -> [δ] β) -> (ε -> [γ] α) -> ε -> [δ] β
```

違いは hidden evidence にある。

```text
compose_plain:
  keep = None

compose_surface:
  keep = Surface
```

この差は、handler body の内側で effect を捕捉してよいかどうかに効く。表層型だけでは、
両方とも「引数 `g` の effect が `f` 側の effect row へ流れる」ことしか見えない。

## 例: hidden evidence が表層型にも反映される場合

`catch` が実際に effect を処理できる shape まで見える場合は、solved residual が通常 row として
型に反映される。

```yulang
act out:
    pub say: str -> ()

our run_plain(x) = catch x:
    out::say o, k -> run_plain(k ())
    v -> v

our run_surface(x: [_] _) = catch x:
    out::say o, k -> run_surface(k ())
    v -> v
```

未注釈引数は `keep = None` なので、handler は引数由来の `out` を捕捉できない。

```text
run_plain : α -> α
```

`[_]` は表層 effect を見せるので、`out` を処理した residual が公開型にも現れる。

```text
run_surface : α [out; β] -> [β] α
```

ここで見えている `[out; β]` は公開 row の compact 結果であり、`handler_match` 自体を表示して
いるわけではない。

## runtime lowering

typed IR evidence は runtime IR で guard boundary に落ちる。

主な node は次の通りである。

```rust
ExprKind::LocalPushId { id, body }
ExprKind::PeekId
ExprKind::FindId { id }
ExprKind::AddId { id, allowed, active, thunk }
```

考え方はこうである。

1. handler scope に入ると fresh guard id を作る。
2. thunk boundary は、その guard id と allowed effect を `AddId` として thunk に付ける。
3. thunk を force して effect が発生したとき、allowed に含まれない effect はその guard で
   blocked と見なす。
4. handler search は、自分の guard snapshot に blocked guard が含まれていれば、その handler
   frame を捕捉候補から外す。

これにより、「型 row の全 effect に番号を振り直す」のではなく、実行時の handler search で
捕捉可能性を判定する。

## native CPS lowering

native CPS では runtime の `AddId` を `AddThunkBoundary` に落とす。

```rust
CpsStmt::AddThunkBoundary {
    dest,
    thunk,
    guard,
    allowed,
    active,
}
```

CPS/CPS-repr evaluator は thunk / resumption / return frame に active boundary snapshot を
保持する。Cranelift scalar path では、thunk pointer に active blocked guard masks を保存し、
thunk force 中だけ thread-local active boundary stack へ積む。

`Perform` は次の 2 種類の blocked 情報を合わせて handler を探す。

- lowering 時点で静的に分かる blocked guard。
- thunk force 中に active boundary stack から分かる blocked guard。

このため native 側でも、未注釈 thunk 由来の effect は内側 handler を飛ばし、対応する
boundary の外側へ出てから捕捉される。

## 不変条件

実装は次の不変条件を守る。

1. `handler_match` は `Type` / `CompactType` に入れない。
2. `shift` / `peel` / delimiter は型構文にしない。
3. `actual` が naked type variable のとき、solver は handled effect を発明しない。
4. solved residual だけを ordinary row として表示へ反映する。
5. pending hidden evidence は normal hover / `check` / diagnostics に出さない。
6. typed IR には `PrincipalEvidence.handler_matches` として machine metadata を残す。
7. runtime/native は型 row を持ち込まず、guard boundary と handler search で衛生性を実行する。
8. shallow handler の resumption は handler frame 自身を含まないが、boundary evidence は
   continuation / thunk 側に残す。

## 今後の拡張余地

現在の solver は意図的に保守的である。次に鋭くできる場所は次の通り。

- `Set(paths)` の selective keep を closed row に対して解く。
- open tail を含む row で、既知 prefix だけを削り tail 側に handler_match を残す。
- debug mode で `handler_match` を直接出さず、`boundary: hidden` / `boundary: surface` のような
  人間向け注記として表示する。
- LSP hover に、通常 hover とは別の opt-in debug hover を用意する。

ただし、どの拡張でも、naked type variable から effect row shape を発明しないことを最優先に
する。
