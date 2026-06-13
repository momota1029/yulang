# 計算を伴う変数取得と値制限

2026-06-13 決定。specialize / elaborate に入る前に、infer は各 binding について
「その変数を取得しただけで計算が走るか」を記録し、その情報を量化境界と SCC 判定へ使う。

この仕様は、式そのものの `Evaluation::{Value, Computation}` と別に、
binding を参照する操作の性質を定義する。関数 body が計算を含むことと、関数値を取得することは
別物である。関数値の取得は value であり、body の計算は apply した後にだけ起きる。

## 目的

次のような binding は、参照されるたびに本体の計算を走らせる可能性を持つ。

```yu
my x = make()
my a = 1 + 1
```

この `x` や `a` を、値 binding と同じように通常量化してしまうと、使用箇所ごとに fresh な
型・role requirement・効果残差を作れるように見えてしまう。しかし runtime では同じ計算結果を
共有するか、同じ計算を再実行するかのどちらかであり、use-site ごとの自由な instantiate とは
意味が合わない。

一方、関数定義は取得時点では値である。

```yu
my id = \x -> x
my f x = g x
my g x = f x
```

`id` / `f` / `g` を取得しても body は実行されない。再帰関数 SCC はこの理由で許される。
計算が起きるのは、取得した関数値を apply した後である。

## 用語

infer は各 runtime binding に、次の metadata を持たせる。

```text
BindingFetch =
  | FetchValue
  | FetchComputation
```

- `FetchValue`
  - 変数を取得しても計算は走らない。
  - literal、constructor value、lambda、関数 item、recursive lambda の self binding など。
  - 関数 body の effect / evaluation はここへ混ぜない。
- `FetchComputation`
  - 変数を取得すると、その binding の RHS 計算を評価する必要がある。
  - 関数リテラル外の直接 apply、effectful block、取得時に force が必要な thunk 相当の binding など。
  - `make_id()` が関数を返す場合でも、外側の `make_id()` を走らせるため binding fetch は
    `FetchComputation` である。

式 lowering が持つ `Evaluation` は「その式を今評価する時に計算か」を表す。
`BindingFetch` は「binding を名前で取得する時に計算か」を表す。
両者は似ているが、関数境界で必ず分かれる。

## metadata の作り方

binding の RHS を lower した時点で、その binding の fetch 性質を決める。

1. RHS が関数値そのものなら `FetchValue`。
   - function item
   - lambda
   - labelled `case` / `catch` / `for` など、lowering 後に recursive lambda として扱われるもの
2. RHS の外側が literal / record / variant constructor / tuple などの値構造だけなら `FetchValue`。
3. RHS の外側で apply、method selection の実行、effectful block、force 相当の操作が必要なら
   `FetchComputation`。
4. function boundary の内側にある計算は、外側 binding の fetch 性質へ伝播しない。

この判定は名前文字列ではなく、lowered expression の構造と `Evaluation` から行う。
型推論の途中で `path == ...` や fixture 名を見る分岐を足してはならない。

## 参照 edge への伝播

名前解決後の direct ref / resolved typeclass ref / method member ref は、参照先 `DefId` と一緒に
`BindingFetch` を SCC machine へ渡す。

概念的には `UseResolved` が次の形になる。

```text
UseResolved {
  parent: DefId,
  target: DefId,
  use_value: TypeVar,
  fetch: BindingFetch,
}
```

`fetch` は参照元の式形ではなく、参照先 binding の性質で決まる。
`f` を bare ref として渡す場合も、`f x` の callee として使う場合も、
`f` の取得が value なら `FetchValue` である。apply 自体の計算は別の `Evaluation` として扱う。

## 量化境界

`FetchValue` の binding は従来どおり、binding の local generalize boundary で量化してよい。

`FetchComputation` の binding は、取得時に走る計算で生まれた型変数を、その binding の scheme へ
量化してはならない。実装上は、該当する変数の level を量化境界より 1 段外側へ引き上げる
（数字としては 1 つ小さくなる）か、同等の non-generic 集合として扱う。

この引き上げ対象には、主型に直接出る型変数だけでなく、次も含まれる。

- RHS 計算で生まれた role / typeclass predicate の入力変数
- RHS 計算で生まれた effect row / stack residual の変数
- RHS 計算で生まれ、annotation や associated type 経由で surface へ漏れうる変数

つまり、計算を伴う binding の scheme は「この計算を use-site ごとに fresh に instantiate できる」
という形を持ってはならない。必要な requirement は親の level、またはより外側の owner に残る。

例:

```yu
my a = 1 + 1
```

`Add` requirement が `a` の local scheme に量化されるのではなく、親 level へ残る。
これは role-system の「明示的な計算がある level は 1 つ上がる」規則と同じ方向の制限である。

## SCC でのエラー

複数の runtime 関数・定義を含む SCC の内部に `FetchComputation` edge が入った場合、その SCC は
不正である。

```yu
my a = make(b)
my b = make(a)
```

この group では、`a` を得るには `make(b)` を計算する必要があり、その中で `b` が必要になる。
逆も同じである。これは純粋な再帰関数参照ではなく、計算を伴う値取得の循環である。
principal scheme と specialize の demand だけでは、実行順序・共有・再実行を一意に決められない。

一方、次は許される。

```yu
my f x = g x
my g x = f x
```

`f` / `g` の取得は関数値の取得であり、body は apply 後に走る。
SCC の内部 edge は `FetchValue` なので、通常の再帰関数 group として扱う。

SCC machine は component を merge する時点、または ready component を取り出す直前に、
次を満たす component を診断として落とす。

1. component が複数の runtime root を持つ。
2. component 内部 edge の少なくとも一つが `FetchComputation`。

診断には、component members と、問題になった ref span / `parent` / `target` を渡せる形にする。
表示文言は diagnostics 側で作り、SCC machine は構造化された原因だけを返す。

単一 binding の `FetchComputation` は、この仕様だけではエラーにしない。
値制限により量化されない binding として扱う。ただし self-recursive な computed value を
別診断にする必要が出た場合は、multi-root SCC とは別の規則として切る。

## top-level 実行需要

top-level binding が `FetchComputation` の場合、その binding は未参照でも program の実行需要に入る。

```yu
my a = say "Hello"
```

この `a` は、値として参照された時に RHS 計算を走らせる binding である。top-level に現れている以上、
program 実行時にもその計算を評価する必要がある。したがって、specialize / mono へ渡す runtime root には、
裸の top-level expression だけでなく `FetchComputation` top-level binding も source order で含める。

一方、`FetchValue` top-level binding は、それ自体では runtime root にならない。
未使用の関数定義や literal binding は、明示 entrypoint、裸式、computed binding などから到達した場合にだけ
specialize される。

## specialize / elaborate への前提

specialize / elaborate は、infer output に次の情報があることを前提にする。

- 各 exported binding の `BindingFetch`
- top-level `FetchComputation` binding が runtime root として source order に残っていること
- `FetchComputation` binding で量化してはならない変数が scheme quantifier に入っていないこと
- `FetchComputation` edge を含む multi-root SCC が infer 段階で診断済みであること

後段は infer の constraint graph や level を覗かない。
したがって、この値制限は scheme metadata と ref table に残す必要がある。
後段が scheme だけを見て「この参照は instantiate してよい普通の値か、取得時に計算を走らせる
binding か」を推測してはならない。

## 実装上の置き場所

- lowering / analysis
  - RHS の `Evaluation` と function boundary から binding ごとの `BindingFetch` を決める。
  - direct ref / typeclass ref 解決後の `UseResolved` に `fetch` を載せる。
- SCC machine
  - use edge に `BindingFetch` を保持する。
  - component 内部の `FetchComputation` edge と multi-root component を診断へ変換する。
  - `FetchValue` edge は従来の recursive function edge と同じ扱いにする。
- generalize
  - `FetchComputation` binding では、取得時計算で生まれた変数を 1 段外側へ引き上げてから
    scheme を作る。
  - role predicate / effect residual / stack residual も同じ owner level で扱う。
- export
  - `BindingFetch` を scheme metadata または binding table として外へ出す。
  - diagnostics に使う span / ref identity は erased IR 側の `RefId` と対応できる形にする。

## 禁止事項

- `Any` を fallback として入れて値制限を回避すること。
- `Never` を placeholder として入れて循環を消すこと。
- def 名・path 文字列・fixture 名で `FetchValue` / `FetchComputation` を決めること。
- SCC で問題が見えた後に、表示用 scheme を書き換えて循環を隠すこと。
- specialize 側で infer の内部 level を覗いて、この metadata を復元しようとすること。
