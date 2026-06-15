# specialize2: mono 用 simple-sub 型推論

2026-06-15 決定。`specialize2` は、既存 `specialize` の延長ではなく、
`poly` の主型と erased IR を材料にして、mono 化のための simple-sub 型推論をもう一度行う後段である。

この文書は [`2026-06-07-principal-monomorphization.md`](2026-06-07-principal-monomorphization.md)
の後継仕様である。2026-06-07 版に残る「expected type を手渡して demand を作る」記述は、
`specialize2` の根拠にしない。

## 主旨

infer は principal scheme を作る。`specialize2` は、その principal scheme を使って
「今回の実行で必要になった mono instance」の型をもう一度推論する。

重要なのは、型が再帰的に決まっていくことだ。

1. ある式や定義 body を mono 推論タスクとして読む。
2. 式 node ごとに mono 用の型変数を置く。
3. literal、ref、apply、selection、cast、handler などから simple-sub と同じように制約を集める。
4. 変数の上下界をまとめ、cast rule や invariant 分解で必要な制約を増やしながら、各変数を単一 concrete type へ解く。
5. 式全体に型が付いたら、参照している多相関数・typeclass member・cast 関数へ concrete signature を代入し、次の mono 推論タスクを積む。
6. 新しい task でも同じことを行う。
7. 到達したすべての task が concrete に解けたら `mono::Program` を生成する。

したがって `specialize2` は「expected type を callee に渡す elaborator」ではない。
`specialize2` は「poly 主型から始める第2の simple-sub 推論器」と「解けた代入で再帰的に
mono instance を作る demand expander」である。

## 入力

`specialize2` が信用してよい入力は次だけである。

- `poly::Arena` の erased expression / pattern / statement
- `RuntimeRoot`
- `DefId -> Scheme`
- `RefId -> DefId`
- `SelectId` の解決結果
- role impl / typeclass impl candidate table
- cast rule table
- constructor / effect operation / field projection metadata
- runtime hygiene に必要な metadata

式 node ごとの infer 済み型、infer の内部 constraint graph、途中の compact 表現、表示用に整えた
dump 型は入力にしない。

## 禁止事項

`specialize2` では次を禁止する。

- `signature_for_scheme(def, scheme, None)` のような入口で、量化変数を `unit` / pure effect に
  既定化して instance 型を作ること
- 型が決まらない場所を `Any` に逃がすこと
- 型が決まらない場所を `Unknown` として mono へ流すこと
- 出力型が分からないことを理由に、callee の主型を閉じること
- method / typeclass / primitive を path 文字列の局所分岐で決めること
- mono 生成中に型推論を局所的に走らせ、先に解いた mono 推論結果と切り離すこと

未確定の型は mono 推論タスク内の type variable として保持する。
上下界をまとめても concrete type が一つに決まらないなら specialize error である。

## MonoInferTask

`specialize2` の基本単位は `MonoInferTask` である。

```text
MonoInferTask =
  | RootExpr(ExprId)
  | ComputedDef(DefId)
  | DefBody(DefId, ConcreteSignature)
  | LocalFunction(LocalDefId, ConcreteSignature)
  | ImplMember(ImplMemberDefId, ConcreteSignature)
  | CastRule(CastDefId, ConcreteSignature)
```

`DefId` だけを見て mono instance を作らない。必ず、その定義が今回どの concrete signature で
使われるかを表す `ConcreteSignature` と組にする。

root expression のように外から出力型が与えられていない task では、result type は制約収集から
決まる。関数引数や別関数 body の中で使われる task では、呼び出し元の制約から concrete signature
が得られたあとで task が積まれる。

この `ConcreteSignature` は「expected type を渡す」ものではない。
前段の mono 推論タスクが simple-sub 制約を解いた結果として得た、参照先を mono 化するための
代入済み主型である。

## Task 内の型変数

task を開始したら、その task の erased IR に出現する式・pattern binder・一時的な計算に fresh な
mono 用 type variable を割り当てる。

```text
ExprType(e) = Computation(value = αe, effect = ρe)
BinderType(x) = αx
RefUseType(r) = instantiate(scheme(r))  // 量化変数は fresh mono variable
```

scheme を instantiate するとき、量化された型変数・効果変数・stack 変数・量化された `RefId` は、
すべて task 内の fresh variable へ写す。

```text
instantiate(Scheme) =
  substitution {
    'a -> α1,
    'e -> ρ1,
    r_add -> μ1,
    ...
  }
```

この段階で default type は入れない。

scheme 内に量化されていない open variable が残っている場合、それは infer/poly export のバグである。
`specialize2` は `unit` や `Any` で補わず、invalid scheme として止める。

## 制約収集

制約収集は erased IR の構造から行う。制約収集中に型を即時確定しない。

### literal

literal は閉じた value type を持つ。

```text
1       : int
1.0     : float
"x"     : str
true    : bool
()      : unit
```

literal expression の effect は pure である。

### variable

`Var(ref)` は参照先 scheme を fresh instantiate し、その instantiated computation と
`Var(ref)` の computation を接続する。

- direct ref は、参照先 scheme の型を task 内 fresh variable で展開する。
- local binder は、binder slot と接続する。
- effect operation は、operation scheme と effect metadata から request computation を作る。
- constructor は、constructor value の function type を作る。

direct ref の body はこの時点で mono 化しない。
まず現在の task の制約を解き、ref use-site の instantiated scheme が concrete signature に
なってから、参照先の `MonoInferTask` を積む。

### apply

`f x` は、callee value が argument computation から result computation への関数であるという
制約を作る。

```text
f.value <: x.computation -> result.computation
```

`f` や `x` の evaluation effect、関数の argument effect / return effect は call result の
computation effect へ合流する。

外側から result type が分かっている場合は、result variable に上界を足す。
外側から分からない root expression では、この上界は足さない。

### lambda

lambda は parameter value variable と body computation variable から function value を作る。

parameter pattern は parameter value variable に接続する。
body は同じ task 内で制約収集する。

lambda expression が別の関数型と接続される場合も、expected を渡すのではなく、function value 同士の
subtype / invariant 制約として task の制約へ入れる。

### let

local `let` は、binding の scheme がある場合でも、body を即時に `unit` 既定化しない。

- monomorphic local は binder variable と RHS computation を接続する。
- polymorphic local は use-site ごとに scheme を instantiate する。
- local function は、使われた concrete signature が解けたあとで `LocalFunction` task として
  再帰的に mono 推論する。
- 値制限で computed fetch と判定された binding は、infer が量化境界を上げた scheme と
  runtime root metadata を出していることを前提にする。

### case

`case` は scrutinee、pattern、arm body を同じ result variable へ接続する。

到達不能 arm の実行 effect は result effect へ足さない。ただし、到達不能判定そのものは
solution 前に過剰に強く行わない。pattern から明らかに分かる閉じた variant mismatch だけを
到達不能にしてよい。

### record / poly variant / tuple

構造型は各 field / payload / item の variable を不変位置として接続する。
record field selection は receiver record variable と field result variable を接続する。
optional record field は「存在しないならその field の constraint を生成しない」だけであり、
`Any` を埋める規則ではない。

### method / typeclass selection

selection は、receiver type と member scheme を task 内の制約として接続する。

record field として解けるか、method / typeclass として解けるかは、infer が残した
`SelectResolution` と role/typeclass candidate table を使う。

typeclass member は、receiver type が解ける前に impl を選ばない。
まず role/typeclass demand を task 内に残し、型変数の上下界をまとめる過程で入力型が具体化したら
candidate を照合する。

impl が一意に決まったら、その impl member def の scheme を instantiate し、selection expression の
function value と接続する。さらに、selection が concrete signature に解けた後で
`ImplMember(impl_member, concrete_signature)` task を積む。

impl が複数なら ambiguous error、0 件なら unresolved typeclass method error である。
record fallback を持つ場合でも、role/typeclass 解決が停止した後にだけ fallback を試す。

### cast

`lower <: upper` が直接の constructor subtype で解けない場合、cast rule table を見る。

cast rule は単なる後段 coerce ではない。cast rule の scheme は制約を増やす。
例えば `list α <: opt β` を直接解けず、cast rule に

```text
cast_list_to_opt : list γ -> opt δ
```

があるなら、次の制約を task へ追加する。

```text
list α <: list γ
opt δ <: opt β
```

この追加制約で `γ` や `δ` が決まることがある。cast は、変数境界をまとめる処理の中で
制約を増やす要素である。

cast が成立した場合は、mono 生成時に producer-consumer boundary へ cast/coerce node を挿入し、
cast function 自身も `CastRule(cast_def, concrete_signature)` task として mono 化する。

### effect / thunk / handler

計算型は `(value, effect)` として扱う。
`Thunk(effect, value)` は value type であり、effect を持つ computation そのものではない。

force / thunk 作成 / handler / catch は、value variable と effect variable の制約として task に入る。
effect row subtraction は stack weight 付き制約として扱い、
[`2026-05-31-effect-variable-subtractable.md`](2026-05-31-effect-variable-subtractable.md) の
weight 規則に従う。

handler が effect を捕捉した結果、runtime guard marker が必要になる場合、marker plan は
task の solution 後に producer-consumer の concrete effect 差から作る。
marker primitive の実行時意味は
[`2026-06-13-runtime-guard-markers.md`](2026-06-13-runtime-guard-markers.md) に従う。

## 境界をまとめる

制約収集が終わったら、task 内のすべての型変数について上下界をまとめる。

```text
lower_bounds(α) <: α <: upper_bounds(α)
```

lower 側は join、upper 側は meet として読む。

```text
join(lower_bounds(α)) <: α <: meet(upper_bounds(α))
```

この join / meet は単なる構文上の union / intersection ではない。subtype / cast / invariant 分解により、
制約を追加しながら単一 concrete type へまとめる。

### subtype と cast によるまとめ

例えば、次の境界があるとする。

```text
int | float <: α
```

`int <: float` が成り立つなら、境界は次へ畳める。

```text
float <: α
```

`int <: float` は primitive の特殊分岐ではなく、通常の subtype / cast rule として登録される。

constructor が違うため直接畳めない場合も、cast rule の signature から追加制約を出せる。
`list α <: opt β` と `cast : list γ -> opt δ` があるなら、

```text
list α <: list γ
opt δ <: opt β
```

を追加し、その追加制約でまた上下界をまとめ直す。

### invariant 分解

不変な型引数を持つ constructor 同士をすり合わせるときは、poly 側の不変区間と同じように
両方向の制約を増やす。

`Box α <: Box β` のような不変位置では、単に `α <: β` だけにしない。
同じ実引数を満たすため、上下界の両側を足し、必要な交差条件も task へ戻す。
この読みは [`2026-06-02-role-system.md`](2026-06-02-role-system.md) の不変区間規則に従う。

### 代入

境界をまとめた結果、ある変数が単一 concrete type に挟まれたら、その変数をその型へ代入する。

```text
float <: α <: float
=> α = float
```

下界だけ、または上界だけでも、まとめた結果が単一 concrete type ならその型へ代入できる。
ただし複数の候補が残る場合は error である。

```text
int | str <: α <: list int & unit
```

このように単一型へまとめられないものは、`Any` / `Unknown` / `unit` へ逃がさず error にする。

## role/typeclass 解決

role/typeclass demand は、通常の型変数境界と同じ task 内にいる。

境界をまとめる過程で demand の入力が具体化したら、candidate table を照合する。
candidate が一意に決まると、associated type、prerequisite、member signature から新しい制約が
task へ追加される。

```text
loop:
  collect/saturate ordinary constraints
  summarize variable bounds
  solve cast/invariant/subtype additions
  solve role/typeclass demands that became concrete
  add candidate constraints
  stop when no constraint was added
```

この loop は、role/typeclass 解決で初めて得られる型制約を同じ simple-sub 推論に戻すためのものだ。
method selection はこの loop の一部である。receiver type が concrete になる前に impl member を
mono 化してはならない。

## 式の concrete annotation

task の型変数がすべて concrete に解けると、その task 内の式へ concrete type が付く。

例えば `1 + 1.5` では、最終的に次のような annotated expression が得られる。

```text
[+ : float -> float -> float] [1 : int] [1.5 : float]
```

ここで callee は `float -> float -> float` を要求しているが、第一引数は `int` である。
producer type と consumer type が異なり、`int <: float` が cast で成立しているため、
mono 生成前に cast boundary を入れる。

```text
[[+ : float -> float -> float]
  ([cast : int -> float] [1 : int])
  [1.5 : float]
  : float]
```

cast insertion は型推論の代替ではない。型推論で producer / consumer の concrete 差が分かった後に
挿入される。

## 再帰的な mono demand

task が concrete に解けたら、その task 内の ref use / typeclass member / cast use から
次の mono demand を作る。

```text
MonoDemandKey = (Identity, ConcreteSignature)

Identity =
  | DefId
  | LocalFunctionId
  | ImplMemberDefId
  | CastDefId
  | BuiltinOp
```

同じ key は一つの mono instance へ対応する。同じ polymorphic def が二つの concrete signature で
使われる場合は、二つの mono instance を作る。

新しい demand が生まれたら、その body をまた `MonoInferTask` として推論する。
この再帰により、トップレベル式から参照された関数、その中で参照された typeclass member、
さらにその中の primitive / builtin へ順に型が伝わる。

## worked example: `1 + 1.5`

`+` は source 上では infix operator だが、ここでは関数として読む。

```text
1 + 1.5
```

### 1. 式を単一化する

literal と `+` の主型を fresh instantiate する。

```text
1       : int
+       : α -> α -> α where α: Add
1.5     : float
```

### 2. apply 制約を足す

第一引数から次の制約が出る。

```text
int <: α
```

第二引数から次の制約が出る。

```text
float <: α
```

root expression で出力型が外から分からないため、今回は `α <: output` のような上界は足さない。
関数の戻り値が外側から要求されている場合は、その result variable に上界が足される。

### 3. 境界をまとめる

`α` の lower bound は次である。

```text
int | float <: α
```

`int <: float` が cast/subtype rule として成り立つなら、これは次へまとまる。

```text
float <: α
```

この段階で `α: Add` は `Add float` へ具体化できるが、まだ `+` 本体の mono 化までは行わない。
まず現在の式 task を concrete にする。

### 4. 代入して式に型を付ける

境界が単一 concrete type にまとまったため、次の代入を得る。

```text
α = float
```

式は次のように型付く。

```text
[+ : float -> float -> float] [1 : int] [1.5 : float]
```

callee の parameter は `float`、第一引数 producer は `int` なので cast を挿入する。

```text
[[+ : float -> float -> float]
  ([cast : int -> float] [1 : int])
  [1.5 : float]
  : float]
```

### 5. `+` を mono 化する

`+` の主型は次である。

```text
α -> α -> α where α: Add
```

この use-site では `float -> float -> float` として使われるため、`+` の `MonoInferTask` には
次の境界が入る。

```text
float <: α <: float
```

したがって `α = float` である。
`+` の body は `Add::add` なので、`Add float` の解決結果から float 用の add member を選ぶ。

### 6. `Add(float)::add` を mono 化する

`Add(float)::add` は concrete signature として次を持つ。

```text
float -> float -> float
```

この signature で impl member body を mono 推論する。
body が `std::float::add` なら、その ref use も同じ signature で mono demand になる。

### 7. mono instance を組み戻す

この例では次の mono 定義ができる。

```text
Add(float)::add#mono = builtin_op::float_add
infix(+)#mono#float = Add(float)::add#mono
cast#int#float#mono = builtin_op::int_to_float
```

最後に root expression の `+` と `cast` ref を mono instance へ置き換える。

```text
infix(+)#mono#float(cast#int#float#mono 1, 1.5)
```

ここで初めて root expression の mono 化が完了する。

`builtin_op::int_to_float` が存在しないなら、std / builtin 側へ追加する必要がある。
`specialize2` が「プリミティブだから」と言って `int <: float` を path 文字列で特別扱いしてはならない。

## concrete closure

最終的に、mono へ出すものはすべて concrete でなければならない。

次に未解決 variable が残ったら error である。

- runtime root の computation
- emitted expression の producer / consumer boundary
- mono instance signature
- primitive context
- typeclass / method selection の receiver と member signature
- cast/coerce boundary
- handler / marker plan に使う effect path / effect argument

一方で、task 内の補助 variable のうち、どの emitted value / selection / instance key / marker plan にも
到達しないものは mono 結果ではない。これらは出力へ出さない。
ただし、補助 variable が role/typeclass demand を持つ場合は、到達しないものとして捨ててはならない。
未解決 demand は error である。

## mono 生成

mono 生成は、到達したすべての `MonoInferTask` が concrete に解けた後に行う。

- expression は task の concrete annotation を読む。
- variable ref は ref use が選んだ concrete instance / local / constructor / effect op を読む。
- boundary node は producer-consumer の concrete 差から挿入する。
- thunk / force は concrete computation/value 差から挿入する。
- cast/coerce は解決済み cast demand から挿入する。
- guard marker plan は concrete effect 差から挿入する。

mono 生成中に scheme を instantiate して型を解き直してはならない。
mono 生成中に typeclass method を再解決してはならない。

## diagnostics

`specialize2` の主要 error は次の通りである。

- invalid exported scheme: scheme に未量化 open variable が残っている
- unresolved concrete type: root / instance / boundary に concrete type が一つも決まらない
- conflicting concrete type: lower/upper が単一 concrete type にまとまらない
- unresolved typeclass method
- ambiguous typeclass method
- unresolved cast
- non-concrete effect marker plan

diagnostics は mono 推論 task、式 node、source span を持つ。表示文言は diagnostics 層へ寄せ、
solver 本体は構造化 error を返す。

## 実装境界

`specialize2` は既存 `specialize::solve` の局所修正として実装しない。
少なくとも次の module 境界を持つ。

```text
specialize2/
  mod.rs          public entrypoint
  task.rs         MonoInferTask / demand key
  infer.rs        erased IR -> mono simple-sub constraints
  graph.rs        task-local variables / bounds / constraints
  solve.rs        bound summary, cast/invariant expansion, substitution
  role.rs         role/typeclass demand solving
  demand.rs       concrete def/impl/cast demand expansion
  emit.rs         solved tasks -> mono::Program
  diagnostics.rs  structured errors
```

既存 `specialize` は参照用に残してよいが、`specialize2` の solver が
`signature_for_scheme(..., None)` 由来の default 型に依存してはならない。

