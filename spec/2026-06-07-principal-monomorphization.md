# 主型からの単相化

2026-06-07 決定。monomorphize は infer の内部状態を引き継がず、infer が出した主型と、
型を消去した IR、direct / infer-resolved な `RefId` table、量化された `RefId` を持つ
型クラス obligation だけから、単相化に必要な型制約を作り直す。

## 目的

infer は各定義の主型を求める段階である。monomorphize は、その主型が実際の使用箇所で
どの具体型として使われるかを決める段階である。

この二つの段階を混ぜてはならない。infer の制約グラフ、境界、途中の単一化結果、表示用に
compact 化された型などを monomorphize が覗くと、後段が infer の偶然の形に依存する。
その場合、注釈で一度開いた効果行や、body 側にだけ残った具体型が、単相化の根拠として
使われたり使われなかったりする。

実装上は、既存 `yulang-monomorphize` をそのまま入口差し替えで流用しない。
typed IR / apply evidence 前提の処理を残したまま `InferExport` を受ける形にすると、
境界だけ新しく見えて中身が旧 evidence に戻る。新しい後段 crate を切り、
作業名を `Elaborate`、crate 名候補を `yulang-elaborate` とする。
この crate は principal scheme、erased IR、ref table だけから単相化需要、参照解決、
cast adapter 挿入を作る責務を持つ。

monomorphize の入力として信用してよい型情報は、次の五つだけである。

1. 各定義の主型
2. 型・効果を消去した IR
3. direct な `RefId -> DefId` table
4. infer 時点で解けた型クラス参照の `RefId -> impl member DefId` table
5. 主型に量化された `RefId` を持つ未解決の型クラス obligation

IR は「型が付いた構文木」ではない。infer が型証拠を集め終わったら、式 node の型と効果は
IR から消去する。後段が読むのは、値の構造、参照先、`RefId`、literal kind、span など、
型ではない情報だけである。

infer が binding や root expression を外へ出すときは、式木そのものに型を埋め込まず、
次のような外側の triple として扱う。

```text
InferredExpr = { typ, eff, ir }
```

`typ` と `eff` はその computation 全体の推論結果であり、`ir` の node に再帰的に畳み込まれた
型ではない。monomorphize は `ir` の途中 node から推論済み型を読む経路を持たず、必要な型制約は
主型とこの top-level computation 境界から作り直す。

`Coerce` は erased IR の node ではない。型注釈や representation coerce によって制約や
diagnostic evidence が生まれることはあるが、実行値の構造としては残さない。必要な cast は
monomorphize / elaboration が producer-consumer の型差から後で挿入する。

## infer 出力に残すもの

型クラスは、型推論だけではなく名前解決の結果でもある。

例えば `x.meth` や role member 呼び出しがあったとき、infer は「どの型クラスのどの member を
使う要求なのか」を決める。その後、型が十分に具体化していれば impl まで解ける。まだ型が
浮いていれば impl は未決定のまま残る。

ただし、その identity は式 node の型として残すのではない。

infer 時点で impl まで解けた型クラス参照は、direct 参照へ畳まない。`RefId` から
「どの class/member が、どの impl/member に解けたか」を引ける table として出す。
まだ impl が解けない型クラス参照は、主型の量化対象に含まれる `RefId` を持つ
typeclass obligation として scheme に残す。

現行 export では role/typeclass の identity は `DefId` ではなく `Path` で持つ。
source impl や synthetic impl では impl owner `DefId` も保持する。compiled snapshot 由来の
候補では impl owner がまだ保存されていないため、`impl_def` は欠けうる。

保持する identity は次の通りである。

- 型クラスまたは role の `DefId`
- member 関数の `DefId`
- infer 時点で解決済みなら impl の `DefId` と impl member の `DefId`
- 未解決なら、後段で解くべき型クラス制約と、その型引数・関連型・効果引数
- その要求がどの `RefId` を埋めるか

未解決の型クラス制約を、単なる `T: Role` のような曖昧な形で残してはならない。
浮いた制約でも「どの role/member の要求か」は infer の時点で確定しているため、
`RoleDefId + MemberDefId + 型引数` の形で保持する。

同じ理由で、`RefId` は型変数と同じように量化対象として扱える形で残す。未解決の
型クラス obligation は `RefId` を持ち、解決後にどの実体を使ったかを concrete な
単相化需要として記録する。

infer 出力は概念的に次の情報を持つ。

```text
RefExportTable {
  direct: [
    r_direct := DefId(foo),
  ],
  resolved_typeclass: [
    r_int_add := ResolvedTypeClassRef {
      class: Add,
      member: add,
      impl_def: IntAdd,
      impl_member: int_add,
    },
  ],
}

Scheme {
  ty: 主型,
  quantified_types: [α, β, ρ, ...],
  quantified_refs: [r_add, r_show, ...],
  typeclass_obligations: [
    TypeClassObligation { ref_id: r_add, class: Add, member: add, args: [α, int], out: β },
    TypeClassObligation { ref_id: r_show, class: Show, member: show, args: [β] },
  ],
}
```

erased IR には、`r_direct`、`r_int_add`、`r_add` などを参照する構造だけが残る。
`RefId` の型、呼び出し結果の型、
そこで発生した効果型は残らない。

ただし、lambda parameter や pattern binder のような lexical local は、program-global な
runtime identity ではない。これらは local binder の `DefId` として IR 内に残してよい。
program-global な値参照は、lower 済み AST で直接 `DefId` に畳まれていても、export 境界で
`RefId` と `RefExportTable.direct` へ戻す。最終形では、source lowering が最初から erased IR と
computation 型を同時に作るため、この戻し処理は legacy lower との橋にだけ残る。

## 注釈の扱い

型注釈と effect 注釈は infer の入力であり、monomorphize の入力ではない。

注釈によって生まれた subtractability や非 subtract 境界は、infer が主型と scheme の
obligation に畳み込む。値制限や量化境界は scheme の metadata として残す。後段に
「この場所に注釈があった」という evidence を渡してはならない。

monomorphize が注釈を再解釈すると、infer と別の意味で注釈を読む経路が生まれる。これは
主型から単相化するという API 境界を壊す。

ただし、function boundary hygiene に必要な情報は、注釈履歴とは別分類として infer output に残す。
`f: () -> [io] _` のような関数 parameter の return effect 境界や、`x: [_] _` のような
effective thunk parameter の effect 境界は、後段が関数値の producer-consumer 境界で
`FunctionAdapter` / `LocalPushId` / `AddId` を組むための runtime hygiene 入力である。

この情報は erased expression node の field ではなく、lambda parameter `DefId` で引ける
`HygieneExportTable` に置く。table は「この場所に注釈があった」という evidence ではなく、
その lambda parameter を値として受け渡すときに守るべき runtime 境界だけを表す。
elaboration は主型と erased IR から関数境界を再構築し、この table を補助入力として
adapter hygiene plan を作る。runtime lower はこの plan を実行表現へ落とすだけで、
関数型や apply spine から hygiene を推測してはならない。

## 単相化需要

monomorphize の作業単位は次の組である。

```text
Demand = (定義または参照の identity, 主型への具体代入)
```

identity は通常の関数 `DefId`、型クラス impl の `DefId`、erased IR が保持する `RefId` などである。
具体代入は、その identity の主型に現れる量化変数へ、今回の使用箇所で入る concrete 型を
対応させる写像である。

同じ identity と同じ具体代入は同じ単相化結果を指す。worklist はこの組で重複を消す。

direct ref の使用箇所では、その `RefId` の主型と、apply の引数・返り値から具体代入を作る。
例えば `id : α -> α` を `id 1 : int` として使う場合、引数 literal と apply result から
`α := int` を得る。この concrete signature は、参照元 instance 内の `RefId` 解決だけでなく、
参照先 binding をどの `MonoInstance` として materialize するかにも使う。
引数が direct ref で、その参照先 scheme がすでに単相 concrete なら、その scheme body も
同じ use-site の concrete 情報として使える。

使用箇所から concrete 型が十分に得られない場合は、`Any` / `Unknown` で補わず、未対応の
generic direct ref として止める。後続では、引数 expression の制約を先に解いてから同じ規則で
具体代入を作れる範囲を広げる。

## 初期需要

最初の需要はトップレベルから作る。

トップレベルでは、リテラルの型は既に決まっている。値制限により量化されていないものを
除けば、トップレベル定義の主型に現れる変数は量化されている。

そのため、トップレベルの erased IR を通常の需要と同じ手順で制約化し、リテラル構文の閉じた型と
単相化された量化変数から、最初の具体代入を得る。ここでも infer の内部グラフは使わない。

## 需要の処理

ある `Demand = (F, S)` を処理するとき、monomorphize は次を行う。

1. `F` の主型へ `S` を代入する。
2. まだ量化されている型変数、効果変数、型クラス制約、`RefId` を、この需要専用に fresh な
   単相変数として instantiate する。
3. `F` の erased IR を走査し、型制約を一から作り直す。
4. リテラルは literal kind から決まる閉じた型として扱う。
5. 量化された値を参照した箇所では、その値の主型をこの需要内で単相化し、通常の制約を作る。
6. 関数適用、field/method 選択、handler、cast/coerce 境界を、erased IR の構造に従って
   制約へ戻す。
7. subtype 制約と単一化制約を解く。
8. 残った単相変数を、上下界から concrete 型へ決める。
9. 実際の値型と要求型が異なる境界へ cast を挿入する。
10. infer 時点で解けていた型クラス参照は、記録済みの impl member をその `RefId` の concrete 解にする。
11. `RefId` に結びついた未解決の型クラス obligation を concrete impl へ解決し、`RefId` を
    impl member 参照へ置き換える。
12. direct / infer-resolved / monomorphize-resolved の各参照先について、参照先定義の主型への
    具体代入を作る。
13. その処理で使った関数、impl、`RefId` と、それぞれの主型への具体代入を記録する。
14. 記録した組を新しい `Demand` として worklist へ入れる。

この処理を worklist が空になるまで繰り返す。

infer-resolved typeclass ref は impl selection をやり直さない。`ResolvedTypeClassRef.impl_member`
の scheme を、その `RefId` の use-site で direct ref と同じように制約化し、elaborated ref table には
`ResolvedRefSource::InferResolvedTypeclass` として残す。

## 制約グラフ

Elaborate の制約解決は、`DraftComputationId -> MonoComputation` の代入表として保持してはならない。
各 computation slot の value / effect と、scheme instantiate で fresh 化した単相型変数を
同じ制約グラフの node として扱う。

制約グラフは次を持つ。

- node ごとの lower bounds
- node ごとの upper bounds
- `lower_node <: upper_node` の subtype edge

下界 `L` を node `α` に追加したら、既存の各上界 `U` について `L <: U` を制約化し、
`α <: β` の edge がある各 `β` へ同じ下界を流す。
上界 `U` を node `α` に追加したら、既存の各下界 `L` について `L <: U` を制約化し、
`β <: α` の edge がある各 `β` へ同じ上界を流す。

`Type::Var(a) <: Type::Var(b)` は `a <: b` の edge、`T <: Type::Var(a)` は `a` の lower bound、
`Type::Var(a) <: T` は `a` の upper bound として扱う。
関数型では引数と引数 effect を反変、返り値と返り値 effect を共変に分解する。
tuple や同一 constructor の type argument も、構造が一致する範囲で子制約へ分解する。

generic direct ref の instantiate は、量化変数を use-site fresh node に置き換えてから制約を作る。
例えば `id : α -> α` を `id 1 : int` として使う場合は、`int <: α` と `α <: int` を同じ
fresh node `α` の上下界に入れ、concrete selection で `α = int` を読む。
`Any` や `Unknown` による穴埋めは行わない。

## concrete 型の選択

制約を解いた後でも、需要内の単相変数 `α` には上下界だけが残ることがある。
このとき `α` は、境界から一意に読める concrete 型へ落とす。

ここで concrete 型とは、型変数・効果変数・未解決 `RefId`・未解決型クラス制約を含まない型である。
`Unknown` は concrete 型ではない。`Any` と `Never` は Top/Bottom であり、制約から明示的に
出たときだけ通常の concrete 型として扱う。型が決まらないことの fallback に使ってはならない。

選択規則は次の通りである。

1. `α` の下界を正規化し、下界側がちょうど一つの concrete 型 `L` を表すなら、下界候補を `L` とする。
2. `α` の上界を正規化し、上界側がちょうど一つの concrete 型 `U` を表すなら、上界候補を `U` とする。
3. 片側だけに候補があるなら、その候補を `α` の型にする。
4. 両側に候補があり、それらが同じ concrete 型へ正規化されるなら、その型を `α` の型にする。
5. 両側に候補があり、束の関係によって唯一の concrete 型へまとめられるなら、その型を `α` の型にする。
6. 両側の候補が互いに矛盾するなら、通常の制約不整合としてエラーにする。
7. どちらの境界からも一意の concrete 型が得られないなら、「中間の型がなかった」エラーにする。

この規則は「より見た目が綺麗な型を選ぶ」規則ではない。
境界の片側が concrete 型を一つだけ持っているか、束の正規化で一つに畳めるかだけを見る。

例えば次の制約を考える。

```text
A | B <: α <: C & D
```

`A | B` が一つの concrete join として定義されており、下界側が一つの concrete 型へ
正規化できるなら、その型を候補にする。`C & D` も同様に、一つの concrete meet として
定義されている場合だけ候補になる。

どちらの側も複数の具体型の集合でしかなく、束の関係から一つの concrete 型へ畳めないなら、
`α` へ入れる中間型は存在しない。このとき `Any` や `Unknown` で穴埋めしてはならない。

## cast の挿入

concrete 型の選択後、erased IR の構造から再構築した各境界には「式が実際に持つ型」と
「文脈が要求する型」が残っている。

両者が同じでない場合、制約解決により subtype 関係が確認できている境界へ cast を挿入する。
これは simple-sub の健全性により可能である。cast は型を決めるための手段ではなく、
決まった型の差を runtime IR に明示するための処理である。

cast を挿入できない境界が残る場合は、単相化の失敗ではなく、前段の制約解決が不完全か
不整合を見落としていることを意味する。

## 関数 cast

関数値の cast は、呼び出し先へ暗黙の実行時 cast 責務を押し付けない。
関数型の境界で型が変わる場合、cast は adapter lambda を生成する。

例えば実際の関数値が `A -> C` で、文脈が `B -> D` を要求する場合、関数 subtyping は
引数で反変、返り値で共変であるため、次が必要である。

```text
B <: A
C <: D
```

この cast は概念的に次の高階関数になる。

```text
\x: B ->
    let y: A = cast x
    let r: C = f y
    cast r : D
```

effect 付き関数でも同じである。adapter の外側は期待された関数型を持ち、内側では実際の
関数を呼ぶ。引数側の cast は反変方向、返り値と返り effect の cast は共変方向に入る。

関数を渡した先で呼び出し時に cast する方式は採用しない。その方式では、関数を record に
入れる、ref に入れる、別の高階関数へ渡す、impl member 経由で渡す、といったケースで
どの値が cast 責務を背負っているかが曖昧になる。

原則:

- 値 cast は、その値が境界を越える場所に入れる。
- 関数値 cast は adapter lambda として表す。
- adapter 内では引数を反変 cast し、返り値と返り effect を共変 cast する。
- direct ref / infer-resolved typeclass ref / monomorphize-resolved typeclass ref のどれであっても、
  単相化後に必要なら同じ規則で adapter を生成する。
- runtime IR の呼び出し側へ、暗黙の関数 cast 責務を残さない。

## elaborated IR

単相化後の出力は、旧 monomorphize の runtime IR をそのまま再利用しない。
`Elaborate` は `InferExport` から型制約を作り直し、制約を concrete に解いた後で、
新しい `elaborated IR` を組む。

この IR は型付きでよい。ただし、ここで言う型付きとは、infer の typed IR や apply evidence を
再利用することではない。各 node の型は、需要内で concrete に決まった computation 型であり、
`Unknown`、free type variable、未解決 `RefId`、未解決 typeclass obligation を含まない。

effect を持つ thunk は `effective-thunk` として表す。

```text
EffectiveThunk = {
  effect: concrete effect row,
  value: concrete value type,
}
```

旧 runtime IR の `BindHere` は名前としては「ここで bind する」に見えるが、意味は
`effective-thunk` を開いて、その thunk の effect を現在の computation へ出す境界である。
新しい elaborated IR では、この操作を cast と同じ種類の境界として扱う。

```text
ForceThunk {
  source: EffectiveThunk,
  target: Computation,
  thunk: Expr,
}
```

`source` は開く前の thunk 型、`target` は開いた後に得る computation 型である。
値 cast が `source value -> target value` の境界であるのと同じく、thunk open は
`source effective-thunk -> target computation` の境界として残す。

この境界を runtime-lower 側の暗黙責務にしてはならない。
関数 cast を呼び出し先に押し付けないのと同様に、thunk を開く責務も、producer-consumer の
型差が確定した場所で elaborated IR に明示する。

effect id hygiene も同じく、runtime-lower 側の暗黙責務にしてはならない。

旧 runtime IR の `LocalPushId` / `AddId` は、型上の値 cast ではなく、effect request と
effective thunk に付く runtime control boundary である。ただし、高階関数をさらに高階関数へ
渡す場合、呼び出し箇所だけを見て後から `LocalPushId` / `AddId` を挿入する方式では、
必要な境界が first-class function value と一緒に移動できない。

そのため、関数値が producer-consumer の型境界を越える場所では、関数 cast と同じく
`FunctionAdapter` を挿入する。`FunctionAdapter` は source / target の関数境界だけでなく、
その adapter が呼ばれたときに実行する hygiene plan を持つ。

```text
FunctionAdapter {
  source: FunctionBoundary,
  target: FunctionBoundary,
  call: FunctionAdapterCall {
    local_scope: Option<EffectIdVar>,
    result_boundaries: [
      AddId { id: EffectIdRef, allowed: concrete effect row, active: bool },
      FunctionAdapter(...), // returned function value にさらに境界が必要な場合
    ],
  },
}
```

`local_scope` は adapter call body を `LocalPushId` で囲むことを表す。
`AddId` result boundary は、adapter の実行結果として得た effective thunk / effectful result に
blocked effect id を付与することを表す。返り値自体が関数値で、その関数値にも hygiene が必要な
場合は、result boundary に nested `FunctionAdapter` を持たせる。

これにより、`(A -> [e] B)` の関数値をさらに別の高階関数へ渡しても、必要な hygiene boundary は
adapter と一緒に値として運ばれる。runtime lower は adapter に書かれた plan を実行表現へ落とすだけで、
関数型や呼び出し spine から `LocalPushId` / `AddId` を推測してはならない。

## 型クラス impl と impl member demand

型クラス参照には二種類ある。

1. infer 時点で impl member まで解けた参照
2. monomorphize 時点で需要内の型が concrete に決まってから解く参照

前者は direct 参照ではない。`ResolvedTypeClassRef` として `RefId -> { class, member,
impl_def?, impl_member }` を保持する。monomorphize は impl selection をやり直さず、
記録済みの `impl_member` をその `RefId` の concrete 解にする。

後者は、scheme の `typeclass_obligations` に `RoleDefId + MemberDefId + 型引数 + ref_id`
として残る。monomorphize は型表示や path 文字列から impl を推測しない。解決は、
構造化された role/member identity と concrete 型引数に対して行う。

どちらの場合でも、impl member が決まったら対象の `RefId` を impl member 参照へ代入する。
さらに、その impl member の主型に対する具体代入を作り、新しい `Demand` として記録する。
関連型がある場合は、impl 解決で得られた関連型の等式も同じ需要内の制約として扱う。

impl が一つに決まらない場合は曖昧性エラー、候補がない場合は missing impl エラーである。
ここでも `Any`、`Unknown`、名前文字列の fallback を使ってはならない。

## 単一化の証拠

monomorphize は、すべての単一化と concrete 代入について、それが何によって生まれたかを
記録する。

記録する対象は次を含む。

- 関数適用によって単一化された引数型・返り型・効果型
- field/method 選択によって要求された record/role 制約
- infer 時点で解けていた型クラス参照と、その impl member
- 型クラス impl 解決で選ばれた impl と impl member
- cast 挿入を必要にした producer/consumer の型差
- `RefId` の単一化、その concrete 代入、対応する型クラス obligation

この証拠から、需要内で実際に使われた identity と concrete 代入が分かる。
主型に何を代入したかが分かっているため、その identity ごとに次の `Demand` を作れる。

## 不変条件

- monomorphize は infer の内部制約グラフを読まない。
- monomorphize は主型、erased IR、direct ref table、infer-resolved typeclass table、
  未解決 typeclass obligation から型制約を作り直す。
- infer 出力の IR は式 node の型・効果を持たない。
- infer 時点で解けた型クラス参照は direct に畳まず、`RefId -> ResolvedTypeClassRef` として残す。
- scheme の `typeclass_obligations` は型クラス・method・role member の `DefId` を失わない。
- 浮いた型クラス制約も、`RoleDefId + MemberDefId + 型引数` として残す。
- 型クラスと `RefId` は、型変数と同じく需要ごとに量化・単相化される。
- 型クラス解決で得た impl member は、infer-resolved / monomorphize-resolved のどちらでも
  impl member 自身の monomorphize demand を作る。
- 型注釈の場所や意味を monomorphize evidence として渡さない。
- concrete 型の選択で `Any` や `Unknown` に逃げない。
- 「中間の型がなかった」場合は、型を捏造せずエラーにする。
- impl 解決は型表示や path 文字列ではなく、`typeclass_obligations` に残った identity と
  concrete 型から行う。
