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
作業名を `Specialize`、crate 名を `specialize` とする。
出力 IR の crate 名は `mono` とする。
`specialize` は principal scheme、erased IR、ref table だけから単一化需要、参照解決、
cast adapter 挿入、runtime hygiene 境界を作り、`mono` IR を返す責務を持つ。
yulang2 系の first cut では、現行の `poly::Arena` をこの入力境界として扱う。
旧 `yulang` / `yulang-elaborate` / `yulang-elaborated-ir` へは接続しない。

`poly::Arena::roots` は module 直下の定義一覧であり、runtime demand root ではない。
ただし、裸の `1` も立派な program である。また、top-level binding でも RHS 評価で計算が
発生するものは、未参照でも実行しなければならない。

```yu
my a = say "Hello"
```

この `a` は「使われていない定義」として捨てる対象ではない。`a` を取得することで RHS の
計算が走るため、program の実行需要に含まれる。

そのため `poly::Arena::roots` とは別に、実行対象になる top-level item を source order の
`poly::Arena::runtime_roots` として保存する。`runtime_roots` は次のどちらかを持つ。

- `RuntimeRoot::Expr(ExprId)`:
  裸の top-level expression。
- `RuntimeRoot::ComputedDef(DefId)`:
  `BindingFetch::FetchComputation` になった top-level binding。

`poly::Arena::root_exprs` は root expression の debug view として残してよいが、実行順の根拠は
`runtime_roots` である。specialize は未使用の `FetchValue` top-level 定義を単一化しない。
top-level runtime root や明示 root から変数参照を辿って到達した定義だけを `mono` instance として
materialize する。

monomorphize の入力として信用してよい型情報は、次の五つだけである。

1. 各定義の主型
2. 型・効果を消去した IR
3. direct な `RefId -> DefId` table
4. infer 時点で解けた型クラス参照の `RefId -> impl member DefId` table
5. 主型に量化された `RefId` を持つ未解決の型クラス obligation

IR は「型が付いた構文木」ではない。infer が型証拠を集め終わったら、式 node の型と効果は
IR から消去する。後段が読むのは、値の構造、参照先、`RefId`、literal kind、span など、
型ではない情報だけである。

ただし、specialize は式に型を付けないわけではない。specialize は、各 `mono` instance の
erased IR を読むたびに、その instance 専用の型 slot を全 expression へ割り当てる。
`1 + 1` なら、各 literal に `int`、`+` 参照に主型 `α -> α -> α where α: Add` を fresh
instantiate し、apply 構造から `int <: α` と result slot `α` を作る。その bounds を解いた結果
`α = int` が得られたら、`+` の参照先 demand は `int -> int -> int` になる。そこからさらに
参照先 instance を materialize し、その body でも同じ処理を繰り返す。

つまり、式 node の型を infer から export するのではなく、specialize が主型と erased IR から
式の型を再構成する。全式に型が付くのは specialize 内部の作業状態であり、`poly` の永続 field
ではない。

infer が binding や root expression を外へ出すときは、式木そのものに型を埋め込まず、
top-level computation の境界だけを必要に応じて外側の triple として扱う。

```text
InferredExpr = { typ, eff, ir }
```

`typ` と `eff` はその computation 全体の推論結果であり、`ir` の node に再帰的に畳み込まれた
型ではない。monomorphize は `ir` の途中 node から推論済み型を読む経路を持たず、必要な型制約は
主型、literal kind、参照先 scheme、erased IR の構造から作り直す。top-level expression の
境界型は初期 demand の補助として使ってよいが、式内部の型 table の代替にはしない。

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
  typeclass_impl_candidates: [
    TypeClassImplCandidate {
      class: Add,
      args: [Input(int), Input(int), Associated(out = int)],
      members: [add -> int_add],
      prerequisites: [],
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
obligation に畳み込む。値制限や量化境界は scheme の metadata として残す。
計算を伴う変数取得の値制限と SCC 診断は
[`2026-06-13-computed-fetch-value-restriction.md`](2026-06-13-computed-fetch-value-restriction.md)
に従う。後段に
「この場所に注釈があった」という evidence を渡してはならない。

monomorphize が注釈を再解釈すると、infer と別の意味で注釈を読む経路が生まれる。これは
主型から単相化するという API 境界を壊す。

ただし、function boundary hygiene に必要な情報は、注釈履歴とは別分類として infer output に残す。
`f: () -> [io] _` のような関数 parameter の return effect 境界や、`x: [_] _` のような
effective thunk parameter の effect 境界は、後段が関数値の producer-consumer 境界で
`FunctionAdapter` と runtime guard marker plan を組むための runtime hygiene 入力である。
guard marker の実行時意味は
[`2026-06-13-runtime-guard-markers.md`](2026-06-13-runtime-guard-markers.md) に従う。

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

direct ref の使用箇所では、その `RefId` の主型と、文脈が要求する computation から具体代入を作る。
apply callee の場合は、apply の引数・返り値も文脈の一部として使う。
例えば `id : α -> α` を `id 1 : int` として使う場合、引数 literal と apply result から
`α := int` を得る。この concrete signature は、参照元 instance 内の `RefId` 解決だけでなく、
参照先 binding をどの `MonoInstance` として materialize するかにも使う。
引数が direct ref で、その参照先 scheme がすでに単相 concrete なら、その scheme body も
同じ use-site の concrete 情報として使える。
apply されていない direct ref でも、root や関数引数などの文脈が concrete computation を要求する場合は、
その computation と主型を照合して concrete signature を作る。
高階関数の引数として direct ref を渡す場合、callee scheme の返り値と外側 expected result から
parameter computation が concrete に決まるなら、その parameter computation を argument 側へ渡し、
argument の direct ref scheme も同じ規則で単相化する。

使用箇所から境界が十分に得られない fresh 単相変数は、`Any` / `Unknown` で補わず、
value type なら `unit`、effect row なら `Never` を代入する。
ただし未解決 `RefId`、未解決 typeclass obligation、kind の分からない free type variable が
残る場合は、未対応の generic direct ref として止める。後続では、引数 expression の制約を
先に解いてから同じ規則で具体代入を作れる範囲を広げる。

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
9. fresh な単相変数から concrete 型への型代入表を作る。
10. その型代入表で、instantiate 済みの主型、参照先 signature、elaborated IR の computation 型、
    cast 境界の actual / expected 型を置換する。
11. 実際の値型と要求型が異なる境界へ cast を挿入する。
12. infer 時点で解けていた型クラス参照は、記録済みの impl member をその `RefId` の concrete 解にする。
13. `RefId` に結びついた未解決の型クラス obligation を concrete impl へ解決し、`RefId` を
    impl member 参照へ置き換える。
14. direct / infer-resolved / monomorphize-resolved の各参照先について、参照先定義の主型への
    具体代入を作る。
15. instance-local な `RefId -> target MonoInstanceId` table を作り、elaborated expression 内の
    `RefId` を target instance 参照へ置換する。`RefId` は provenance table には残してよいが、
    runtime-lower 側の暗黙の名前解決責務として残さない。
16. その処理で使った関数、impl、`RefId` と、それぞれの主型への具体代入を記録する。
17. 記録した組を新しい `Demand` として worklist へ入れる。

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

この段階で読めるのは、まだ「fresh 単相変数 `α` の concrete 解」だけである。
解いた直後の型を、その場で scheme body や elaborated IR に再帰的に混ぜてはならない。
制約解決は fresh 単相変数ごとの解を集め、後続の型代入表を作るところまでを責務とする。

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
7. どちらの境界からも一意の concrete 型が得られないなら、単相化不能としてエラーにする。

この規則は「より見た目が綺麗な型を選ぶ」規則ではない。
境界の片側が concrete 型を一つだけ持っているか、束の正規化で一つに畳めるかだけを見る。

例えば次の制約を考える。

```text
A | B <: α <: C & D
```

`A | B` が一つの concrete join として定義されており、下界側が一つの concrete 型へ
正規化できるなら、その型を候補にする。`C & D` も同様に、一つの concrete meet として
定義されている場合だけ候補になる。

下界の正規化では、複数の concrete lower bound から代表になる concrete 型を一つ選ぶ。
`L1 <: α` と `L2 <: α` が同時にあるなら、`L1 <: L2` が言える場合は `L2`、`L2 <: L1`
が言える場合は `L1` を候補にする。どちらの関係も言えないなら、`L1 | L2` を合成して
穴埋めするのではなく、単相化不能としてエラーにする。`Never` は下界候補の情報を増やさず、
`Any` が下界に現れた場合は代表候補が `Any` になる。
上界の正規化でも同じく、複数の concrete upper bound から代表になる concrete 型を一つ選ぶ。
`α <: U1` と `α <: U2` が同時にあるなら、`U1 <: U2` が言える場合は `U1`、`U2 <: U1`
が言える場合は `U2` を候補にする。どちらの関係も言えないなら、`U1 & U2` を合成して
穴埋めするのではなく、単相化不能としてエラーにする。`Any` は上界候補の情報を増やさず、
`Never` が上界に現れた場合は代表候補が `Never` になる。

direct cast 宣言は、join / meet の候補選択で subtype edge として扱う。ただし見るのは
読み込まれた cast 宣言そのものだけであり、cast graph の推移閉包は作らない。
`A <: B` と `B <: C` に対応する cast があっても、それだけでは `A <: C` とはみなさない。
推移的な cast 合成は、どの中間変換を実行するかを勝手に選ぶことになり、cast によって
追加される制約や実行時処理を隠してしまうためである。

したがって、文脈型を持たない root expression の `case true: true -> 1, false -> 2.0` は、
二つの arm body から `int <: α` と `float <: α` を得るが、`int` と `float` を一つの
代表 concrete 型へ畳む subtype edge がない限り、単相化不能としてエラーになる。
これは `case` 専用規則ではなく、同じ result slot へ複数の concrete lower bound が集まる
すべての expression に適用する。

同じ source に direct cast 宣言が読み込まれている場合は、`int <: float` をその宣言から得る。

```yul
cast(x: int): float = ...

case true: true -> 1, false -> 2.0
```

この場合、下界候補は `float` へ畳める。これは primitive numeric 型の特別扱いではなく、
`cast(int): float` が direct edge として存在することだけに由来する。

どちらの側も複数の具体型の集合でしかなく、束の関係から一つの concrete 型へ畳めないなら、
`α` へ入れる中間型は存在しない。このとき `Any` や `Unknown` で穴埋めしてはならない。
境界から候補が一つも出ない場合も、具体型が決まらないため単相化不能としてエラーにする。
root expression の `TypeBounds` から初期 computation を作る入口でも同じ規則を使う。
ただし `Union(Var, Fun(...))` のように裸変数と構造を持つ型が混在する場合、裸変数を default 候補として
混ぜず、まず構造を持つ候補を読む。候補が本当に一つもない場合は field の kind に応じた default へ
落とさず、単相化不能として扱う。

## 型代入と置換

concrete 型の選択後、monomorphize は fresh 単相変数から concrete 型への型代入表を作る。
この表は、推論器の内部 substitution ではなく、需要内で作った fresh 単相変数だけを対象にする。

```text
α0 := int
ε0 := Never
ρ0 := std.str.str
```

制約グラフを解いている途中で、型の中に直接 concrete 解を埋め込んではならない。
また、量化元の型変数名へ直接代入してはならない。
必ず次の段階に分ける。

1. 量化変数を use-site fresh な単相変数へ instantiate する。
2. 制約グラフを解いて、その fresh 単相変数から concrete 型への代入表を作る。
3. その代入表で、必要な型構造を置換する。

置換対象は次を含む。

- instantiate 済みの主型
- direct ref / infer-resolved typeclass ref / monomorphize-resolved ref の concrete signature
- elaborated IR の各 expression computation 型
- cast / force-thunk / function adapter 境界の actual 型と expected 型
- worklist に入れる次の `Demand` の具体代入
- expression 内の `RefId`。instance-local table で target `MonoInstanceId` 参照へ置換する。

例えば `id : α -> α` を `id 1 : int` として使う場合、`α` はまず `α0` に instantiate される。
制約解決は `α0 := int` の代入表を作る。
その後、`α0 -> α0` へ代入表を適用し、`int -> int` の concrete signature を得る。
`α0` が入った型をその場で部分的に書き換えながら制約を解く形にはしない。

## runtime symbol name

elaborated IR の `MonoInstance` は、runtime lower がそのまま binding symbol として使える
`name: Path` を持つ。runtime lower は `DefId`、`RefId`、型クラス情報、元の infer export を
再参照して symbol 名を決めてはならない。

単相 binding は元の binding path を使ってよい。generic binding の specialization は同じ
source binding から複数個生まれるため、元 path に `monoN` のような安定した suffix を足した
runtime name にする。root expression や typeclass ref 由来の synthetic instance も、
module path と instance id から安定した synthetic path を作る。

elaboration の final pass は expression 内の `RefId` を `InstanceRef(MonoInstanceId)` へ置換する。
`RefId` は provenance table に残ってよいが、runtime lower の入力 expression に unresolved
`RefId` が残っている場合は不変条件違反である。

runtime lower は `InstanceRef(id)` を `MonoInstance.name` の `Var(path)` へ構造変換する。
この段階で impl selection、direct ref 解決、generic instantiation、型クラス解決をやり直さない。

## cast の挿入

型代入表を適用した後、erased IR の構造から再構築した各境界には「式が実際に持つ型」と
「文脈が要求する型」が concrete 型として残っている。

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

## mono IR

単相化後の出力は、旧 monomorphize の runtime IR をそのまま再利用しない。
`specialize` は `InferExport` から型制約を作り直し、制約を concrete に解いた後で、
新しい `mono` IR を組む。

この IR は型付きでよい。ただし、ここで言う型付きとは、infer の typed IR や apply evidence を
再利用することではない。各 node の型は、需要内で concrete に決まった computation 型であり、
`Unknown`、free type variable、未解決 `RefId`、未解決 typeclass obligation を含まない。

effect を持つ thunk は `effective-thunk` として表す。

```text
Type::Thunk = {
  effect: concrete effect row,
  value: concrete value type,
}
```

これは expression node だけの付加情報ではなく、mono の value type そのものに現れる。
関数値、record field、tuple payload、variant payload など first-class value として移動する場所では、
effectful computation boundary を `Type::Thunk` として持つ。

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

実装上の `mono` IR は、producer-consumer 境界を次の node として保持する。

```text
Coerce {
  source: Type,
  target: Type,
  expr: Expr,
}

MakeThunk {
  source: ComputationType,
  target: EffectiveThunkType,
  body: Expr,
}

ForceThunk {
  source: EffectiveThunkType,
  target: ComputationType,
  thunk: Expr,
}

FunctionAdapter {
  source: Type,
  target: Type,
  function: Expr,
  hygiene: FunctionAdapterHygiene,
}

EffectOp {
  path: EffectPath,
}
```

`source` は式が実際に持つ concrete 境界、`target` は文脈が要求する concrete 境界である。
`Coerce` は型を決めるための node ではなく、解決済みの actual / expected 差を runtime lower へ渡す
ための node である。`MakeThunk` / `ForceThunk` も同じく、plain computation と first-class
`Type::Thunk` value の境界を明示する。`FunctionAdapterHygiene` は guard marker spec の
`add_id[n, path, id]` / `push` / `pop` へ落ちる plan を持ち、空 plan は「追加 hygiene なし」を表す。
`EffectOp` は effect request を送出する operation value である。act operation def は body を持たない
`Def::Let` だが、通常の local variable として mono へ落としてはならない。lowering は
`DefId -> EffectPath` を poly 境界に残し、specialize はその def の参照を `EffectOp` へ変換する。

関数値の concrete 型は、runtime shape へ読む段階で、effectful な parameter / return 境界を
`Type::Thunk` に畳む。mono の関数型は runtime value の入力型と出力型を持ち、effect row は
関数型の外側に別枠で残さない。

`Never` は empty effect row なので、`thunk[Never, a]` は作らない。pure な parameter / return は
裸の runtime value shape として渡す。effect row が `Never` ではない場合だけ、
その computation boundary を `effective-thunk` として一級値に持たせる。

```text
a [b] -> [c] d
  ~~>
shape(b, a) -> shape(c, d)

shape(Never, x) = runtime-value-shape(x)
shape(e, x)     = thunk[e, runtime-value-shape(x)]  when e != Never
```

`a` や `d` がさらに関数型の場合も、この変換を再帰的に適用する。つまり、高階関数を値として
渡す場合でも、必要な thunk boundary は関数値の型と一緒に移動できる。

apply では、callee の runtime function boundary を見る。parameter shape が `effective-thunk`
なら argument computation を `MakeThunk` で閉じ、return shape が `effective-thunk` なら
inner apply の結果を `ForceThunk` で開く。pure boundary では `MakeThunk` / `ForceThunk` を
挿入しない。

`catch` の effect arm は、lowering 後の erased IR でも handler 対象 operation の exact path を
保持する。runtime handler はこの path を effect request の path と照合するため、operation path を
型制約だけに閉じ込めて捨ててはならない。

operation 宣言が解決済みであれば、effect arm はその operation def も保持する。
specialize は operation def の scheme を通常の参照と同じ経路で materialize し、handler payload の
mono 型と continuation が受け取る値型を得る。`op: A -> [E] B` の arm では、payload pattern は
`A`、continuation は `B -> shape(scrutinee_effect, scrutinee_value)` として扱う。
generic operation の型引数は、operation def を fresh instantiate しただけでは決まらないため、
operation の return effect を scrutinee effect row の同じ family item へ結び直す。
これにより `get: () -> [var 'a] 'a` のような operation では、`[var int]` を持つ scrutinee から
continuation 入力も `int` へ解ける。
operation def が未解決の fallback arm では、payload 型と continuation 入力型を同じ fresh slot とする。

`case` の arm pattern は scrutinee の mono 型で bind する。constructor pattern は constructor def の
scheme を fresh instantiate し、その return 型を scrutinee 型と両方向に結んで payload 型を取り出す。
mono pattern の constructor identity は runtime constructor identity であり、関数 instance ではない。
したがって constructor pattern は `InstanceId` ではなく constructor `DefId` を持つ。

top-level `FetchComputation` binding は source order の runtime root として materialize される。
`my run = out::say(1); my handled = catch run: ...` の `catch run` は `run` の RHS を handler の
内側で再評価しない。`run` の effect は先行する runtime root の評価で発生し、後続の handler へは
計算済み value だけが渡る。
top-level root expression も runtime root であるため、root expression の actual 型が `Type::Thunk` なら
root の出口で `ForceThunk` を挿入して実行対象にする。これは root にだけ効く規則であり、record field や
関数引数など first-class value として運ばれる thunk を勝手に force しない。

effect id hygiene も同じく、runtime-lower 側の暗黙責務にしてはならない。guard marker の
runtime 意味、`add_id[n, path, id]` の depth、関数起動時の push / pop、resumable effect を含む
unwind 規則は
[`2026-06-13-runtime-guard-markers.md`](2026-06-13-runtime-guard-markers.md) が定義元である。

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
この文書に残る `LocalPushId` / `AddId` は旧 runtime IR の呼び名であり、実装時には
runtime guard marker spec の `push` / `pop` / `add_id[n, path, id]` として読む。

## 型クラス impl と impl member demand

型クラス参照には二種類ある。

1. infer 時点で impl member まで解けた参照
2. monomorphize 時点で需要内の型が concrete に決まってから解く参照

前者は direct 参照ではない。`ResolvedTypeClassRef` として `RefId -> { class, member,
impl_def?, impl_member }` を保持する。monomorphize は impl selection をやり直さず、
記録済みの `impl_member` をその `RefId` の concrete 解にする。

後者は、scheme の `typeclass_obligations` に `RoleDefId + MemberDefId + 型引数 + ref_id`
として残る。infer export は別に `typeclass_impl_candidates` を持ち、各候補の class、input /
associated args、member -> impl member 対応、prerequisites を構造化して渡す。monomorphize は
型表示や path 文字列から impl を推測しない。解決は、構造化された role/member identity と
concrete 型引数を candidate table に照合して行う。

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
  typeclass impl candidate table、未解決 typeclass obligation から型制約を作り直す。
- infer 出力の IR は式 node の型・効果を持たない。
- infer 時点で解けた型クラス参照は direct に畳まず、`RefId -> ResolvedTypeClassRef` として残す。
- scheme の `typeclass_obligations` は型クラス・method・role member の `DefId` を失わない。
- 浮いた型クラス制約も、`RoleDefId + MemberDefId + 型引数` として残す。
- 型クラスと `RefId` は、型変数と同じく需要ごとに量化・単相化される。
- 型クラス解決で得た impl member は、infer-resolved / monomorphize-resolved のどちらでも
  impl member 自身の monomorphize demand を作る。
- 型注釈の場所や意味を monomorphize evidence として渡さない。
- concrete 型の選択で `Any` や `Unknown` に逃げない。
- 境界がなく concrete 型候補を得られない fresh 変数は、value type なら `unit`、effect row なら
  `Never` にする。
- impl 解決は型表示や path 文字列ではなく、`typeclass_obligations` に残った identity と
  concrete 型、ならびに `typeclass_impl_candidates` の構造化 candidate から行う。
