# Yulang 実装抽出レポート

作成日: 2026-04-30

この文書は、現時点の実装から Yulang の仕様らしきものを抽出したレポートである。主に `crates/yulang`、`crates/yulang-parser`、`crates/yulang-infer`、`crates/yulang-runtime`、`std`、`examples`、`tests` を読んでまとめている。

これはまだ正式仕様ではない。実装上は存在するが意味論まで追い切れていない機能、パーサだけが先に持っている構文、現在の dirty workspace に依存して見える挙動も含む。公開仕様へ育てるなら、最後の「未確定点」を先に潰すのがよさそうである。

## 1. 言語の全体像

Yulang は、式指向の関数型言語を核に、以下の仕組みを組み合わせている。

- Simple-sub 系の制約ベース型推論
- 構造的な record / tuple / variant / row 型
- 名目的な `type` / `struct` / `enum`
- role と impl による型クラス風の ad-hoc 多相
- algebraic effect と handler
- effect を使った `sub` / `return`、`for` / `last` / `next` / `redo`
- 参照を effect として扱う `$x` / `&x = value`
- ユーザー定義演算子と構文レベルの演算子優先順位
- indentation と brace の両方を受け入れるブロック構文

実装上のコンパイル単位は module である。source loader が entry source に暗黙の prelude を挿入し、複数ファイルを依存順に並べ、parser が CST を作り、infer/lower が型制約つき AST へ落とし、core IR を export し、runtime IR へ下げ、必要に応じて monomorphize して VM が実行する。

## 2. コンパイルと実行パイプライン

CLI の入口は `crates/yulang/src/main.rs` にある。大まかな流れは次の通りである。

1. source loader が entry file または仮想 source を読む。
2. `lib/std/prelude.yu` が `std::prelude` として暗黙 import される。
3. parser が operator table を使いながら CST を作る。
4. infer/lower が CST を AST と型制約へ落とす。
5. `LowerState::finalize_compact_results_profiled` が制約を解き、scheme を凍結する。
6. `--infer` では compact な binding type を表示する。
7. `--core-ir` では core program を export して表示する。
8. `--runtime-ir` / `--run` では runtime lowering を行う。
9. `--run` では runtime IR を monomorphize し、VM で評価する。

ユーザーから見ると、`yulang --infer file.yu`、`yulang --core-ir file.yu`、`yulang --run file.yu` が主な確認手段になる。

現在の workspace で `examples/showcase.yu` に対して確認した限り、`--infer` は成功する。

```text
chosen : std::opt::opt<int>
point : {x: int, y: int} -> point
point::norm2 : point -> int
point::x : point -> int
point::y : point -> int
```

一方で同じ file の `--run` は、現状では runtime lowering 中に `std::list::merge` の residual polymorphic binding で失敗した。これはこのレポート作成時点の実装状態の観測であり、言語仕様として確定した制約ではない。

## 3. ソース、モジュール、import

### 3.1 ソース読み込み

source loader は `crates/yulang-source/src/lib.rs` にある。`SourceOptions` は次の情報を持つ。

- `std_root`
- `implicit_prelude`
- `search_paths`

`implicit_prelude` と `std_root` が有効な場合、entry source の先頭に概念的に次が挿入される。

```yu
use std::prelude::*
```

source loader は先頭の metadata だけを先に集める。対象になるのは、先頭に並んだ `mod`、`use`、operator syntax export などである。通常の item が現れた時点で metadata scan は止まる。

### 3.2 module file 解決

`mod foo;` は、同階層の `foo.yu` または `foo/mod.yu` を探す。`std` 配下の import は `std_root` から解決される。それ以外は `search_paths` を使う。

source loader は module / use 依存を見て、file を依存順に並べる。parser で必要になる operator table も、local な public operator 定義と import / reexport された operator syntax から組み立てられる。

### 3.3 `use`

実装上、`use` はかなり広い形を持つ。

```yu
use std::prelude::*
use std::list::{map, filter}
use std::io::Read as Reader
use a/b::c
use m::(+)
use m::{foo, bar, (+)}
```

group import、glob import、alias、operator import、`without` 付き import が CST と source metadata に現れる。

## 4. 字句、layout、演算子

### 4.1 keyword と token

主な keyword は次である。

```text
do if else elsif case catch my our pub use type struct enum role impl act mod as for in with where via mark
```

演算子は固定 token ではなく、operator token として読まれる。演算子優先順位は operator table で管理される。

### 4.2 comment と doc comment

通常 comment として line comment / block comment がある。block comment は nest できる。

doc comment は syntax item として扱われる。

```yu
-- line doc

---
block doc
---
```

block doc の中身は Yumark として parse され、Yulang の fenced code も扱える。ただし doc comment が型推論や runtime にどう効くかは、今回の調査範囲では確認できていない。

### 4.3 indentation と brace

Yulang は indentation block と brace block の両方を受け入れる。たとえば次のような形がある。

```yu
if cond:
  a
else:
  b
```

```yu
if cond { a } else { b }
```

statement の区切りは newline、semicolon、comma など、文脈によって複数ある。

### 4.4 標準演算子

parser の初期 operator table には、概ね次の演算子が入る。

| 演算子 | fixity | 概要 |
| --- | --- | --- |
| `not` | prefix | boolean negation |
| `last` / `next` / `redo` | prefix / nullfix | loop control |
| `return` | prefix | sub return |
| `+` / `-` | prefix / infix | 数値演算 |
| `*` / `/` / `%` | infix | 数値演算 |
| `..` | nullfix / prefix / infix / suffix | range 系 |
| `==` / `!=` / `<` / `<=` / `>` / `>=` | infix | 比較 |
| `and` | infix | short-circuit and |
| `or` | infix | short-circuit or |

実際の表面言語では `lib/std/prelude.yu` も operator 定義を持つ。特に range 系は prelude 側で `(..)`、`(..<)`、`(<..)`、`(<..<)` などが再定義されている。

operator の定義は次の形を取る。

```yu
nullfix (..)
prefix (not) 70
infix (+) 50 50
suffix (!) 80
```

binding としての operator 定義は、優先順位と本体を持てる。

```yu
infix (++) 50 50 = append
```

## 5. 宣言と statement

Yulang の statement parser は、まず expression として読めるだけ読む。その後に statement keyword が来た場合、宣言や制御構文として解釈する。主な statement は次である。

### 5.1 binding

binding は `my` / `our` / `pub` を持つ。

```yu
my x = 1
our answer = 42
pub exported = answer
pub declared
```

関数引数は binding header に直接書ける。

```yu
my add x y = x + y
```

これは lower 時に lambda へ落とされる。

```yu
my add = \x -> \y -> x + y
```

method 風の dotted binding もある。

```yu
our p.norm2 = p.x * p.x + p.y * p.y
```

この形は struct method、extension method、effect method、role method などの候補になる。

### 5.2 visibility

visibility は次の 3 種である。

| visibility | 意味 |
| --- | --- |
| `my` | module 内 private |
| `our` | module 外からも使える実装要素 |
| `pub` | public export |

実装上、module-level の非 public binding は module-private として扱われる。local binding は lexical local である。export collection では `my` と synthetic name が除かれる。

`our` と `pub` の差は、現状のアクセス判定だけを見るとまだ仕様としてかなり近い。公開仕様にするなら、両者の意図を明文化する必要がある。

### 5.3 `type`

`type` は名目的な型や companion module を作るために使われる。

```yu
type list 'a
```

`lib/std/var.yu` などでは self struct を伴う type が使われる。

```yu
type ref 'e 'a with:
  struct self:
    get: () -> ['e] 'a
    update_effect: () -> [ref_update 'a; 'e] ()
```

`impl` の中では associated type の equation としても現れる。

```yu
impl Fold (list 'a):
  type item = 'a
```

現時点の lower 実装では、`type T = ...` は型 alias として扱われない。詳細は追補 16.3 にまとめる。

### 5.4 `struct`

`struct` は名目的な record-like type を作る。

```yu
struct point:
  x: int
  y: int
with:
  our p.norm2 = p.x * p.x + p.y * p.y
```

`struct point { x: int, y: int }` のような brace form もある。constructor と field accessor が生成される。`examples/showcase.yu` では `point` の infer 結果が `{x: int, y: int} -> point` になり、`point::x : point -> int` のような accessor も出る。

### 5.5 `enum`

`enum` は名目的な variant type を作る。

```yu
enum opt 't = nil | just 't
```

brace / indentation form もある。

```yu
enum color:
  red
  green
  blue
```

constructor は value として登録され、pattern match にも使える。

### 5.6 `role`

`role` は型クラス風の interface である。input type parameter と associated type を持てる。

```yu
role Eq 'a:
  our x.eq: 'a -> bool
```

method は `our` binding として宣言される。default body を持つこともできる。role lower では role の type argument、method、associated type、requirement が登録される。

### 5.7 `impl`

`impl` は role の実装である。

```yu
impl Eq int:
  our x.eq y = x == y
```

impl の中の `our` member は候補として公開される。`my` member は helper として impl 内で使える。lower では impl 用の synthetic module が作られ、missing method / unknown method も検査される。

### 5.8 `act`

`act` は algebraic effect の宣言である。

```yu
act console:
  our read: () -> str
  our write: str -> ()
```

operation は binding として登録される。operation signature は、最終戻り位置に latent effect が足りなければ、対象 act の effect row を補う。

`lib/std/flow.yu`、`lib/std/undet.yu`、`lib/std/var.yu`、`lib/std/junction.yu` が実際の effect 利用例になっている。

### 5.9 `where`

`where` は現在の owner / type scope に対して追加制約を置く構文である。

```yu
where:
  T: Role
```

lower 側では、現在の owner と type scope がある場合に role requirement として処理される。

## 6. 式

### 6.1 literal

主な literal は次である。

- integer
- float
- string
- bool
- unit `()`
- tuple
- list
- record

```yu
1
1.5
"hello"
true
()
(1, "x")
[1, 2, 3]
{x: 1, y: 2}
```

list には spread がある。

```yu
[1, ..xs, 3]
```

record literal は field と spread を持つ。

```yu
{x: 1, y: 2, ..rest}
```

### 6.2 名前、path、field

simple name は lexical local、module scope、use import の順で探される。qualified path は module path として解決される。

```yu
x
std::list::map
```

field selection は `x.foo` である。ただし lower コメントにある通り、`x.foo::bar` は「`foo::bar` を `x` に適用する」method sugar として解釈され、通常の record field を取ってから path を進む、という意味ではない。

index は field selection と application に落ちる。

```yu
xs[0]
```

これは概念的に `xs.index 0` 系の呼び出しになる。

### 6.3 application

application には複数の形がある。

```yu
f x y
f(x, y)
f:
  body
lhs | rhs
```

ML-style application は空白でつながる。call syntax の zero arg は unit argument を渡す形に落ちる。

```yu
f()
```

pipeline は左辺を右辺の最初の引数として入れる。

```yu
xs | map f
```

### 6.4 lambda

lambda は `\pat -> body` である。

```yu
\x -> x + 1
\x y -> x + y
```

複数 pattern は nested lambda に落ちる。

### 6.5 block と `with`

block は複数 statement を順に評価し、最後の式が block の値になる。

```yu
{
  my x = 1
  x + 1
}
```

`with:` suffix は、局所的な binding 群を tail expression の前に開く。

```yu
target with:
  our helper = ...
```

lower 実装では、with block 内の `our` / `pub` name が tail から見える。

### 6.6 `if`

`if` は式である。`elsif` と `else` を持てる。

```yu
if cond:
  a
elsif other:
  b
else:
  c
```

`else` がない場合、false branch は unit になる。

condition が effectful な場合、`std::junction::junction` を使って effectful condition を扱う経路がある。

### 6.7 `case`

`case` は pattern match である。

```yu
case value:
  nil -> 0
  just x -> x
```

guard も持てる。

```yu
case value:
  x if x > 0 -> x
  _ -> 0
```

arm は上から順に試される。

### 6.8 `catch`

`catch` は effect handler である。

```yu
catch expr:
  value -> value
  effect_pat, k -> body
```

arm の pattern が 1 個なら value arm、2 個なら effect arm として扱われる。effect arm の 1 個目は effect operation と payload に match し、2 個目は continuation を受け取る。

runtime では、handler は thunk を force して、値なら value arm、effect request なら対応する effect arm を実行する。continuation を呼ぶと、捕まえた地点以降の計算を再開する。

### 6.9 `do`

`do` は continuation marker である。

```yu
my x = effectful do
rest
```

lower では、`do` の後続 statement が lambda として切り出され、`do` の位置に渡される。effectful API を見た目上は direct style で書くための構文である。

### 6.10 `sub` と `return`

`sub:` は `std::flow::sub::sub` に落ちる。

```yu
sub:
  return 1
```

label 付き sub もある。

```yu
sub 'outer:
  return 'outer 1
```

label 付きの場合、lower は label 専用の synthetic act を作り、body 内の bare / labeled `return` をその act の operation に結びつける。

### 6.11 `for`、`last`、`next`、`redo`

`for` は標準ライブラリの loop effect と fold に支えられている。

```yu
for x in xs:
  body
```

label 付き loop もある。

```yu
for 'outer x in xs:
  last 'outer value
```

`last`、`next`、`redo` は operator として prelude に定義され、`lib/std/flow.yu` の `loop` act に接続される。

### 6.12 参照

参照読み取りは `$x`、更新は `&x = value` である。

```yu
my $current = 0
$current
&current = $current + 1
```

lower 実装では、`$x` は `&x` という reference binding を探す。local な var act alias があればその `get()` を呼び、なければ `std::var::ref::get` を使う。assignment も同様に var act の `set` または `std::var::ref` の update として扱われる。

### 6.13 rule と mark

parser には rule / mark 系の構文がある。

```yu
rule { ... }
~"pattern"
```

quoted mark expression も parser に存在する。ただし lower 実装はこれらに式としての意味をまだ与えておらず、fallback で unit に落ちうる。現段階では「parser-only feature」として扱うのが安全である。

## 7. pattern

pattern は binding、destructuring、match、catch で使われる。lower AST 上の主な pattern は次である。

- wildcard
- literal
- tuple
- list
- record
- constructor
- polymorphic variant
- name binding
- or pattern
- as pattern

### 7.1 wildcard と name

```yu
_
x
```

name は、constructor として解決できる場合は constructor pattern になり、そうでなければ binding になる。

### 7.2 literal pattern

```yu
0
true
"ok"
```

parser は string literal pattern も持つ。ただし追補 16.6 の再調査では、source の string literal pattern は現状 string pattern として lower されず、wildcard に落ちうることが分かった。

### 7.3 tuple、list、record

```yu
(x, y)
[head, ..middle, tail]
{x, y: renamed, z = default}
```

record pattern は shorthand、rename、default value、spread を持てる。

default value は、field が欠けている場合に評価される。そのため pattern match 自体が effect を持ちうる。

### 7.4 constructor pattern

```yu
nil
just x
Foo::Bar x
```

enum constructor や nominal constructor は pattern として使える。

### 7.5 or / as / annotation

```yu
left | right
pat as name
x: int
```

or pattern は複数候補のどれかに match する。as pattern は match した値全体に名前を付ける。annotation は pattern へ型制約を足す。

## 8. 型注釈と型式

型注釈 parser は `crates/yulang-infer/src/lower/signature/parse.rs` にある。表面構文上は parser の `TypeExpr` を経由するが、lower 時には文字列化された型式を signature parser が読む。

### 8.1 基本形

```yu
int
float
bool
str
()
'a
_
List int
std::list::list int
```

`'a` は型変数であり、`_` は fresh wildcard type variable である。

### 8.2 function

```yu
int -> int
int -> bool -> str
```

arrow は右結合である。

function type は value parameter、parameter computation effect、return effect、return value を持つ。core type では次のような構造になる。

```text
Fun {
  param,
  param_effect,
  ret_effect,
  ret,
}
```

### 8.3 effect row 付き function

return effect は arrow の後ろに square bracket で書ける。

```yu
() -> ['e] 'a
() -> [ref_update 'a; 'e] ()
```

row の構文は概ね次である。

```yu
[EffectA, EffectB; tail]
[_]
['e]
```

semicolon の後ろは row tail である。要素が 1 個だけで、それが variable の場合は tail として扱われる。

### 8.4 tuple / record / row

```yu
(int, bool)
{x: int, y: int}
{x?: int, ..tail}
```

record field は required / optional を持つ。spread tail もある。

### 8.5 variant

parser test には polymorphic variant type に見える構文がある。

```yu
:{A int, B}
```

ただし今回の調査では、signature lower から runtime までの扱いを十分に確認できていない。

## 9. 名前解決

名前空間は少なくとも次に分かれている。

- value
- type
- module
- operator value

value lookup は概ね次の順である。

1. lexical local frame を内側から探す。
2. 現在 module から親 module へ lexical module chain を探す。
3. `use` による search set を探す。

type lookup は local frame を使わず、module chain と `use` を探す。qualified path の先頭は module として解決されるため、local binding が qualified path の first segment を奪うことはない。

operator は `(name, fixity)` を key に別扱いされる。これにより、同じ記号でも prefix / infix / suffix / nullfix を別に定義できる。

## 10. 型システムと推論

### 10.1 typed expression

lower 後の expression は、すべて value type と effect type を持つ。

```text
TypedExpr {
  tv,
  eff,
  kind,
}
```

ここで `tv` は式の値型、`eff` はその式を評価するときの computation effect である。

### 10.2 subtyping constraint

推論の基本は `positive <: negative` の制約である。

- positive は produced value / lower bound 側
- negative は consumed value / upper bound 側

型変数は lower bounds と upper bounds を集める。制約解決は union / intersection / row / function / record / variant / nominal type などの shape を見ながら伝播する。

### 10.3 top / bottom、union / intersection

core type には `Never` と `Any` がある。subtyping では bottom / top として振る舞う。

union と intersection も型として存在する。positive union、negative intersection などは制約伝播時に分配される。

### 10.4 function subtyping

function は parameter が反変、return が共変である。

概念的には次のような制約になる。

```text
expected_param <: actual_param
actual_return <: expected_return
```

effect も function type の一部である。実装では parameter effect と return effect が別にあり、argument を値として渡すのか、computation / thunk として渡すのかで effect の流れが変わる。

特に callee が pure value argument を期待する場合、argument の effect は call 全体の effect に合流する。callee が computation argument を期待する場合は、argument effect が parameter effect 側へ入る。

### 10.5 record subtyping

record は field 単位で subtyping される。

- negative 側が required field を要求する場合、positive 側はそれを持つ必要がある。
- positive 側の optional field は required field の証明にはならない。
- negative 側の optional field はなくてもよい。
- spread tail がある場合、見つからなかった field は tail row に流される。

### 10.6 variant subtyping

variant は tag と payload arity を見て対応する。payload は各要素ごとに制約される。

enum constructor などの nominal variant と、構造的 variant / polymorphic variant がどこまで統一されるかは、公開仕様では整理が必要である。

### 10.7 nominal type と variance

`type` / `struct` / `enum` は named constructor として型に出る。constructor argument には variance がある。登録されていない場合は invariant として扱われる。

数値型には builtin の widening がある。実装上、`int` から `float` への制約が特別扱いされる。

### 10.8 row と effect

effect は row として表現される。row は effect atom の集合的な部分と tail を持つ。

effect atom は path と引数列を持つ。row 同士の制約では、同じ path / arity の atom が対応し、effect argument は invariant に制約される。残った atom は tail へ流れる。

```yu
() -> [ref_update int; 'e] ()
```

このような型は、「`ref_update int` effect を起こし、さらに tail `'e` の effect も起こしうる computation」を表す。

### 10.9 scheme と generalization

binding は最終的に `Scheme` を持つ。

```text
Scheme {
  requirements,
  body,
}
```

lower 中は provisional な self scheme を使って相互再帰を扱う。finalize では binding graph の SCC を見て、ready component を compact / freeze する。凍結された scheme は、利用箇所で fresh に instantiate される。

### 10.10 application 推論

application では、callee が function type であるという制約を作る。引数、call effect、return type、式全体の effect が新しい型変数で結ばれる。

概念的には次の制約が作られる。

```text
callee <: arg -> ret
expr_type = ret
expr_effect includes callee_effect, argument_effect, call_effect
```

method call や role method call は、ここで deferred selection として登録され、後の selection solving で record field / extension method / role method などに解決される。

### 10.11 binding 推論

binding lower は、先に module-level binding を登録し、その後に本体を lower する。これにより相互参照や再帰が可能になる。

```yu
my even n = if n == 0: true else: odd (n - 1)
my odd n = if n == 0: false else: even (n - 1)
```

header argument は lambda へ変換され、annotation がある場合は expected type として制約に加わる。

### 10.12 role constraint

role method selection は requirement として scheme に残ることがある。

```yu
role Add 'a:
  our x.add: 'a -> 'a
```

`x + y` のような式は `Add` role method の呼び出しへ落ちる。具体型が決まれば impl candidate に解決される。多相なまま残る場合は、scheme の requirement として表面に出る。

impl は associated type equation も持てる。

```yu
impl Index (list 'a) int:
  type value = 'a
```

selection solving では、record field、extension method、effect method、role method、ref method などが候補になる。

### 10.13 effect operation

`act` の operation は effectful function として見える。operation を呼ぶと、対応する effect atom を持つ computation になる。

handler がない場合、その effect は式の effect row に残る。`catch` で handler がある場合、対応する effect atom が捕捉され、handler body の effect と continuation の effect によって結果 effect が決まる。

### 10.14 reference 推論

`$x` / `&x = value` は、effectful reference operation に落ちる。`lib/std/var.yu` は次を定義している。

```yu
type ref 'e 'a with self:
  effect: 'e
  update: 'a -> ['e] 'a

act var 't:
  our get: () -> 't
  our set: 't -> ()
```

そのため、参照は mutable cell というより、「get/set/update effect を持つ値」として推論される。

## 11. core IR

core IR は `crates/yulang-infer/src/export/core_ir.rs` 周辺で作られる。型は次のような形を持つ。

- `Never`
- `Any`
- `Var`
- `Named`
- `Fun`
- `Tuple`
- `Record`
- `Variant`
- `Row`
- `Union`
- `Inter`
- `Recursive`

expression は typed AST から export される。role requirement、selection、effect、scheme が core program に含まれる。`--core-ir` はこの段階を見るための主要な debugging interface である。

`examples/06_undet_once.yu` に対する `--core-ir` は成功し、graph summary として `57 binding nodes, 1 root nodes, 107 runtime symbols` が出た。

## 12. runtime lowering と実行意味論

### 12.1 runtime IR

runtime IR は `crates/yulang-runtime/src/ir.rs` にある。型はかなり絞られている。

- core primitive type
- function
- thunk

expression kind には次のようなものがある。

- variable
- effect operation
- primitive operation
- literal
- lambda
- apply
- if
- tuple
- record
- variant
- select
- match
- block
- handle
- thunk
- coercion

runtime lowering は core IR の型を投影し、runtime に必要な形だけを残す。

### 12.2 monomorphization

`monomorphize_module` は、runtime 実行前に多相 binding を特殊化する。処理は複数 pass で、概ね次を繰り返す。

- use site から monomorphic instance を作る
- type refinement
- specialization
- canonicalization
- nullary constructor inlining
- residual role / associated binding の解決
- prune
- monomorphic であることの検査

runtime 実行は基本的に monomorphic runtime IR を前提にしている。

### 12.3 値

VM の値は次のような種類を持つ。

- int
- float
- string
- bool
- unit
- list
- tuple
- record
- variant
- effect operation
- primitive operation
- resume continuation
- closure
- thunk
- effect id

### 12.4 評価順序

基本は call-by-value である。ただし parameter type が thunk の場合、argument は delay される。非 thunk が期待される位置では thunk が force される。

block は上から順に statement を評価する。let binding は thunk を force してから binding する。単一 binding closure では recursion 用に `self_name` が入る。

### 12.5 thunk と effect request

effect operation を payload に適用すると thunk ができる。その thunk を `bind_here` で force すると、effect が実行される代わりに `VmRequest` が作られる。

request は次を持つ。

- effect
- payload
- continuation
- blocked id

handler が request を捕まえると、payload pattern と continuation を effect arm に渡す。continuation は inside handler / outside handler の境界を保った形で再開される。

### 12.6 handler

runtime の `Handle` は body を評価し、thunk を force する。

- value が返った場合、value arm を試す。
- effect request が返った場合、対応する effect arm を探す。
- 対応する arm がなければ request は外側へ伝播する。

guard stack / effect id により、handler region の内外で effect が誤って捕まらないように制御される。

### 12.7 pattern match

runtime pattern match は arm を上から順に試す。guard は bool でなければならない。record pattern の default expression は、field が存在しない場合に評価される。

### 12.8 coercion

runtime coercion として確認できる主なものは `int` から `float` への変換である。

### 12.9 primitive operation

VM は標準的な primitive operation を持つ。

- bool: `not`, equality
- int: arithmetic, comparison, `to_string`, hex formatting
- float: arithmetic, comparison, `to_string`
- string: length, index, range, splice, concat
- list: empty, singleton, length, merge, index, range, splice, view

標準ライブラリの role method は、最終的にはこれらの primitive operation に落ちることが多い。

## 13. 標準ライブラリ

### 13.1 prelude

`lib/std/prelude.yu` は多くの基本要素を reexport する。

- `str`
- `int`
- `float`
- `bool`
- `list`
- `opt`
- `range`
- `index`
- `var`
- `junction`
- `flow`

主な role も prelude にある。

- `Eq`
- `Ord`
- `Add`
- `Sub`
- `Mul`
- `Div`
- `Len`
- `Display`
- `LowerHex`
- `UpperHex`

`+`、`-`、`*`、`/`、comparison、`not`、range、`last`、`next`、`redo`、`return` などの operator も prelude で表面構文に接続される。

### 13.2 flow

`lib/std/flow.yu` は `sub` と `loop` の制御構文を effect として定義する。

```yu
act sub 'a:
  our return: 'a -> never
```

`sub` は `return` を handler で捕まえる。`loop` は `last` / `next` / `redo` を handler で捕まえ、`for` を fold と組み合わせて実現する。

### 13.3 undet

`lib/std/undet.yu` は nondeterminism を effect として定義する。

- `branch`
- `fail`
- `guard`
- `each`
- `list`
- `logic`
- `once`

extension method として `.list`、`.logic`、`.once` があり、effectful な nondeterministic computation を list / logic / opt 的な結果へ集約する。

### 13.4 list

`lib/std/list.yu` は名目的な `list 'a` を定義し、list view、index、fold、append、map、filter、sort などを提供する。

### 13.5 range

`lib/std/range.yu` は bound と range の enum を定義し、range operator から作られる値を扱う。`Fold` impl により `for` の入力にもなる。

### 13.6 fold

`lib/std/fold.yu` は `Fold` role を定義する。associated type `item` を持ち、effect-polymorphic な `fold` signature を持つ。`find`、`contains` などの default method もある。

### 13.7 index

`lib/std/index.yu` は `Index` role と associated type `value` を定義する。list や string の indexing はこの role によって表面構文と接続される。

### 13.8 var

`lib/std/var.yu` は reference と variable effect を定義する。`$x` / `&x = value` の表面構文はこの module と密接に対応する。

### 13.9 junction

`lib/std/junction.yu` は effectful condition を扱うための `junction` effect を定義する。`if` の condition が pure でない場合に、lower 側でこの仕組みへ寄せる経路がある。

## 14. 仕様化するときに先に決めたい点

### 14.1 `my` / `our` / `pub` の差

現状の実装では `my` は private として分かりやすい。一方で `our` と `pub` の公開範囲や、public API と implementation candidate の差は仕様として明文化した方がよい。

### 14.2 `type T = ...` の扱い

parser は alias 風の `type` を読めるように見えるが、lower 実装は alias body を読んでいない。現状仕様としては、`type` は nominal type と companion module の宣言であり、alias は載せない方がよい。

### 14.3 parser-level feature の扱い

rule / mark / Yumark は parser には存在するが、lower ではまだ意味づけされていない。公開仕様に載せるなら、experimental 章に隔離するか、parser-only と明記するのがよさそうである。

### 14.4 effect row の正規形

row は実装上かなり重要である。公開仕様では、row item の重複、順序、tail の表記、effect atom の引数 variance、handler 後の残余 effect を、例と一緒に定義した方がよい。

### 14.5 role selection の曖昧性

record field、extension method、role method、effect method、ref method が同じ `.foo` 構文に集まる。候補の優先順位、曖昧な場合の error、impl overlap を仕様化する必要がある。

### 14.6 runtime と多相性

runtime は monomorphic IR を強く期待している。公開仕様では「実行可能 program は runtime lowering 後に monomorphize 可能でなければならない」と書くか、多相 runtime を将来仕様として残すかを決める必要がある。

### 14.7 現在の実装不整合

この調査時点では `examples/showcase.yu` の `--infer` は通るが、`--run` は residual polymorphic runtime IR binding で失敗した。これは標準ライブラリや monomorphization の現状不整合の可能性がある。仕様を書く前に、代表 examples の `--run` が通る状態を基準にしたい。

## 15. 実装参照

このレポートを書くにあたって、特に参照した入口は次である。

- `crates/yulang/src/main.rs`
- `crates/yulang-source/src/lib.rs`
- `crates/yulang-parser/src/lex.rs`
- `crates/yulang-parser/src/op.rs`
- `crates/yulang-parser/src/stmt/mod.rs`
- `crates/yulang-parser/src/expr/mod.rs`
- `crates/yulang-parser/src/stmt/type_decl.rs`
- `crates/yulang-infer/src/ast.rs`
- `crates/yulang-infer/src/lower/mod.rs`
- `crates/yulang-infer/src/lower/ctx.rs`
- `crates/yulang-infer/src/lower/expr/mod.rs`
- `crates/yulang-infer/src/lower/stmt/mod.rs`
- `crates/yulang-infer/src/lower/signature/parse.rs`
- `crates/yulang-infer/src/solve/mod.rs`
- `crates/yulang-infer/src/solve/selection/mod.rs`
- `crates/yulang-infer/src/solve/selection/method.rs`
- `crates/yulang-infer/src/solve/selection/role_method.rs`
- `crates/yulang-infer/src/solve/selection/effect_method.rs`
- `crates/yulang-infer/src/export/core_ir.rs`
- `crates/yulang-runtime/src/lower/mod.rs`
- `crates/yulang-runtime/src/monomorphize/mod.rs`
- `crates/yulang-runtime/src/vm/mod.rs`
- `crates/yulang-runtime/src/vm/interpreter.rs`
- `lib/std/prelude.yu`
- `lib/std/flow.yu`
- `lib/std/undet.yu`
- `lib/std/list.yu`
- `lib/std/range.yu`
- `lib/std/fold.yu`
- `lib/std/index.yu`
- `lib/std/var.yu`
- `lib/std/junction.yu`
- `examples/showcase.yu`
- `examples/06_undet_once.yu`

## 16. 追補 1: 未確定点の再調査

この章は、最初のレポート後にもう一段実装へ潜って分かったことを追記する。特に「未確定」と書いたもののうち、実装を見れば判断できるものを中心に潰している。

### 16.1 標準ライブラリの file path と module path

repository 上の標準ライブラリは `lib/std/*.yu` にある。一方、言語内の module path は `std::...` である。

たとえば `lib/std/list.yu` は `std::list` module として読まれ、`lib/std/prelude.yu` は `std::prelude` として暗黙 import される。

### 16.2 builtin primitive と `type list 'a with:`

`list` と `str` は、標準ライブラリ source を読む前に primitive installer が `std::list::list` と `std::str::str` の型名を登録する。入口は `crates/yulang-infer/src/lower/primitives/mod.rs` で、`ensure_builtin_type` が型名前空間へ def を入れる。

その後で `lib/std/list.yu` の次の宣言が読まれる。

```yu
type list 'a with:
    our xs.append ys = std::list::append xs ys
    our xs.splice r ys = std::list::splice xs r ys
    our &xs.push x = &xs = $xs.append [x]
```

`lower_type_decl` は、同じ module にすでにその型が登録済みで、かつ `struct self` / `enum self` を持たない場合、新しい型を作らず companion module を再オープンする。そのため `type list 'a with:` は「primitive 型 `std::list::list` に method を足す宣言」として働く。

同じ仕組みにより、将来的には builtin や外部定義の nominal type に Yulang 側で method を追加できる。

### 16.3 `type` は alias ではない

最初のレポートでは `type T = ...` を parser-level の可能性として書いたが、lower 実装を見る限り、現時点の `type` は型 alias ではない。

`crates/yulang-infer/src/lower/stmt/decl/type_decl.rs` の `lower_type_decl` は、`TypeExpr` の RHS を alias body として読まない。処理しているのは次である。

- nominal type 名を型名前空間へ登録する
- 同名の value def を登録する
- companion module を開く
- `with:` 内の binding を nominal type method として登録する
- `with: struct self:` があれば、その field から constructor と accessor を合成する
- すでに型が存在し、`self` 宣言がなければ companion module だけを再オープンする

したがって公開仕様では、`type` を alias として載せるべきではない。少なくとも現在の実装仕様としては、`type` は opaque / primitive / self-struct 付き nominal type と companion method のための宣言である。

### 16.4 `type ... with: struct self:`

`type ref 'e 'a with: struct self:` は実装済みである。`lib/std/var.yu` の例は次である。

```yu
type ref 'e 'a with:
    struct self:
        get: () -> ['e] 'a
        update_effect: () -> [ref_update 'a; 'e] ()
```

この形では、外側の nominal type 自体が struct-like な field set を持つ。lower は field accessor を companion module に登録し、constructor は record を受け取って nominal type を返す function として制約される。

概念的には次のような constructor / accessor が作られる。

```text
ref : { get: () -> ['e] 'a, update_effect: () -> [ref_update 'a; 'e] () } -> ref 'e 'a
ref::get : ref 'e 'a -> () -> ['e] 'a
ref::update_effect : ref 'e 'a -> () -> [ref_update 'a; 'e] ()
```

実装では field accessor の frozen scheme と principal body も synthetic に作られる。

### 16.5 `type ... with: enum self:` は検出だけある

`lower_type_decl` には `type_decl_self_enum` があり、`with:` block 内の `enum self` を探している。ただし、その結果は現在 lower に使われていない。`self_enum` は「既存 type を再オープンするかどうか」の判定には使われるが、enum variant を外側 type の variant として lower する処理はない。

つまり、現時点で仕様化できるのは `struct self` だけである。`enum self` は構文を見つける下準備だけあり、実用的な意味論は未実装と見るのが正しい。

### 16.6 source の string pattern は現在 wildcard になりうる

runtime IR は literal pattern として string を扱える。`crates/yulang-runtime/src/lower/patterns.rs` は `core_ir::Pattern::Lit(lit)` を受け取り、`lit_type` による型照合を行う。

しかし source pattern の lower は別である。`crates/yulang-infer/src/lower/stmt/patterns/pattern.rs` の `literal_pat` は、現時点で次だけを literal pattern として認識する。

- `true`
- `false`
- number

`StringLit` node は `literal_pat` で見られていない。そのため source 上で次のような pattern を書いた場合、現状の lower では string literal pattern としては落ちない。

```yu
case s:
    "ok" -> 1
    _ -> 0
```

実装の分岐を読む限り、string literal は constructor path でも binding name でもないので、`PatKind::Wild` に落ちる可能性が高い。これは仕様候補というより、修正対象の実装挙動である。公開仕様では string pattern を載せるなら、先に lower を実装する必要がある。

### 16.7 rule / mark は parser-only で、lower では unit に落ちうる

`rule { ... }` と `~"..."` は parser にかなり具体的な構文がある。

`rule { ... }` の body は PEG 風で、次を持つ。

- `|` による alternation
- 空白による sequence
- `name = rhs` capture
- `*` / `+` / `?` / `*?` / `+?` quantifier
- `.field`
- `::path`
- call `(...)`
- index `[...]`
- string item

`~"..."` literal もあり、`{...}` interpolation と `:name` / `:{name}` lazy capture を持つ。

quoted mark expression は次の 2 形である。

```yu
'[inline yumark]
'{
block yumark
}
```

ただし、`crates/yulang-infer/src/lower/expr/atom.rs` は `SyntaxKind::RuleExpr`、`RuleLit`、`MarkExpr` を特別扱いしていない。該当 node は atom lower の fallback に入り、unit literal に落ちうる。

そのため、現時点では rule / mark を「表面構文として parse されるが、式としての意味論は未実装」と書くのが正確である。最初のレポートの「parser-level feature」という表現は正しかったが、より強く「lower はまだ意味を付けていない」と言える。

### 16.8 `$x` binding の実装詳細

`my $x = init` は単なる sigil 名ではなく、block suffix と組み合わせて synthetic act を作る。

pattern 中の `$x` は内部的に次の 2 名へ分解される。

```text
#x   初期値用 local binding
&x   reference 用 binding / alias
```

`crates/yulang-infer/src/lower/stmt/var/sigil.rs` がこの変換を行う。`lower_var_binding_suffix` は、`std::var::var` act を source template として synthetic act を materialize し、block body 全体を `run init body` で包む。

`&x` そのものが body 内で読まれる場合だけ、実際の local binding として `&x` が materialize される。読まれない場合は、context 内の alias として `&x -> synthetic act` だけが登録される。これにより、普通の `$x` 読み書きだけなら余分な reference value を作らない。

`&x = value` は assignment target として見たときは `set` operation へ落ちる。`&x.field` のように reference の field を投影する場合は、selection solver の ref field projection 経路に乗る。

### 16.9 selection 解決の優先順位

`.name` selection は、lower 時点では deferred selection として積まれる。解決は `crates/yulang-infer/src/solve/selection/method.rs` にあり、概ね次の順で試される。

1. receiver の nominal type に登録された method / field accessor
2. `std::var::ref` の内側 type に対する ref method
3. `std::var::ref` の内側 type の field projection
4. role method
5. receiver effect row から見つかる effect method
6. module から見える extension method

この順序は仕様上かなり重要である。たとえば ref field projection は、同名の ref type method や normal type method がある場合には抑制される。extension method は、アクセス可能な同名候補がちょうど 1 つのときだけ解決される。複数ある場合はここでは曖昧 error ではなく、extension method としては解決しない。

effect method は、receiver の effect row から effect path を集め、その effect に登録された method を探す。候補が 1 つなら採用、複数なら `AmbiguousEffectMethod` が報告される。effect path の一致は完全一致だけでなく、fully qualified path の prefix 関係も見ている。

role method は、候補 impl の input argument を compact type pattern と照合して決まる。複数候補が合った場合は、互いの pattern match によって「より具体的な候補」を残す。最終的に 1 つなら採用、0 なら missing impl、複数なら ambiguous impl になる。impl に method 本体がなく、role 側に default body があれば default method が使われる。

### 16.10 selection と effect の流れ

selection はただの field access ではなく、method call として制約される。

`.name` の receiver は、選ばれた method の最初の引数として渡される。receiver が value として期待される場合、receiver の evaluation effect は method call effect に合流する。receiver が computation として期待される extension/effect method の場合は、receiver effect は parameter effect として扱われる。

この差は `SelectedReceiverStyle::Value` / `SelectedReceiverStyle::Computation` として実装されている。effectful computation に対する method と、普通の値に対する method を同じ `.name` 構文で扱うための核になっている。

### 16.11 公開仕様へ反映するときの修正候補

この追補を踏まえると、公開仕様草案では次を直した方がよい。

- `type` を alias として扱う記述は消す。
- `type ... with: struct self:` は正式に説明する。
- `type ... with: enum self:` は未実装として experimental か削除にする。
- string literal pattern は現状未実装または bug として扱う。
- rule / mark は parser-only と明記する。
- `.name` selection の解決順序を仕様本文へ昇格する。
- `notes/` ではなく追跡される `docs/` / `spec/` に移すなら、標準ライブラリ参照 path は `lib/std/*.yu` に統一する。

## 17. 追補 2: examples から見える言語中核

この章では `examples/*.yu` を入口にして、どの機能が「ただのライブラリ」ではなく、構文、lower、型推論、runtime に食い込んでいるかを整理する。

### 17.1 example 実行状況

この調査時点の workspace で `--run` した結果は次である。

| file | `--run` 結果 | 見ている機能 |
| --- | --- | --- |
| `examples/01_struct_with.yu` | `[0] 25` | struct、with method、field selection、role operator |
| `examples/02_refs.yu` | `[0] (11, 21)` | `$x` / `&x = ...`、synthetic var act |
| `examples/03_for_last.yu` | `[0] 5` | `for`、range、loop control |
| `examples/04_sub_return.yu` | `[0] 5` | `sub:`、`return`、loop からの早期脱出 |
| `examples/05_undet_all.yu` | `[0] [5, 6, 7, 6, 7, 8, 7, 8, 9]` | nondeterminism、extension method `.list` |
| `examples/06_undet_once.yu` | runtime lowering 失敗 | unbounded nondeterministic search、`.once` |
| `examples/07_junction.yu` | `[0] 1` | effectful boolean condition、junction |
| `examples/08_types.yu` | `[0] 42` | public binding、role requirement 表示 |
| `examples/09_optional_record_args.yu` | `[0] 6`, `[1] 2`, `[2] 12`, `[3] 12` | optional record pattern default |
| `examples/showcase.yu` | runtime lowering 失敗 | struct、refs、junction、undet の混合 |

失敗している 2 つは、いずれも runtime lowering で `std::list::merge` の residual polymorphic binding が残る。`--infer` は通るため、表面言語と推論が直ちに壊れているというより、runtime lowering / monomorphize 側で多相 primitive 参照が残っている問題に見える。

### 17.2 struct with は構文、型登録、selection solver の合成機能

`examples/01_struct_with.yu` は小さいが、かなり多くの機構を通る。

```yu
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

ここで起きることは次である。

- `struct point` が nominal type `point` を型名前空間へ登録する。
- 同名 value `point` が constructor として登録される。
- `point::x` / `point::y` が field accessor として companion module に登録される。
- `with:` 内の `our p.norm2` が type method として登録される。
- `.norm2` は syntax 上は field selection だが、lower では deferred selection になる。
- selection solver が receiver type `point` から `point::norm2` を解決する。
- `*` と `+` は parser 組み込み演算子ではなく、prelude の role method call として解決される。

つまり、struct method は単なる record field ではない。nominal type、companion module、deferred selection、role operator がつながることで動く。

`--infer examples/01_struct_with.yu` では、`point::norm2` は次のように少し多相に出る。

```text
point::norm2 : Mul<int | α>, Add<int | α> => point -> α | int
```

annotation を付けた `showcase.yu` の `our pt.norm2: int = ...` では `point -> int` に締まる。この差から、method 本体の arithmetic は role constraint として残りうることが分かる。

### 17.3 `$x` / `&x` は構文 sugar ではなく effect scope を作る

`examples/02_refs.yu` は次の形を持つ。

```yu
{
    my $x = 10
    my $y = 20

    &x = $x + 1
    &y = $y + 1

    ($x, $y)
}
```

これは単に mutable variable を持つわけではない。lower は `$x` pattern を見つけると、内部名 `#x` と `&x` を作り、`std::var::var` act をもとに synthetic act を materialize する。その後、後続 block を `run init body` で包む。

このため `$x` の read / write は、言語の通常の値環境ではなく、effect handler によって局所 state を模倣する。`&x` が実際に値として読まれない場合は local binding を作らず、context alias だけで済ませる最適化も入っている。

仕様上は、次のように書けそうである。

- `my $x = init` は、後続 scope に `x` の mutable cell effect を導入する。
- `$x` はその cell の `get` operation を呼ぶ。
- `&x = v` はその cell の `set` operation を呼ぶ。
- `&x` が値として必要な場合は `std::var::ref e a` が materialize される。

これは library だけでは実現できない。`$` / `&` の sigil pattern、assignment target 判定、synthetic act materialization が lower に食い込んでいる。

### 17.4 `for` は statement 構文だが、実体は `Fold` と `std::flow::loop::for_in`

`examples/03_for_last.yu` は次である。

```yu
{
    for x in 0..:
        if x == 5: last
        else: ()
    5
}
```

`for` は parser / lower に専用 node を持つ。`crates/yulang-infer/src/lower/stmt/control/for_stmt.rs` は、iterator expression と body pattern を取り出し、body を lambda に包んで次のような呼び出しへ落とす。

```text
std::flow::loop::for_in xs (\x -> body)
```

label なしなら `std::flow::loop::for_in`、label 付きなら `std::flow::label_loop` から synthetic act を作って、その `for_in` を呼ぶ。

`for` の iterable 性は組み込み protocol ではなく `Fold` role に寄せられている。`lib/std/range.yu` と `lib/std/list.yu` がそれぞれ `impl Fold ...` を持つので、range や list が `for` で使える。

`last` / `next` / `redo` は loop act の operation であり、prelude の nullfix / prefix operator として表面構文に出る。したがって `for` は「構文は言語中核、反復 protocol と control は標準ライブラリ」という分担になっている。

### 17.5 `sub:` と `return` は effect handler を直書きしないための構文

`examples/04_sub_return.yu` は、`sub:` と `return` が effect と handler の sugar であることを示している。

```yu
sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
```

`lib/std/flow.yu` の `sub` act は `return: 'a -> never` を持つ。`sub(x)` は `catch x:` で `return a` を捕まえて `a` を返し、普通の値 `a` もそのまま返す。

```yu
pub sub(x: [_] _) = catch x:
    return a, _ -> a
    a -> a
```

表面構文としての `sub:` は lower で `std::flow::sub::sub` 呼び出しへ落ちる。`return` は prelude で prefix operator として `std::flow::sub::return` に接続されるが、label 付き sub の場合は lower が label 専用 synthetic act を作る。

ここも library だけではなく、`sub:` block、`return` operator、label alias の解決が lower に入っている。

### 17.6 nondeterminism は act + extension method + runtime handler の合成

`examples/05_undet_all.yu` と `examples/06_undet_once.yu` は `std::undet` を使う。

```yu
use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).list
```

`lib/std/undet.yu` は `undet` act を定義する。

```yu
pub act undet:
    pub branch: () -> bool
    pub fail: () -> never
```

`each xs` は `branch()` によって各候補を選び、選べなければ `fail()` する。`.list`、`.logic`、`.once` は computation receiver を受ける extension method として定義されている。

```yu
pub (x: [_] _).list = list x
pub (x: [_] _).logic = logic x
pub (x: [_] _).once = once x
```

この形が重要である。`.list` は普通の値 method ではなく、effectful computation そのものを receiver に取る。selection solver では `receiver_expects_computation` が効き、receiver effect が value evaluation effect として先に消費されず、method の parameter computation effect として渡される。

したがって nondeterminism は、act / catch / continuation は標準ライブラリで書けるが、「effectful computation に method を生やす」selection の仕組みが言語中核に入っている。

### 17.7 junction は `if` condition に食い込んでいる

`examples/07_junction.yu` は、普通の boolean 条件に見えるが、実際には effectful condition を使っている。

```yu
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

`lib/std/junction.yu` では `any` と `all` が `junction` act の operation を起こす。`junction(x)` は `catch x:` で `or()` / `and()` を捕まえ、true/false 両方の continuation を組み合わせる。

lower 側では `if` condition を特別に見る。`lower_if` は condition を lower した後、effect が exact pure row でなければ `junction::junction cond` を挟む。

```text
if cond then a else b
```

は、condition が pure なら普通に bool として扱われる。condition が effectful なら、概念的に次のようになる。

```text
if junction::junction cond then a else b
```

これはかなり言語に食い込んだ設計である。`any` / `all` 自体は library だが、`if` が effectful condition を自動で junction に通すのは lower の専用規則である。

### 17.8 optional record args は record pattern default として実装されている

`examples/09_optional_record_args.yu` は「named optional arguments」に見える。

```yu
my area({width = 1, height = 2}) = width * height

area { width: 3 }
area {}
area { width: 3, height: 4 }
```

しかし実装上は function argument の特別規則ではなく、record pattern の default である。

pattern lower は `{width = 1}` を `RecordPatField { name: width, default: Some(1) }` として持つ。型制約では default を持つ field が optional field になる。

```text
area : {width?: α, height?: α} -> ...
```

VM では record pattern match 時に field が存在しなければ default expression を評価し、その値を field pattern に bind する。`next_area` のように後続 default が先の field を参照できるのは、field を順に処理し、default を現在の environment で評価しているからである。

```yu
my next_area({width = 2, height = width + 1}) = width * height
```

これは「関数引数機能」ではなく、「pattern matching の機能が関数引数にも使われている」例である。

### 17.9 public binding と role requirement の表示

`examples/08_types.yu` は `--infer` のための example である。

```yu
our twice x = x + x
our answer = twice 21
```

`--infer` では public / exported binding の scheme が表示される。

```text
answer : int
twice : Add<α> => α -> α
```

`+` は `Add` role method なので、`twice` は `Add<α>` requirement を持つ多相関数になる。`answer` は `21` で使われることで `int` に解決される。

この example は、role constraint が型表示の表面に出ることを示している。型推論の仕様では、単なる principal type だけでなく、role requirement の表示と generalization も公開 API として扱う必要がある。

### 17.10 showcase は境界をまとめて踏む統合 example

`examples/showcase.yu` は次を同時に使う。

- struct method
- explicit type annotation
- junction condition
- nondeterminism `.once`
- enum pattern `opt::just` / `opt::nil`
- `$current` / `&current`
- method selection `.norm2`

```yu
my chosen = ({
    if all [1, 2, 3] < any [2, 3, 4]:
        each [3, 4, 5]
    else:
        2
}).once
```

この部分は、effectful condition を `junction` で bool にし、その中で `undet` effect を起こし、最後に `.once` で `opt<int>` に畳む。つまり effect が複数種類同時に存在し、handler / extension method / selection が重なっている。

`case chosen:` では `opt` enum の constructor pattern で分岐し、`just y` の中で reference を作って更新し、最後に nominal method を呼ぶ。

この example が `--infer` では通るが `--run` で失敗するのは、言語表面の意図は推論できているが、runtime lowering がすべての多相 primitive を monomorphic に落とし切れていないことを示している。

### 17.11 examples から見た「言語に食い込んでいる」機能一覧

examples を基準に分けると、次は language core に近い。

- indentation / brace block
- `struct` / `enum` / `type` / companion module
- `with:` method block
- `role` / `impl` / role requirement
- deferred selection `.name`
- operator definitionと operator lowering
- `act` / `catch` / continuation
- `sub:` / labeled return alias
- `for` statement lowering
- `$x` / `&x` sigil reference lowering
- optional record pattern default
- effectful condition の junction 挿入
- computation receiver extension method
- runtime monomorphization requirement

一方で、次は標準ライブラリでかなり書けている。

- arithmetic / comparison の具体 impl
- range constructor
- list operations
- `Fold` protocol
- `sub` / `loop` / `label_loop` の handler 本体
- nondeterminism の探索戦略
- junction の boolean 合成戦略
- reference cell の get/set/run handler

ただし「標準ライブラリで書けている」機能も、たいていは言語中核の hook に乗っている。たとえば `for` は `Fold` を呼ぶだけではなく専用 lower を持ち、junction は `if` lower に hook があり、undet の `.once` は computation receiver selection が必要である。Yulang の仕様を書くときは、「ライブラリ関数として定義される意味」と「そのライブラリ関数へ自動で落とす構文規則」を分けて書くと読みやすい。
