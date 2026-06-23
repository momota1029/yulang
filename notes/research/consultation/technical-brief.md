# Yulang における高階関数の型推論と hygienic effect subtraction

Subtitle: Effect-only contracts, residual-row-polymorphic handler combinators,
and principal weighted schemes.

Status: draft for an initial research consultation, 2026-06-23.

Compiler snippets below were collected on 2026-06-23 from a working tree based
on implementation commit `8d12fc8e`. Right-hand IR is omitted from the displayed
public type lines.

## 1. 問題と相談事項

Yulang は、代数的エフェクトとハンドラを備え、値型と effect row を
subtyping 制約から同時に推論する実験的プログラミング言語である。

本資料の中心的な問題は、単に effect row を推論できるかではない。
高階関数の境界を越えて流入した effect の由来を失わず、handler による
effect subtraction を行いながら、利用者には一般的な公開型を提示できるか、
という問題である。

例えば、次の高階関数を考える。

```yu
my compose f g x = f (g x)
```

`g x` が effect `h` を発生させるとき、`f` の内部にある `h` handler が
その effect を偶然捕捉してはならない。その effect は `f` の内部で発生した
ものではなく、`compose` の呼出し側から渡された計算に由来するからである。
通常の effect row subtraction だけでは、この由来を表現できない。

Yulang の推論器は、subtyping 制約に方向付きの stack weight を付与し、
各 handler 境界から捕捉可能な effect family を記録する。概略的には、

```text
alpha @L <: [K; beta]
J = K ∩ Common(L)
```

とし、handler が実際に除去できる head を `J` に限定する。`J` が非空なら、

```text
alpha <: [J; gamma]
gamma @(L - J) <: beta
```

へ分解する。stack weight は handler hygiene の内部証拠であり、通常の公開型には表示しない。

現在の実装では、次の性質を観察している。

1. 具体的な値型や effect family 集合を指定せずに、高階関数の値型と latent effect を一般化できる。
2. handler combinator の返り値型と residual effect row を一般化できる。
3. annotation は具体的な値型を選択せず、主に関数の形と effect の可視性・流出を制約する。

一方、詳細な形式化は簡略化した中核言語を対象としている。本資料では、実装で観察している性質、
中核言語についての定理、および両者の対応が未整理な部分を区別して述べる。

## 2. コンパイラで観察している二つの例

### 2.1 高階関数の latent effect

Source: `notes/research/consultation/examples/high_order_inference.yu`

```yu
our apply f x = f x
our twice f x = f (f x)
our use_int = twice (\x -> x + 1) 20

use_int
```

導入例として見たい型は次である。

```text
apply : (α ->[ε] β) -> α ->[ε] β
```

実際の compiler output:

```text
d1:apply: ('a -> ['c] 'b) -> 'a -> ['c] 'b
d2:twice: (('a | 'c) ['d] -> ['d & 'e] 'c & 'b) -> 'a -> ['e] 'b
d3:use_int: int
```

`apply` では、関数引数の latent effect `'c` が呼出し側へそのまま残る。`twice` は
より複雑な公開型を持つため、本文では導入例ではなく付録の canary として扱う。

### 2.2 handler combinator の residual row

Source: `notes/research/consultation/examples/local_sub_handler.yu`

```yu
pub act sub 'a:
  pub return: 'a -> never
  pub sub(x: [_] 'a): 'a = catch x:
    return a, _ -> a
    a -> a

pub act note:
  pub tell: () -> ()

our use_int = sub::sub:
  sub::return 0

our use_str = sub::sub:
  sub::return "done"

our use_residual() = sub::sub:
  note::tell()
  1

(use_int, use_str, use_residual)
```

`[_] 'a` は concrete value type や effect family 集合を固定しない skeleton である。
ここで見たい性質は、同じ handler combinator が返り値型と residual row の両方を一般化すること、
および handler 内に残る別 effect が public residual row へ出ることである。

実際の compiler output:

```text
pub d1:"sub.return": 'a -> [sub 'a] never
pub d2:"sub.sub": 'a [sub('c & 'a); 'b] -> ['b] 'a | 'c
pub d4:"note.tell": () -> [note] ()
d5:use_int: int
d6:use_str: std::text::str::str
d7:use_residual: () -> [note] int
```

`use_int` と `use_str` は同じ `sub.sub` を異なる値型で使う。`use_residual` は
`sub` effect が handler に処理され、`note` effect だけが residual row として外へ残る例である。

## 3. 方向付き weight による解決の要点

内部制約は、概略として次の流れで扱う。

```text
surface term
  -> skeleton / annotation lowering
  -> weighted subtype constraints
  -> weighted row split
  -> saturation and compact extraction
  -> public scheme projection
```

制約は方向付き weight を持つ。

```text
T @L <: @R U
```

effect row upper bound は、左側 weight を通して可視な family だけで分割する。

```text
alpha @L <: [K; beta]
J = K ∩ Common(L)
alpha <: [J; gamma]
gamma @(L - J) <: beta
```

`Common(L)` は active boundary を通して handler から見える effect family の共通部分である。
handler は `K` 全体ではなく、`K ∩ Common(L)` だけを処理できる。

stack evidence は handler hygiene と residual subtraction の内部証拠であり、public scheme には出さない。
public surface では ordinary effect row として説明できる residual だけを表示する。

## 4. 形式化の範囲と対応

現時点の中核言語の形式化は、次の範囲を対象にしている。

- 完全 shallow handler
- effect-only skeleton
- rank-1 let polymorphism
- monomorphic `let rec`
- finite effect family
- directed stack weight による effect subtraction
- colored handler soundness
- principal weighted scheme

範囲外または未整理のもの:

- polymorphic recursion
- 任意の実装 constraint graph に対する無条件停止性
- effect family の型引数と ADT を含む surface language 全体
- public scheme projection 後にも同じ意味で principal と呼べるか
- same-boundary alias-cycle subsumption の完全な形式化
- data-position private tail と local wildcard handler evidence を同一概念として扱うべきか

## 5. 相談したいこと

1. principalness は hidden weighted scheme と public projection のどちらについて定式化するのが自然か。
2. substitution、ID renaming、subtype widening による一般性順序は妥当か。
3. 研究上の中心を principal inference、handler hygiene、effect-only contract のどこに置くべきか。

## Appendix A. 重い compiler canaries

### A.1 `twice`

`twice` は広い公開型が出る重要な例だが、初回資料の導入例としては型が重い。
そのため本文では `apply` を使い、`twice` は canary として残す。

```text
d2:twice: (('a | 'c) ['d] -> ['d & 'e] 'c & 'b) -> 'a -> ['e] 'b
```

### A.2 Standard library canaries

```text
std.control.var.ref.update:
  std::control::var::ref('a & 'c, 'b) -> ('b -> ['c] 'b) -> ['c, 'a] ()

std.text.parse.choice:
  (() -> ['g] 'a) -> ['g] (() -> ['f] 'a) -> ['f] () -> [std::text::parse::parse 'b 'c 'd 'e] 'a
  where 'c: std::text::parse::ParseError(item = 'h, pos = 'i)

std.control.flow.loop.for_in:
  'a -> ('c -> [std::control::flow::loop; 'b] any) -> ['b] ()
  where 'a: std::data::fold::Fold(item = 'c)
```

これらは public scheme に `#...` や `AllExcept(...)` の hidden stack evidence を出さず、
必要な residual row だけを残す canary である。

### A.3 `ref.update` private evidence leak

`std.control.var.ref.update` は、data-position に effectful function を持つ。

```text
update_effect: () -> [ref_update a; e] ()
```

この field の latent return-effect tail を public tail `e` へ直接つなぐと、public scheme 内に
`AllExcept(ref_update)` を持つ weighted self-alias が入り、bounds replay が無限に増殖しうる。

現在の実装では、data-position function の tail を private `kappa` として lower し、
ordinary residual だけを `kappa <: e` の projection で public tail へ戻す。

```text
field row internal: [ref_update a; PWeight(@ref[AllExcept(ref_update _)], kappa)]
projection:         kappa <: e
public surface:     ref(e & b, a) -> (a -> [b] a) -> [e, b] unit
```

この projection は `kappa = e` という型等式ではない。private evidence を public scheme へ輸出しないための
boundary operation である。

## Appendix B. Commands

```sh
timeout 120s cargo run -q -p yulang -- dump-poly-std \
  notes/research/consultation/examples/high_order_inference.yu \
  | rg '^d[0-9]+:(apply|twice|use_int):'

timeout 120s cargo run -q -p yulang -- dump-poly \
  notes/research/consultation/examples/local_sub_handler.yu \
  | rg 'sub.sub|sub.return|note.tell|use_int|use_str|use_residual'

timeout 120s cargo run -q -p yulang -- dump-poly-std-in \
  notes/research/consultation/examples/high_order_inference.yu std.control.var.ref \
  | rg 'std.control.var.ref.update'

timeout 120s cargo run -q -p yulang -- dump-poly-std-in \
  notes/research/consultation/examples/high_order_inference.yu std.text.parse \
  | rg '^pub .*"std.text.parse.choice"'

timeout 120s cargo run -q -p yulang -- dump-poly-std-in \
  notes/research/consultation/examples/high_order_inference.yu std.control.flow.loop \
  | rg '^pub .*"std.control.flow.loop.for_in"'
```

## Appendix C. References inside the repository

- `research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex`
- `docs/effect-inference-brief.md`
- `spec/2026-05-31-effect-variable-subtractable.md`
- `docs/infer-solver-invariants.md`
- `notes/diagnostics/2026-06-23-ref_update.md`
