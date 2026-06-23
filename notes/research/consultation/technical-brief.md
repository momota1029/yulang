# Yulang における高階型推論と effect-only annotation

Subtitle: Higher-order inference, polymorphic handlers, and hygienic effect subtraction

Status: draft for an initial research consultation, 2026-06-23.

## 1. Problem

Yulang は代数的エフェクトとハンドラを持つ実験的言語である。値型と effect row は subtype 制約として同時に推論される。

相談したい主張は、次の三つである。

- 具体的な値型や effect family 集合を省略した高階関数に、比較的一般的な公開型が付く。
- handler combinator は、返り値型と residual effect row に関して多相な型を持てる。
- annotation は値型を指定するためではなく、handler に見せてよい effect と、外へ残す residual を制限する effect-only contract として働く。

この資料では「注釈なし」という語を、単に annotation syntax が無いという意味では使わない。正確には、具体的な値型・effect family 集合を表面で省略し、内部で effect-only skeleton / wildcard slot を生成する、という意味で使う。

## 2. Current Compiler Output

出力は 2026-06-23 時点の `target/debug/yulang` からの抜粋である。右辺 IR は省略し、公開型の部分だけを載せる。

### 2.1 Higher-order Inference

Source: `notes/research/consultation/examples/high_order_inference.yu`

```yu
our apply f x = f x
our twice f x = f (f x)
our use_int = twice (\x -> x + 1) 20

use_int
```

Command:

```sh
timeout 180s target/debug/yulang dump-poly-std notes/research/consultation/examples/high_order_inference.yu \
  | rg '^d[0-9]+:(apply|twice|use_int):'
```

Observed public lines:

```text
d1:apply: ('a -> ['c] 'b) -> 'a -> ['c] 'b
d2:twice: (('a | 'c) ['d] -> ['d & 'e] 'c & 'b) -> 'a -> ['e] 'b
d3:use_int: int
```

`apply` は effectful function argument の latent effect `'c` を外へ残す。`twice` は現在の public surface がまだ専門的で、相談資料では「広い型が出る」例としては有用だが、導入例としては説明を要する。

### 2.2 Effect-only Handler Skeleton

Source: `notes/research/consultation/examples/local_sub_handler.yu`

```yu
pub act sub 'a:
  pub return: 'a -> never
  pub sub(x: [_] 'a): 'a = catch x:
    return a, _ -> a
    a -> a

our use_int = sub::sub:
  sub::return 0

use_int
```

Command:

```sh
timeout 120s target/debug/yulang dump-poly notes/research/consultation/examples/local_sub_handler.yu
```

Observed public lines:

```text
pub d2:"sub.sub": 'a [sub('c & 'a); 'b] -> ['b] 'a | 'c
pub d1:"sub.return": 'a -> [sub 'a] never
d3:use_int: int
```

ここで `[_] 'a` は値型を指定しない effect-only skeleton である。`sub.sub` は `sub` effect を処理し、残りの effect row `'b` を外へ戻す。

### 2.3 Standard-library Canaries

Command examples:

```sh
timeout 120s target/debug/yulang dump-poly-std-in notes/research/consultation/examples/high_order_inference.yu std.control.var.ref \
  | rg 'std.control.var.ref.update'

timeout 120s target/debug/yulang dump-poly-std-in notes/research/consultation/examples/high_order_inference.yu std.text.parse \
  | rg '^pub .*"std.text.parse.choice"'

timeout 120s target/debug/yulang dump-poly-std-in notes/research/consultation/examples/high_order_inference.yu std.control.flow.loop \
  | rg '^pub .*"std.control.flow.loop.for_in"'
```

Observed public signatures:

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

これらは public scheme に `#...` や `AllExcept(...)` の hidden stack evidence を出さず、必要な residual row だけを残す canary である。

## 3. Inference Mechanism

内部制約は、概略として次の形で扱う。

```text
surface term
  -> effect-only skeleton / annotation lowering
  -> weighted subtype constraints
  -> weighted row split
  -> saturation and compact extraction
  -> public scheme projection
```

制約は方向付き weight を持つ。

```text
T @L <: @R U
```

effect row upper bound は次の形で分割する。

```text
alpha @ L <: [K; beta]
J = K intersection Common(L)
alpha <: [J; gamma]
gamma @ (L minus J) <: beta
```

`Common(L)` は active boundary を通して handler から見える effect family の共通部分である。handler は `K` 全体ではなく `K intersection Common(L)` だけを処理できる。

stack evidence は handler hygiene と residual subtraction の内部証拠であり、public scheme には出さない。public surface では ordinary effect row として説明できる residual だけを表示する。

## 4. Ref.update as a Canary

`std.control.var.ref.update` は、data-position に effectful function を持つ。

```text
update_effect: () -> [ref_update a; e] ()
```

この field の latent return-effect tail を public tail `e` へ直接つなぐと、public scheme 内に `AllExcept(ref_update)` を持つ weighted self-alias が入り、bounds replay が無限に増殖しうる。

現在の実装では、data-position function の tail を private `kappa` として lower し、ordinary residual だけを `kappa <: e` の projection で public tail へ戻す。

```text
field row internal: [ref_update a; PWeight(@ref[AllExcept(ref_update _)], kappa)]
projection:         kappa <: e
public surface:     ref(e & b, a) -> (a -> [b] a) -> [e, b] unit
```

この projection は `kappa = e` という型等式ではない。private evidence を public scheme へ輸出しないための boundary operation である。

## 5. Theoretical Claims and Scope

現時点の形式化は、次の範囲を対象にしている。

- 完全 handler
- effect-only skeleton
- rank-1 let polymorphism
- monomorphic `let rec`
- finite effect family
- directed stack weight による effect subtraction
- colored handler soundness
- principal weighted scheme

範囲外または未整理のもの:

- polymorphic recursion
- 任意 constraint graph に対する無条件停止性
- public scheme projection 後にも同じ意味で principal と呼べるか
- same-boundary alias-cycle subsumption の完全な形式化
- local wildcard helper evidence の close / projection を、data-position function tail と同一概念として扱うべきか

## 6. Questions for Consultation

1. subtype と hidden weighted evidence を含む体系で、主型性は hidden weighted scheme と public scheme のどちらに対して述べるのが自然か。
2. `instance / substitution / subtype widening` による一般性順序は、既存の qualified typing や row-polymorphic effect system と比較して自然か。
3. effect-only annotation は partial type signature、bidirectional typing、capability annotation のどれに近いと説明すべきか。
4. handler combinator の多相性は、polymorphic resumption ではなく residual row polymorphism として述べるのが妥当か。
5. 停止性の議論では、exact seen key、self-tail no-op、residual hash-cons、same-boundary alias-cycle subsumption のどこを最も疑うべきか。
6. 論文化する場合、中心に置くべき主張は principal inference、handler hygiene、effect-only annotation のどれか。

## 7. References inside the Repository

- `research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex`
- `spec/2026-05-31-effect-variable-subtractable.md`
- `docs/infer-solver-invariants.md`
- `notes/diagnostics/2026-06-23-ref_update.md`
