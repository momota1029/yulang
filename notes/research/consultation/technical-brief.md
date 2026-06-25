# Yulang における effect capture contracts と handler hygiene

Subtitle: From algebraic effects examples to weighted constraints for higher-order inference.

Status: draft for an initial research consultation, 2026-06-24.

Compiler snippets below were collected on 2026-06-24 from implementation commit
`59198894`, unless otherwise noted. Right-hand IR is omitted from displayed
public type lines.

## 1. 最小例: algebraic effects and handlers

Yulang は、代数的エフェクトとハンドラに近い機構を持つ実験的言語である。
`act` は effect family とその operation を定義し、`catch` は operation を捕捉する。

次は `bool` を返す effect operation `flip::coin` と、それを全分岐探索として解釈する
handler である。

```yu
act flip:
    our coin: () -> bool

our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]

all_paths:
    my a = if flip::coin(): 1 else: 0
    my b = if flip::coin(): 10 else: 0
    my c = if flip::coin(): 100 else: 0
    a + b + c
```

`flip::coin()` は、通常の値を返す関数呼び出しのように書かれている。しかし、実際には
operation request を発生させ、近い handler に制御を渡す。`catch` の

```yu
flip::coin(), k -> all_paths(k true) + all_paths(k false)
```

という arm では、`k` が `coin` の発生地点から `action` の残りまでの限定継続である。
この handler は継続を `true` と `false` の両方で再開するので、上の計算は 3 回の
`coin` による 8 通りの分岐を列挙する。

この関数には、次の公開型が付く。

```text
all_paths : 'a [flip; 'b] -> ['b] list 'a
```

これは「`flip` を含む computation を受け取り、`flip` だけを処理し、残りの effect row
`'b` は呼出し側へ残す」という意味である。`notes/research/consultation/examples/nested_handler_contracts.yu`
での実際の compiler output は次の形である。

```text
d5:all_paths: 'a [flip; 'b] -> ['b] std::data::list::list 'a
```

ここで重要なのは、`all_paths` が `int` 専用の関数でも、pure な computation 専用の
関数でもないことである。返り値型 `'a` と residual effect row `'b` は一般化される。

## 2. 複数の handler を重ねる例

`all_paths` が `flip` だけを処理し、別の effect を残せることは、別の handler と重ねると
見えやすい。例えば、`flip` に加えて `amount::coin` という `int` を返す effect を用意する。

```yu
act flip:
    our coin: () -> bool

act amount:
    our coin: () -> int

our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]

our total_amount(action: [amount] _) =
    my loop(n, action: [amount] _) = catch action:
        amount::coin(), k -> loop(n, k n)
        v -> v
    [loop(1, action), loop(2, action)]

total_amount: all_paths:
    my a = if flip::coin(): amount::coin() else: 0
    my b = if flip::coin(): amount::coin() * 10 else: 0
    my c = if flip::coin(): amount::coin() * 100 else: 0
    a + b + c
```

この計算では、内側の `all_paths` が `flip` による 8 通りの分岐を列挙し、外側の
`total_amount` が `amount` を二つの解釈で処理する。`total_amount` も `all_paths` と同じく、
対象 effect だけを処理し、残りの row を外へ残す。

```text
d6:total_amount: 'a [amount; 'b] -> ['b] std::data::list::list 'a
```

現行 runtime での実行結果は次である。

```text
[[111, 11, 101, 1, 110, 10, 100, 0],
 [222, 22, 202, 2, 220, 20, 200, 0]]
```

この例は、handler が「名前の一致した operation を何でも消す」機構ではないことを示す。
各 handler は、自分の引数として受け取る computation に対して、どの effect を処理するかを
型注釈で契約する。

## 3. 衛生性: callback 由来の effect を偶然捕捉しない

次の例は、Yulang で `return` 風の control operator を user-defined effect として書いたものである。

```yu
pub act sub 'a:
    pub return: 'a -> never
    pub sub(x: [_] 'a): 'a = catch x:
        return a, _ -> a
        a -> a

our g h = sub::sub:
    h 0
    sub::return 1

sub::sub:
    g \i -> sub::return i
    sub::return 2
```

このプログラムの結果は `0` である。重要なのは、`g` の内部にも `sub::sub` があるにも
かかわらず、callback `h` から発生した `sub::return i` を `g` 内部の handler が偶然捕捉しない
ことである。

`g` は、渡された callback を ordinary callback として呼びたいだけであることが多い。
callback の実装がたまたま同じ `sub` effect family を使っていたとしても、それは `g` の
局所 handler が処理してよい effect とは限らない。この性質を、ここでは handler hygiene と呼ぶ。

この例は現行 runtime test として固定されている。

```text
control-vm::tests::runs_stack_handler_hygiene_to_outer_handler => [0]
```

## 4. 意図的に捕捉したい場合は contract を書く

では、operation を捕捉したいときはどう書くのか。それが `all_paths` の引数注釈である。

```yu
our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]
```

`action: [flip] _` は、具体的な返り値型を指定していない。ここで指定しているのは、
この handler boundary が `flip` を処理してよい、という局所的な effect capture contract である。

したがって、この注釈は単なる型推論補助ではない。普通の式や高階関数については、値型と effect
の導入・伝播を推論する。一方、handler が effect を局所化・消去する境界では、どの effect を
消去してよいかを明示的な contract として check する。

要約すると、Yulang の現在の設計は次の非対称性を持つ。

- effect introduction and propagation are inferred;
- effect elimination at handler boundaries is checked against explicit contracts.

## 5. なぜ ordinary effect rows だけでは足りないか

上の規律だけなら、「契約した effect だけを引く」と言えば済む。しかし、高階関数では
contract の有無だけでは情報が足りない。

典型例は関数合成である。

```yu
my compose f g x = f (g x)
```

`g x` が effect `h` を発生させるとき、`f` の内部にある `h` handler がその effect を
偶然捕捉してはならない。その effect は `f` の本体から発生したものではなく、`compose` の
呼出し側から渡された computation に由来するからである。

逆に、`f` に `g x` の residual effect を意図的に捕捉させたい場合は、`g` の戻り effect を
surface contract として明示する。例えば、前節の `total_amount` と `all_paths` を `compose`
で合成する canary では、第三引数を computation として渡す `x: [_] _` と、`g(x)` の residual
effect を `f` へ見せる `g: _ -> [_] _` の両方が必要になる。

しかし、ordinary effect row だけで公開型を書くと、次のような形になる。

```text
('a ['b] -> ['c] 'd) -> ('e -> ['b] 'a) -> 'e -> ['c] 'd
```

この型では、`g` の latent effect `'b` が `f` の引数計算として流れ込むことは表せる。
一方で、「`f` の内部 handler は、この `'b` を勝手に subtract してはいけない」という情報は
通常の row 変数だけでは表せない。

内部 scheme では、この差を weighted occurrence として持つ。現在の実装で使っている表記を
概略化すると、次のような情報が必要になる。

```text
('a ['b#0[Empty]] -> ['c] 'd) -> ('e -> ['b#0[Empty]] 'a) -> 'e -> ['c#0] 'd#0
```

ここで `#0[Empty]` は、ある handler boundary `#0` を通るときに、この occurrence からは何も
subtract できないことを表す内部証拠である。`#0` が付いた return-side occurrence は、その
boundary を抜けたあとで制約を対応づけるための証拠である。

現行 compiler dump では、`#... [Empty]` は hygiene を説明する証拠として public scheme 表示に
残り得る。一方で、利用者に見せたい通常の API 型としては ordinary effect row への projection も
考えられる。研究相談として判断したいのは、この weighted scheme と public projection のどちらに
principalness を述べるべきか、またその関係をどう定式化すべきかである。

## 6. Weighted subtype constraints

Yulang の推論器は、値型と effect row を subtyping 制約として同時に扱う。ここで Simple-sub
系の制約解決を使うのは、effect row の包含・残差・値型の上下界を同じ constraint graph で
処理したいためである。

handler hygiene のために、subtype constraint には weight を付ける。

```text
T @L <: @R U
```

effect row upper bound は、左側 weight を通して可視な family だけで分割する。概略的には
次の規則である。

```text
alpha @L <: [K; beta]
J = K ∩ Common(L)
```

ここで `K` は upper row の head 集合、`Common(L)` は weight `L` を通して handler boundary
から見える effect family の共通部分である。handler が実際に除去できるのは `K` 全体ではなく
`J` だけである。`J` が非空なら、制約は次のように分解される。

```text
alpha <: [J; gamma]
gamma @(L - J) <: beta
```

この weight は runtime marker ではなく、型制約上で effect の由来と handler boundary を運ぶ
証拠である。ordinary public type へ射影するときは、利用者に見せるべき residual row だけを残し、
handler hygiene のための stack evidence は隠す。

内部制約の流れは概略として次である。

```text
surface term
  -> skeleton / annotation lowering
  -> weighted subtype constraints
  -> weighted row split
  -> saturation and compact extraction
  -> public scheme projection
```

## 7. 形式化の範囲と相談事項

現時点の中核言語の形式化は、次の範囲を対象にしている。

- fully shallow handlers
- effect capture contracts / effect-only skeletons
- rank-1 let polymorphism
- monomorphic `let rec`
- finite effect families
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

相談したいことは、初回相談では次の三点に絞りたい。

1. principalness は hidden weighted scheme と public projection のどちらについて定式化するのが自然か。
2. substitution、ID renaming、subtype widening による一般性順序は妥当か。
3. 研究上の中心を principal inference、handler hygiene、effect capture contracts のどこに置くべきか。

## Appendix A. Compiler canaries

### A.1 `apply` and `twice`

Source: `notes/research/consultation/examples/high_order_inference.yu`

```yu
our apply f x = f x
our twice f x = f (f x)
our use_int = twice (\x -> x + 1) 20

use_int
```

Compiler output:

```text
d1:apply: ('a -> ['b] 'c) -> 'a -> ['b] 'c
d2:twice: (('a | 'b) ['c#0[Empty]] -> ['c#0[Empty] & 'd#0[Empty]] 'b & 'e) -> 'a -> ['d] 'e#0
d3:use_int: int
```

`apply` は、関数引数の latent effect が呼出し側へそのまま伝播する最小例である。
`twice` は広い公開型が出る重要な canary だが、導入例としては重いので本文からは外した。

### A.2 Standard library canaries

```text
std.control.var.ref.update:
  std::control::var::ref('a & 'b, 'c) -> ('c -> ['b] 'c) -> ['b, 'a] ()

std.text.parse.choice:
  (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> () -> [std::text::parse::parse 'a 'b 'c 'd] 'e
  where 'b: std::text::parse::ParseError(item = 'f, pos = 'g)

std.control.flow.loop.for_in:
  'a -> ('b -> [std::control::flow::loop; 'c] any) -> ['c] ()
  where 'a: std::data::fold::Fold(item = 'b)
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
timeout 120s cargo run -q -p yulang -- run-control-std \
  notes/research/consultation/examples/nested_handler_contracts.yu

timeout 120s cargo run -q -p yulang -- dump-poly-std \
  notes/research/consultation/examples/nested_handler_contracts.yu \
  | rg 'all_paths|total_amount|flip.coin|amount.coin'

timeout 120s cargo test -q -p control-vm runs_stack_handler_hygiene_to_outer_handler -- --test-threads=1

timeout 120s cargo run -q -p yulang -- dump-poly-std-in \
  notes/research/consultation/examples/high_order_inference.yu std.core \
  | rg 'std.core.compose'

timeout 120s cargo run -q -p yulang -- dump-poly-std \
  notes/research/consultation/examples/high_order_inference.yu \
  | rg '^d[0-9]+:(apply|twice|use_int):'

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
