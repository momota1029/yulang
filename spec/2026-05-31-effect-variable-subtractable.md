# effect subtraction（directed stack weight）

日付: 2026-05-31 初版、2026-06-22 全面改訂
状態: infer / poly の effect subtraction 中核仕様
対象: stack 重み付き subtype 制約、effect row subtraction、annotation lowering、cleanup

この文書は、handler hygiene を subtype solver 内の **directed stack weight** として扱う規則を定める。
2026-06-22 の directed stack weight proof 以降は、旧版の `protect` constructor 読みを正式な中核規則としては使わない。

実装上、`poly::types::StackWeight` には互換用の `floor` / `filter` 表現が残る。
ただし colored soundness 側の solver 意味論は、左重みと右重みを分けた directed 表現で説明する。
`floor` は row split や liveness の active family ではない。
停止性の論考では row-only core の ambient residual budget / residual floor が別に現れるが、
それは runtime marker や active family ではなく、exact worklist 停止性を論じるための静的な測度である。

## 前提

Yulang の型体系では次を混同しない。

- `Any` は Top 型である。
- `Never` は Bottom 型である。
- `Unknown` だけが未解決 placeholder である。

effect subtraction が失敗したり residual が残ったりしても、`Any` や `Never` を fallback として入れてはならない。
未解決を表す必要がある場合は `Unknown`、または通常の type / effect row 変数を使う。

## 目的

`catch` は、内側の computation が起こす effect row から handler が処理する family を取り除く。
しかし高階値をまたぐ場合、単純に row から family を引くだけでは handler hygiene が壊れる。

例として、ある関数が呼び出し元由来の computation を受け取り、その内部で別の handler を使う場合を考える。
内側 handler は、自分の lexical body で発生した effect を処理してよいが、呼び出し元が持ち込んだ effect を勝手に捕まえてはならない。

この「どの handler 境界がどの effect family を消費してよいか」を、型に貼り付く内部 wrapper と subtype edge の重みで表す。

```text
stack(T, @S)
T @L <: @R U
```

`stack(T, @S)` は source language の型構文ではない。
solver が annotation / handler / higher-order boundary の情報を運ぶための内部表現である。

## Directed weight

subtype 制約は、左重み `L` と右重み `R` の組を持つ。

```text
T @L <: @R U
```

左重みと右重みは同じ構造ではない。

```text
Left  L : Id -> pop^m take(F)^n
Right R : Id -> pop^m
```

- 左重みは、先行する unmatched pop と active push を持つ。
- active push は `take(F)` と読む。`F` は effect family 集合である。
- 右重みは pure pop だけを持つ。push / family / filter / floor を右側へ保存しない。
- 1 つの id について、正規形は `pop^m take(F)^n` である。
- `take(F); pop` は cancel するが、`pop; take(F)` は cancel しない。
- 別 id は count abstraction 上で可換だが、同じ id の順序は正規形に残る。

実装名との対応:

- `LeftStackWeightEntry { id, leading_pops, family, pushes }`
- `LeftStackWeight`
- `RightStackWeight`
- `ConstraintWeights { left: LeftConstraintWeight, right: RightStackWeight }`

`LeftConstraintWeight` は、directed left weight に一時的な filter check を添える solver 境界の型である。
filter は directed weight 本体ではない。

## Weight composition

同じ id の count は、次の順序付き列として合成する。

```text
pop^m take^n ; pop^p take^q
```

右側の pop は、左側の末尾にある take だけを消せる。

```text
if p <= n:
  pop^m take^(n - p + q)

if p > n:
  pop^(m + p - n) take^q
```

`take; pop` が消えるのは、pop がその take より後に現れるからである。
`pop; take` は「まだ対応する境界を越えていない pop」の後に push が現れる形なので消えない。

左右をまたぐ replay では、まず path の順序で左重みと右重みを合成し、その後に W-Mix を行う。

```text
mix(L, R):
  compose L followed by R per id
  active take が残る成分は left へ戻す
  pure pop だけが残る成分は right へ戻す
```

W-Mix は directed projection であり、意味論側の正規化である。
実装も W-Mix 後の exact label を replay queue に使い、`compose_for_replay` では pop/take count を丸めない。
spec / docs / テスト期待値で `pop(n) = pop(1)` のように説明してはならない。
論考上の W-Mix は、mixed comparison を active-left obligation と pure-right obligation の二本へ分ける規則である。
実装がこれを pair の正規化として持つ場合も、意味はこの二つの obligation を同時に保つこととして読む。

## Variance

関数引数や contravariant な型引数へ入ると、左右の重みは入れ替わる。

```text
(A1 -> B1) <: (A2 -> B2)

argument: A2 @swap(L,R) <: @swap(R,L) A1
result:   B1 @L <: @R B2
```

実装では `ConstraintWeights::swapped()` がこの境界を表す。
右重みは pure pop しか保存しないため、swap 後に右側から左側へ戻る成分も pure pop として materialize する。

## `stack(T, @S)` wrapper

`stack` wrapper は、型構造を降りるときに edge の重みへ移す。

```text
stack(T, S) @L <: @R U
=> T @(S + L) <: @R U

T @L <: @R stack(U, S)
=> T @L <: @(S + R) U
```

ただし directed solver に保存される形は次の制限を持つ。

- 左側へ入る wrapper は `take(F)` / pop / filter check を表せる。
- 右側へ保存される wrapper は pure pop だけである。
- 右側で見つかった filter は check として処理し、保存しない。
- legacy `floor` は active push ではないので、directed left weight へ入れない。

`int` や `bool` のような terminal concrete 型では、重みは観測されない。
関数、tuple、record、row、type argument では、深い effect row へ届く可能性があるため重みを流す。

## Row upper bound

weighted effect row upper bound の中核規則は次である。

```text
alpha @L <: @R [K; beta]
```

ここで `K` は upper row の head family 集合、`beta` は tail である。
`L` と `R` がどちらも空なら、これは普通の open row subtype 制約であり、subtraction budget を新しく作らない。

右 pop は row constructor の head を変えず、tail へ分配する。
したがって split は次の形へ直してから、左重みだけで考える。

```text
alpha @L <: [K; NWeight(R, beta)]
```

このとき row head から消費してよいのは左重みの active push だけで決まる。
右重みは row head を広げない。

```text
J = K ∩ Common(L)
```

`Common(L)` は、`L` に残る active push family の交差である。
active push が空なら、空交差として `All` と読む。
legacy `floor`、pure pop、right pop、filter は `Common(L)` に参加しない。

`J` が空でなければ、solver は次を作る。

```text
alpha <: [J; gamma]
gamma @(L - J) <: NWeight(R, beta)
```

`L - J` は active push family から `J` を引いた左重みである。
right pop は head 消費には使わず、tail 側へそのまま運ぶ。
tail 側の comparison が後で他の構造へ進むときは、通常の wrapper absorption / W-Mix 規則へ戻る。

`J` が空なら、新しい residual は作らない。
制約は tail へ進む。

```text
alpha @L <: NWeight(R, beta)
```

同じ row split から無限に fresh tail を作らないため、residual 変数は hash-cons する。
key は次である。

```text
(source, J, L - J)
```

target tail は key に含めない。
同じ source と同じ消費集合と同じ残差左重みなら、同じ `gamma` を再利用する。

自己 tail split:

```text
beta @L <: [K; beta]
```

この形は、right pop が空なら有限 colored observation では no-op とする。
row cycle を止めるために新しい保護集合を足してはならない。

## Filter

filter は covariant concrete effect annotation の static check である。
directed weight の active family ではなく、runtime marker でもない。

```text
filter(A)
```

- `filter(All)` は no-op である。
- `filter(Empty)` は concrete effect が外へ出ることを許さない。
- `filter(Set(...))` は concrete effect family が annotation に含まれることを検査する。
- family path が一致した場合、type argument は捨てずに invariant 制約を作る。
- check 後の filter は storage / replay / residual propagation から消える。

bound insertion では、左 filter を次のように扱う。

- lower bound 追加時は、incoming lower type をその場で検査し、filter を消してから保存する。
- upper bound / var-var bound 追加時は、source または lower variable に filter を登録し、後から来る lower bound を同じ経路で検査する。
- replay と compact は、すでに check 済みの filter を見ない。

`Neg::Stack` 側で filter が現れた場合も、filter は check として処理してから消す。
右重みに filter を保存してはならない。

## Protect

`protect` は独立した constructor ではない。
fresh internal effect variable や、handler に消費されてはならない residual を守る場合は、左重みとして次を使う。

```text
take(Empty)
```

`take(Empty)` は `Common(L)` を `Empty` へ絞るため、row head を何も消費できない。
これで「この residual からは handler が引けない」という性質を表す。

この目的で、rigid variable set、blocked pair set、through flag、exposed boundary vars のような別の保護機構を追加してはならない。
保護したい変数集合を作って共起分析や極性消去を止める実装は、この仕様ではない。

## Annotation lowering

effect annotation は、公開型を読むための情報であると同時に、higher-order boundary で何を handler に見せてよいかを決める。

基本方針:

- covariant concrete row annotation は filter check になる。
- contravariant concrete row annotation は `take(H)` になる。
- contravariant wildcard `[_]` は `take(All)` になる。
- effect-only skeleton の省略 slot は wildcard と同じであり、反変位置では `take(All)`、共変位置では裸の row variable になる。
- fresh internal effect variable のうち、外側 handler に消費させてはいけないものは `take(Empty)` で protect する。
- covariant wildcard / 省略 slot は filter wrapper を作らない。

例:

```text
x : [io] A
```

`x` が contravariant な computation 引数なら、`io` は caller-supplied computation を内側 handler に見せてよい予算として `take(io)` になる。
返り値や公開 result row のような covariant 位置なら、`io` は外へ出てよい family の filter になる。

不変位置では、上下に同じ annotation を雑に複製しない。
role-system の不変区間規則と同じく、実引数が同じ中心を満たすことを ordinary constraint で表す。

## Family arguments

effect family は path だけで突き合わせない。
同じ path の family が set operation で出会った場合、type argument は invariant に制約する。

対象:

- row split の `K ∩ Common(L)`
- residual subtraction の `L - J`
- duplicate row head collection
- filter check
- `Neg::Stack` common-stack check

例:

```text
ref_update int
ref_update alpha
```

この 2 つが同じ family として扱われる場合、`int` と `alpha` の間にも invariant 制約を作る。
path が同じだからといって payload を捨てない。

## Bound replay

type variable の bounds は、型と directed weight の組として保存する。

```text
lower: (Pos, L, R)
upper: (Neg, L, R)
```

replay では経路に沿って左重みと右重みを合成し、W-Mix で directed projection してから enqueue する。

```text
compose_for_replay:
  left  = earlier.left ; later.left
  right = later.right ; earlier.right
  normalize_directed_mix()
```

var-var replay も同じく W-Mix だけで canonical exact full label を作り、
通常の `SubtypeConstraint { lower, upper, weights }` の queue path へ戻す。
var-var 専用の direct replay 経路や、`compose_for_replay` で pop count を丸める規則は使わない。

ただし var-var bound を保存するときは、同一 endpoint pair / 同一 static subtract id / 同一 family の
alias replay cycle を既存 bound で subsume する。これは型等式ではない。同じ annotation / boundary
site を表す `SubtractId` が worklist cycle で再訪されたことだけを止める保存規則であり、
別 `SubtractId` や別 family は区別する。

unmatched right pop を新しい push と交換してはならない。
右重みは pure pop として tail / variance / replay を通る。

## 停止性論考との関係

`research/effect-mini-language/directed_weight_row_solver_termination_ja.tex` は、値型や constructor 分解を外した
row-only core の停止性を扱う別論考である。
そこでは exact natural-number counter を保つ solver の無条件停止性が偽であることを示し、
cycle-neutrality、exact cache、residual memoization、有限 capability algebra の下で停止性を述べる。

この停止性論考に出る ambient residual budget / residual floor は、ordinary row の二重消費を測るための静的な残量である。
colored soundness 側の `Common(L)` に参加する active push ではなく、runtime marker でもない。
実装は `compose_for_replay` で pop count を丸めず、source-generated graph 側の cycle-neutrality と
exact cache / residual memoization を停止性の前提として扱う。型/row の意味論から外れた実装上の
same-boundary alias cycle は、var-var bounds 保存時の subsumption で止める。
したがって、停止性のための floor や別 key を row head subtraction の visibility 規則へ混ぜてはならない。

## Compact / finalize

compact extraction では、directed weight を polarity に応じて投影する。

- positive occurrence は left weight を `PWeight(L, T)` として見る。
- negative occurrence は right pop を `NWeight(R, T)` として見る。
- filter はすでに check 済みなので principal 型へ出さない。
- legacy `floor` は active push ではない。

cleanup の liveness は、covariant active push だけから stack id を集める。
bare `floor` や pure pop だけでは id を live にしない。

公開型に residual row variable が残ることは正常である。
例えば次のような表示の `; beta` は、handler が消費しなかった effect tail を表す principal な残差であり、出力を短くする目的で消してはならない。

```text
alpha [undet; beta] -> [beta] alpha
```

## Runtime との関係

inference の directed weight は、どの handler 境界がどの effect family を消費してよいかを決める。
specialize 後は、runtime guard marker が同じ hygiene を保つ。

ただし filter は runtime marker ではない。
filter は annotation check を solver 内で済ませ、runtime へは運ばない。

runtime marker の規則は `spec/2026-06-13-runtime-guard-markers.md` を見る。

## 手計算

この節は規則そのものではなく、規則がどう動くかを確認するための worked examples である。
旧版の手計算は `floor` と `common_stack(W)` を前提にしていたが、ここでは directed left/right weight で書き直す。

### 記法

空の左重みを `0L`、空の右重みを `0R` と書く。
id `u` の active push `take(H)` を次のように略記する。

```text
@u[H] = { u -> pop^0 take(H)^1 }
```

消費後に family が狭まったものは `@u[H - J]` と書く。
たとえば `@h[All] - handled` は `@h[AllExcept(handled)]` である。
`H - J = Empty` なら `@h[Empty]` と書き、これは active push ではあるが何も消費させない。

右重みが tail に残る場合は、論考の記法に合わせて `NWeight(R, beta)` と書く。
`R=0R` のときは `NWeight(0R, beta)` を単に `beta` と略す。

row split は常に次の形で読む。

```text
alpha @L <: @R [K; beta]
=> alpha @L <: [K; NWeight(R, beta)]

J = K ∩ Common(L)

if J = Empty:
  alpha @L <: NWeight(R, beta)

if J != Empty:
  alpha <: [J; gamma]
  gamma @(L - J) <: NWeight(R, beta)
```

residual `gamma` は `(source, J, L - J)` で hash-cons する。
同じ source、同じ消費 head、同じ residual left weight なら同じ `gamma` を再利用する。

### 基本例

protected row:

```text
alpha @ @u[Empty] <: [io; beta]
J = io ∩ Empty = Empty
=> alpha @ @u[Empty] <: beta
```

`take(Empty)` は active push なので `Common` を `Empty` にする。
したがって handler はこの row から何も消費できない。

許可された subtraction:

```text
alpha @ @u[G] <: [H; beta]
J = H ∩ G
```

`J` が空でなければ次になる。

```text
alpha <: [J; gamma]
gamma @ @u[G - J] <: beta
```

複数 id:

```text
alpha @ @u[G] @ @v[H] <: [K; beta]
Common = G ∩ H
J = K ∩ G ∩ H
```

全 active id が同時に許す family だけを元 row から一度だけ引く。
`L - J` では、各 active id の family から同じ `J` を引く。
これは push ごとに別々の row head を引くという意味ではない。

right pop:

```text
alpha @L <: @R [K; beta]
=> alpha @L <: [K; NWeight(R, beta)]
```

right pop は row head を見せない。
`K` から消費できるのは `K ∩ Common(L)` だけであり、`R` は residual tail の `NWeight` として残る。

self-tail:

```text
beta @L <: [K; beta]
```

これは新しい residual を立てても同じ `beta` へ戻るだけなので no-op とする。
step-indexed colored observation では有限な head 情報を増やさず、residual hash-cons と合わせて self-fueling を止める。

pop の分配:

```text
A -> B <: pop_u(C)
C <: D -> E
```

右 pop を constructor へ分配すると次の比較になる。

```text
A -> B <: pop_u(D) -> pop_u(E)
```

function domain は反変なので、分解後は次になる。

```text
pop_u(D) <: A
B <: pop_u(E)
```

pop が勝手に辺を移るのではなく、function domain の反変分解で左右が交換された結果である。

### annotation lowering の小例

effect-only skeleton の slot は極性で意味が変わる。

```text
contravariant [_]       => PWeight(@u[All], rho)
contravariant [io]      => PWeight(@u[io], rho)
contravariant []        => PWeight(@u[Empty], rho)
covariant omitted / [_] => rho
covariant [io]          => Filter(io, rho)
covariant []            => Filter(Empty, rho)
```

省略 slot は「予算なし」ではない。
effect-only skeleton では wildcard と同じであり、反変なら `take(All)`、共変なら filter なしの open row になる。

fresh internal effect variable のうち、外側 handler に消費させてはいけないものだけを
`PWeight(@u[Empty], rho)` として protect する。

### shallow と recursive/deep の期待型が分岐する理由

ここでは、handler variant の枝 effect がどう catch 全体へ流れるかだけを比較する。
scrutinee の effect row を次のように置く。

```text
x : [PWeight(@h[All], alpha)] value
```

handler が `handled` を処理するので、まず次を要求する。

```text
alpha @ @h[All] <: [handled; rho]
J = handled ∩ All = handled
```

したがって split は次になる。

```text
alpha <: [handled; gamma]
gamma @ @h[AllExcept(handled)] <: rho
```

`@h[AllExcept(handled)]` は、同じ handler 寿命の residual が `handled` をもう一度消費しないための
colored evidence である。
公開型にはこの weight 自体は出ず、residual row だけが残る。

shallow variant では、operation branch が scrutinee effect をそのまま再び起こしうると見る。
catch 全体の effect を `delta` とすると、枝と residual から次が流れる。

```text
alpha <: delta
rho   <: delta
```

一旦の形は次である。

```text
value [alpha] -> [delta] value
constraints:
  alpha <: [handled; gamma]
  gamma @ @h[AllExcept(handled)] <: rho
  alpha <: delta
  rho <: delta
```

compact では、`alpha` が引数側にも枝 effect 側にも出るため、residual と同じ成分へ畳まれる。
hidden weight を除くと、期待する公開型は次の形になる。

```text
value [alpha & [handled; alpha]] -> [alpha] value
```

recursive/deep variant では、operation branch が continuation を handler 自身へ投げ返すだけで、
scrutinee effect `alpha` を catch 全体の枝 effect へ直接流さない。
生じるのは次だけである。

```text
rho <: delta
```

一旦の形は次である。

```text
value [alpha] -> [delta] value
constraints:
  alpha <: [handled; gamma]
  gamma @ @h[AllExcept(handled)] <: rho
  rho <: delta
```

`alpha` は反変側にしか残らず、`delta` は共変側だけなので、極性消去後に落ちる。
公開型は次の形になる。

```text
value [handled; gamma] -> [gamma] value
```

枝が足りない incomplete handler では、未処理の scrutinee effect も catch 全体 effect へ流す。
その場合は shallow と同じく `alpha <: delta` が残るため、recursive/deep でも shallow 側の形へ近づく。

### `outer/local/repeat` の衛生性

次のような形を考える。

```yu
act outer:
    our redo: () -> never
    my act local:
        our break: () -> never
        our judge(x: [_] _) = catch x:
            break(), _ -> true
            _ -> false
        our sub(x: [_] _) = catch x:
            break(), _ -> ()
            _ -> ()
        my act repeat = local
        our run(f: () -> [outer] _) = local::sub: loop true with:
            our loop b = if b:
                loop:repeat::judge:catch f():
                    redo(), _ -> repeat::break()
                    _ -> local::break()

pub r = outer::run
```

単相化した状態で、次が既に分かっているとする。

```text
repeat::judge : unit [repeat; eps] -> [eps] bool
local::sub    : unit [local; zeta] -> [zeta] unit
```

`run` の引数 annotation `f: () -> [outer] _` は、`run` から見ると反変 slot にある。
したがって `f()` の effect は次の形で置かれる。

```text
f : () -> [PWeight(@run[outer], alpha)] value
```

`catch f()` が `outer` を処理する。

```text
alpha @ @run[outer] <: [outer; rho]
J = outer ∩ outer = outer
```

split:

```text
alpha <: [outer; gamma]
gamma @ @run[Empty] <: rho
```

`@run[Empty]` は「`f` 由来 residual からは、この内側 handler 群がもう何も引けない」という evidence である。

catch の枝では `repeat::break`、`local::break`、未処理 residual が catch 全体 effect `delta` へ流れる。

```text
repeat <: delta
local  <: delta
rho    <: delta
```

`repeat::judge` へ渡すので、`delta <: [repeat; eps]` が必要になる。
下界を一つずつ流す。

```text
repeat <: [repeat; eps]
=> unit row tail eps

local <: [repeat; eps]
=> local <: eps

rho <: [repeat; eps]
```

`rho` には `gamma @ @run[Empty] <: rho` があるので、推移で次も処理する。

```text
gamma @ @run[Empty] <: [repeat; eps]
J = repeat ∩ Empty = Empty
=> gamma @ @run[Empty] <: eps
```

`repeat` は消費されたが、`local` と `gamma@run[Empty]` は `eps` 側へ残る。

次に `local::sub` へ渡すので、`eps <: [local; zeta]` を処理する。
`eps` の下界から見ると次になる。

```text
local <: [local; zeta]
=> unit row tail zeta

gamma @ @run[Empty] <: [local; zeta]
J = local ∩ Empty = Empty
=> gamma @ @run[Empty] <: zeta
```

つまり、`outer` 由来の residual は `repeat` handler にも `local` handler にも捕まらない。
最終的な型は hidden weight を消すと次へ畳まる。

```text
(() -> [outer; gamma] value) -> [gamma] unit
```

ここで `repeat` は `local` と同じ実体に見えても、`outer` の producer-consumer 境界で作った
`@run[Empty]` が residual に残るため、内側 handler が呼び出し元由来の effect を奪わない。

### `m` / `j` が巡回を生まない理由

次を考える。

```yu
act io:
    our read: () -> int

my j(x: [_] _) = catch x:
    io::read(), k -> j(k 0)

my m(x: [io; e] _) = catch x:
    io::read(), k -> j(k 0)
```

`j` は次の型を持つとする。

```text
j : a [io; b] -> [b] a
```

`m` の引数 `x: [io; e] _` は反変 concrete annotation なので、scrutinee effect を次の形で置く。

```text
x : [PWeight(@m[io], gamma)] delta
```

`m` の catch が `io` を処理する。

```text
gamma @ @m[io] <: [io; eps0]
J = io ∩ io = io
```

split:

```text
gamma <: [io; eps]
eps @ @m[Empty] <: eps0
```

枝の中で `k 0` を作り、それを `j` へ渡す。
`j` の引数 effect に合わせるため、再び次が要求される。

```text
gamma @ @m[io] <: [io; b]
```

ここでも

```text
J = io
L - J = @m[Empty]
```

であり、residual key は最初の split と同じ `(gamma, io, @m[Empty])` になる。
したがって fresh residual をもう一つ作らず、同じ `eps` を再利用する。

```text
gamma <: [io; eps]
eps @ @m[Empty] <: b
```

枝 effect は `b`、catch residual は `eps0` なので、catch 全体 effect `zeta` には次が入る。

```text
b    <: zeta
eps0 <: zeta
```

公開型では、`eps @ @m[Empty]` の hidden evidence は表示されず、`j` と同じ主形へ戻る。

```text
a [io; b] -> [b] a
```

重要なのは、2 回目の `gamma @ @m[io] <: [io; ...]` が新しい residual tail を作らない点である。
同じ split slot が同じ `eps` を返すため、`gamma -> eps -> gamma` のような row cycle は発生しない。

### `AllExcept(ref_update _)` と `ref::update`

次のような型を考える。

```yu
pub act ref_update 'a:
    pub update: 'a -> 'a

pub type ref 'e 'a with:
    struct self:
        get: () -> ['e] 'a
        update_effect: () -> [ref_update 'a; 'e] ()
    pub r.update f =
        my loop(x: [_] _) = catch x:
            ref_update::update v, k -> loop:k:f v
        loop:r.update_effect()
```

`ref 'e 'a` の residual `'e` は、`ref_update _` 以外を通す residual として読む。
内部 evidence は次の形で置く。

```text
@ref = @ref_id[AllExcept(ref_update _)]
```

`loop` の引数 `x: [_] _` は反変 wildcard なので、scrutinee effect は次になる。

```text
x : [PWeight(@loop[All], row4)] value5
```

`loop` の catch が `ref_update` を処理する。

```text
row4 @ @loop[All] <: [ref_update t6; tail7]
J = ref_update t6 ∩ All = ref_update t6
```

split:

```text
row4 <: [ref_update t6; row7]
row7 @ @loop[AllExcept(ref_update t6)] <: tail7
```

operation pattern から、payload と continuation には通常の型制約が入る。
ここでは effect の流れだけを見る。

handler arm の `f v` では、`f` の返り effect annotation が無い。
これは外側 handler に勝手に消費させてはいけない internal effect なので、fresh row `row10` を
`@fv[Empty]` で protect する。

```text
f : t8 -> [PWeight(@fv[Empty], row10)] t11
```

`k (f v)` のために continuation の期待 effect と突き合わせると、`row10` は `row4` 側へ流れる。
`row4` には既に `[ref_update t6; row7]` という upper があるので、推移で次が生じる。

```text
row10 @ @fv[Empty] <: [ref_update t6; row7]
J = ref_update t6 ∩ Empty = Empty
```

したがって `ref_update` はここでは消費されない。
新しい residual も作らず、tail 側へ進む。

```text
row10 @ @fv[Empty] <: row7
```

これが「`f v` が起こす effect は、`loop` の `ref_update` handler に奪われず、loop の residual へ残る」
という部分である。

`loop` の主な effect 形は、hidden evidence を消すと次になる。

```text
value [ref_update item; row7] -> [row10; row7] value
```

ここへ `r.update_effect()` を渡す。
`r.update_effect()` の effect は次である。

```text
[ref_update a; PWeight(@ref[AllExcept(ref_update _)], e)] unit
```

関数適用で argument row を合わせると、具体 head `ref_update a` は `loop` が処理する head と一致し、
payload `a` と `item` の間に invariant 制約が入る。
残った ref residual は次のように `row7` へ流れる。

```text
e @ @ref[AllExcept(ref_update _)] <: row7
```

返り effect は `row10` と `row7` から来る。
`row7` には `e@ref` が流れ、`row10` には `f v` の effect が流れる。
hidden evidence を消し、共起する residual を `b` と置くと、最終的な公開型は次の形になる。

```text
ref (e & b) a -> (a -> [b] a) -> [e; b] unit
```

旧手計算の名前に合わせれば、これは次の形である。

```text
forall a b c. ref (a & b) c -> (c -> [b] c) -> [a; b] unit
```

ポイントは 2 つである。

- `@loop[All]` は `ref_update` を一度だけ処理し、residual は `@loop[AllExcept(ref_update)]` へ狭まる。
- `@fv[Empty]` と `@ref[AllExcept(ref_update _)]` は、内側の `ref_update` handler が別由来の residual を消費することを防ぐ。

### 変数展開と one-layer compact

変数展開は、裸の変数ではなく weighted occurrence に対して行う。
positive occurrence なら parent left weight を direct lower bound へ合成し、negative occurrence なら parent right weight を direct upper bound へ合成する。
そのあと polarity に応じて `PWeight` / `NWeight` へ投影する。

重要なのは、展開して出てきた変数を同じ pass でさらに展開しないことである。
これは subtype graph の推移閉包を表示処理でもう一度作らないための制限である。

例として、compact 前に次の upper bounds があるとする。

```text
beta upper includes eps
beta upper includes [undet; zeta]
eps  upper includes [io; eta]
zeta upper includes [flip; gamma]
```

`alpha [beta] -> [gamma] delta` の引数 row を one-layer に展開すると、まず direct upper だけを見る。

```text
alpha [beta & eps & [undet; zeta]] -> [gamma] delta
```

`eps` は `beta` の direct upper として出てきた変数なので、この pass では `[io; eta]` へさらに開かない。
一方、row constructor `[undet; zeta]` の tail として構造上見えている `zeta` は、その row の中で必要な一段だけ見る。

```text
alpha [beta & eps & [undet; zeta & [flip; gamma]]] -> [gamma] delta
```

極性消去後、反変側だけに残る不要成分は落ち、次のような principal な surface に近づく。

```text
alpha [undet; [flip; gamma]] -> [gamma] delta
```

この制限により、compact 表示は飽和済み graph の direct bounds を読むだけになり、
表示側で新しい伝播や無限展開を起こさない。

## 実装上の禁止事項

- 左右重みを row split 前に `left.compose(right)` のように単一 weight へ潰さない。
- row head の消費判定に right pop、filter、legacy floor を参加させない。
- `floor` を formal core の保護機構として復活させない。
- `protect` 専用 constructor や protected variable set を足さない。
- residual key に target tail を含めない。
- `filter` を runtime marker として扱わない。
- `pop(n) -> pop(1)` を型等式として説明しない。
- same-boundary alias cycle の bounds subsumption を、surface type の簡約規則として説明しない。
- family path だけを比較して type argument を捨てない。
- `Any` を曖昧な fallback、`Never` を placeholder として使わない。
- 特定の path / module / fixture 名だけを見る inference 分岐を足さない。

## 実装対応表

- directed weight: `crates/infer/src/constraints/directed_weight.rs`
- weighted row split: `crates/infer/src/constraints/row_effect.rs`
- bound storage / replay: `crates/infer/src/constraints/machine/*`
- cleanup / stack id liveness: `crates/infer/src/generalize/*`
- surface materialization: `crates/infer/src/generalize/finalize.rs`, `crates/poly/src/dump/*`
- runtime marker: `crates/control-vm`, `crates/mono-runtime`, `spec/2026-06-13-runtime-guard-markers.md`
