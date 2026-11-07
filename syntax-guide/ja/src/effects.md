# effect と handler

effect は、「計算が外に頼むこと」を、型に載せて扱う仕組み。`act` で effect を宣言し、`catch` で handler を書いて、頼まれたことを処理する。
この章は書き方と読まれ方を見る。意味(行の引き算、衛生性、型の規則)は spec の章5 と、その先の核の計算体系に任せる。

## `act` と operation

```yulang
act flip:
    our coin: () -> bool

my bit = flip::coin()
```

- `act` は、effect の family を作る。同名の companion module ができ、operation は `flip::coin` のように参照する。
- operation は、`our`(または `pub`)の型 signature として並べる。
- **operation の呼び出しは、普通の関数呼び出しに見える**。呼んだ計算の型には、その effect が残る。
- effect は型引数を持てる(`act ref_update 'a:`)。

```yulang
act ref_update 'a:
    our get: () -> 'a
    our map: ('b -> 'b) -> ()      // 'b はこの operation だけの多相
    our log: 'b -> ()
        where 'b: Display          // handler でも 'b に Display の method が使える
```

状態: 補完は確定。他は仮採用・パース検査済み。出典: `spec/05-effects.md` 5.1。

## `catch`(handler)

```yulang
our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]
```

- `catch expr:` は handler。arm には 2 種類ある。
  - **operation の arm**: `operation pattern, k -> body`。operation の引数と、継続 `k` を受け取る。
  - **value の arm**: `v -> body`。通常の終了(値が返ってきたとき)を処理する。省略すると `v -> v` と同じ。
- `k value` を呼ぶと、operation が起きた地点に値を返して、元の計算を続ける。`k` は限定継続で、何回でも呼べる。上の例は、`true` と `false` の両方で再開している。
- handler は、処理できる effect だけを行から取り除く。それ以外は、外側へ伝わる。

### 部分的な arm

operation の arm の pattern が、payload の一部にしか合わなくてもよい。合わない要求は、元の継続と一緒に外側へ渡される。

```yulang
catch action:
    ask::choose true, k -> k 1     // payload が true の要求だけ処理する
    v -> v
// ask::choose false は外へ渡る。ask::choose は行に残る
```

`case` と違って、`catch` の arm は「引ける範囲のうち、引くものだけ書く」形になる。引けない effect の arm を書くとエラー(後述の注釈を見る)。

### 対象なしの `catch:`

```yulang
my h = catch:
    flip::coin(), k -> k true
    v -> v
```

`catch:` は、一引数の関数を作る。`\a -> catch a:` の略。ただし、`x | catch:` のようにパイプラインの右辺に置いたとき、左辺 `x` の effect が handler に届くかは、まだ決まっていない(`spec/03-expressions.md` の E7)。
状態: `catch expr:` は仮採用、対象なしは確定(届き方は未確定)。パース検査済み。出典: `spec/05-effects.md` 5.2。

## handler は shallow

`k` で再開した計算は、**同じ handler に自動では包まれない**。再開後に同じ effect が起きても、handler は二度目には発火せず、effect は外側へ伝わる。
続けて受けたいときは、arm の中で、継続を handler で包み直す。

```yulang
our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console (k "42")       // 巻き直す
    console::println _, k -> run_console (k ())
    v -> v
```

状態: 確定・パース検査済み。出典: `spec/05-effects.md` 5.3。

## 衛生性: 持ち込まれた effect は奪われない

handler は、自分から見える effect は処理してよいが、**外側の呼び出し元が持ち込んだ effect を奪ってはいけない**。
呼び出し元が持ち込んだ計算(関数、thunk、data の中の effect を持つ関数)の effect は、既定では内側の handler から見えない。見せたいときは、注釈でそう宣言する。

```yulang
our compose(f, g: _ -> [_] _, x: [_] _) = f g(x)     // g(x) の表層の effect を f に見せる
```

理屈と、どの `sub:` に届くかの決まり方は、`spec/05-effects.md` 5.4 を見る。

## effect の注釈

### 一つの規則

effect の注釈は、次の一つの規則で読める。

> **高階関数は、自由に書ける。そのうえで、明示的に見える effect は、ちゃんと検査される。**

注釈は、「どこまでを見える側に出すか」の境界の宣言で、検査されるのは、その境界の内側だけ。注釈が無い所は、検査されず、推論に任される。
(この見方は、衛生性の観点からのユーザーの説明による。spec の 5.5 は、同じ内容を位置ごとの表で書いている。)

- 関数に渡された callback(高階の引数)の effect は、**既定では handler から守られて、見えない**。何も書かなければ、`catch` はそれを引けない。自由に書けて、誤って奪われない。
- 注釈で effect を**見せると宣言**したときだけ、その effect は見える側に入り、`catch` の対象になる。引けない effect の arm は、エラーになる。
- 戻り値側(共変)の注釈も、同じ。**本体に具体的に見えている** effect だけを検査し、まだ見えていないもの(行の変数)は縛らない。

### 位置ごとの表

上の規則を、書く位置ごとに並べた表。

| 位置 | 書き方 | 「見える」の意味 |
| --- | --- | --- |
| 反変(引数の計算など) | `[console]` | その effect を見せる。`catch` が**引いてよい**(許可であって義務ではない) |
| 反変・高階の callback | 注釈なし | 何も見せない。callback 由来の effect は handler から守られる |
| 反変・高階の callback | `[_]` | **全部**見せる(glob)。すべて引いてよい |
| 共変(戻り値側など) | `[console]` | 本体に見えている effect が `console` に収まるかを検査する。見えていない行は縛らない |
| 共変 | 省略、または `[_]` | 追加の検査をしない。行は開いたまま |

- 列挙した注釈は、列挙した effect だけを見せる。`[_]` は glob で、すべての effect を列挙したのと同じ意味。effect 行の中の `_` は、型の穴ではなく glob として働く。
- 反変の注釈が無いと、`catch` はその effect を引けない(`catch` が `io` を引くには、`f(a: [io] _)` が要る)。

```yulang
my f(a: [console] _) =
    catch a:
        console::print s, k -> ...        // 見せた effect なので、引ける
        io::write x, k -> ...             // エラー: io は a の注釈に無く、見えていない
```

- 共変の注釈の検査は、その binding の推論が終わった時点(一般化の直前)で行われる。

状態: 位置ごとの意味は確定。「一つの規則」の見方は、ユーザーの説明で、spec にはまだ書かれていない。出典: `spec/05-effects.md` 5.5。例の構文の細部(T2)は、実行して確かめる項目として残っている。

## effect family の copy

```yulang
act original:
    our tick: () -> never

act local = original with:
    our label = "local"
```

`act copy = source` は alias ではなく、**新しい effect family** を作る。`local::tick` は `original::tick` の別名ではない。

- source から引き継ぐのは `pub` / `our` だけ。source の `my` は、copy 先に現れない。
- source の `our` member が `my` の helper に依存しているときは、helper も copy の private として一緒に持っていく。private の helper が source の operation を呼んでいるときは、copy 先では copy の operation を呼ぶように付け替える。

状態: 可視性の規則は確定、細部は仮採用。パース検査済み。出典: `spec/05-effects.md` 5.6。

## `error` 宣言

```yulang
error path_err:
    not_found path
    denied path
```

`error` は、`enum`、throw する operation を持つ `act`、`impl Throw`、`impl Display`、`wrap` の helper をまとめて作る短縮形。`from` 付きの宣言には、`up` も作る。何を作るかは、言語の仕様として固定されている。

- variant は、**値の constructor と、effect の operation の両方**になる。期待型が error なら値、effect の位置なら operation。
- **`wrap`** は、error effect を handle して、`result` に戻す helper。型は `path_err::wrap : [path_err] 'a -> result 'a path_err`。
- **`up`** は、error effect を別の error effect へ cast する helper。`from` 付きの宣言にだけ作られる。
- record の payload も書ける。

状態: 固定する仕様・パース検査済み。出典: `spec/05-effects.md` 5.7。

## effect 行の method

```yulang
use std::control::nondet::*
(each [1, 2, 3]).list
```

`.list` / `.once` / `.logic` のような method は、receiver の型ではなく、**effect 行**から選ばれる。同じ行の複数の effect が同名の method を持つと、行が絞られるまで selection は曖昧になる。推論が終わっても曖昧なら、曖昧エラー。`p::run e` のように path で指定して直す。
`x.method` の探索は、field と `with:` の method → role の method → effect 行の順に、階層ごとに行う。
状態: 曖昧時の扱いは確定。他は仮採用。出典: `spec/05-effects.md` 5.8。

## junction(effect を持つ条件)

`any` / `all` は、要素を非決定的に選ぶ値になり、`if` の条件が「どれか」「すべて」を表せる。Raku の junction を、effect で再現したもの。

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

`if` の条件が effect を持つ(effect 行に `junction` がある)とき、条件は `junction::junction` という handler で包まれて、真偽が決まる。条件が pure なら、普通の `bool` として扱う。実装は標準ライブラリ(`std::control::junction`)にあり、言語との接続は `if` の 1 箇所だけ。
`junction` を handle する自前の handler も書ける。
状態: 確定・パース検査済み。出典: `spec/05-effects.md` 5.9。
