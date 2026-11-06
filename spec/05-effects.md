# 章5 effect と handler

状態の凡例は [README](README.md)。この章は **利用者から見える effect の意味**を書く。
solver の内部表現（directed stack weight、`J = H ∩ Common(L)` による row の分割など）は、仕様ではなく核の計算体系（Lean）の側で扱う。
effect 注釈が位置によって意味を変える点は、先に確定した [T2・T3](traps.md) が本体で、5.5 でまとめる。
素材は effect 行を `;` 区切りで書いていたが、ここでは新表記の `,` に直してある（[T1](traps.md)）。

## 5.1 `act` と operation　〔補完は確定、他は仮採用〕

```yulang
act flip:
    our coin: () -> bool

my bit = flip::coin()
```

- `act` は effect の family を作る。同名の companion module ができ、operation は `flip::coin` のように参照する。
- operation は `our`（または `pub`）の型 signature として並べる。
- **operation の呼び出しは普通の関数呼び出しに見える。** 呼んだ computation の型には、その effect が残る（`flip` が effect 行に入る）。
- operation の signature に出てくる、`act` の型引数ではない型変数（`'b`）は、その operation だけの多相になる（確定, 2026-11-04）。呼び出しごとに別の型で使える。呼び出す側は好きな型を選べる（`apply::twice (\x -> x + 1)` のように）。一方 handler の側では、その `'b` が何の型か分からない抽象的な型として受け取る（`'b -> 'b` の関数らしいが `'b` は不明。確定, 2026-11-04）。呼ぶ側で全称、受ける側で存在のように働く。handler の中では、`'b` の値は型が合う範囲（`k` に渡して再開する、別の `'b -> 'b` と合成する）で流すだけ。`'b` は handler の中に閉じ込められ、handler 全体の結果の型や外側の環境の型に現れてはならない（エラーにする。確定, 2026-11-05。存在型は導入しない）。operation の signature に role の制約を書けば、handler でもその role の method を使える（確定, 2026-11-04）。綴りは署名の下の `where`（確定, 2026-11-05。章6.3）。

```yulang
act ref_update 'a:
    our get: () -> 'a
    our map: ('b -> 'b) -> ()      // 'b はこの operation だけの多相
    our log: 'b -> ()
        where 'b: Display          // handler でも 'b に Display の method が使える
```

- effect は型引数を持てる: `act ref_update 'a:`。行には `ref_update int` のような entry が入る。
- operation の signature は、最後の戻り位置に effect が書かれていなければ、その `act` の effect を**補う**（確定, 2026-11-04）。
  effect を送出しない operation は作れない。
  戻りに effect を書いたときも、その `act` 自身の effect は自動で足される（確定, 2026-11-04）。`our coin: () -> [io] bool` は `() -> [flip, io] bool` になる。書いた effect は追加であって、置き換えではない。
- 一般に、関数型の戻り側には形式上いつも effect 行が付く。`'a -> ('b -> 'c)` には形式的に `'a -> [e] ('b -> 'c)` が付く。
  表示で行が見えなくても、型の中には行がある。

出典: `main:web/docs/ja/reference/effects.md`、`main:notes/design/yulang-language-report.md` §5.8

## 5.2 `catch`（handler）　〔仮採用〕

```yulang
our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]
```

- `catch expr:` は handler。operation arm は operation の引数と継続 `k` を受け取る。value arm `v -> ...` は通常終了を処理する。
- `k value` を呼ぶと、operation の発生地点に値を返して元の計算を続ける。`k` は限定継続で、何回でも呼べる（multi-shot。確定, 2026-11-04）。（上の例は `true` と `false` の両方で再開する）。
- value arm は省略できる（確定, 2026-11-04）。省略したら `v -> v` と同じで、`action` の値がそのまま返る。型は handler の返り値の型と合わなければならない。
- 推論される型:

```text
all_paths : 'a [flip, 'b] -> ['b] list 'a
```

  `flip` だけを処理し、残りの行 `'b` は外側へ残す。
- handler は処理できる effect だけを行から取り除く。それ以外は外側へ**伝播**する。

出典: `main:web/docs/ja/reference/effects.md`、`main:web/docs/ja/reference/control-flow.md`

## 5.3 handler は shallow　〔確定〕

`k` で再開した計算は、**同じ handler に自動では包まれない**（言語として約束する, 確定, 2026-11-04）。再開後に同じ effect が起きても、handler は二度目には発火せず、effect は外側へ伝わる。
続けて受けたいときは、arm の中で継続を handler で包み直す。

```yulang
our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console (k "42")       // 巻き直す
    console::println _, k -> run_console (k ())
    v -> v
```

出典: `main:web/docs/ja/reference/effects.md` §handler は shallow

## 5.4 handler hygiene　〔確定〕

handler は、**自分から見える effect は処理してよいが、外側の呼び出し元が持ち込んだ effect を奪ってはいけない**。

```yulang
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

この結果は `0`。callback の中の `sub::return i` は外側の `sub::sub` の effect で、`g` の内側に隠れた同じ family の handler が捕まえてはいけない。

- 高階関数 `compose f g x = f(g x)` でも、`g x` が起こす effect を `f` の内側の handler が偶然捕まえてはいけない。
- 呼び出し元が持ち込んだ computation（関数、thunk、data の中の effectful な関数）の effect は、既定では内側の handler から**見えない**。
- 見せたいときは、注釈でそう宣言する（5.5）。

```yulang
our compose(f, g: _ -> [_] _, x: [_] _) = f g(x)     // g(x) の表層の effect を f に見せる
```

出典: `main:web/docs/ja/reference/effects.md` §handler hygiene、`main:web/docs/ja/reference/type-theory.md`

## 5.5 effect 注釈の意味（T2・T3 のまとめ）　〔確定〕

effect 注釈は、公開される型の行を説明すると同時に、**高階の境界で handler に何を見せてよいか**を決める局所的な契約になる。
注釈は閉じた形式で書くが、実際には開いた注釈として扱われる（T3）。

| 位置 | 書き方 | 意味 |
| --- | --- | --- |
| 反変（引数の computation など） | `[console]` | その effect を**引いてよい**行（T2）。許可であって義務ではない |
| 共変（戻り値側など） | `[console]` | 今は具体的な型が見えない行を許す。具体的に見える effect が `console` に収まらなければエラー（T3） |
| 共変 | 省略 / `[_]` | 追加の検査をしない。行は開いたまま |
| 反変・高階の callback | 注釈なし | callback 由来の effect は handler から守られる（空の可視性） |
| 反変・高階の callback | `[_]` | **全部**引いてよい（glob。`[io, undet, console, ...]` と書いたのと同じ。`g: _ -> [_] _` の形） |

- 高階の callback 境界では、**注釈なしは「何も取らない」**。
- **`[console]` のように列挙した注釈は、列挙した effect だけを引いてよい**（T2）。
- **`[_]` は glob** で、**すべての effect を列挙したのと同じ意味**になる（`[io, undet, console, ...]`）。
  `*` でもよかったが、面倒なので通常の hole と同じ `_` で書く（確定, 2026-11-04）。
  effect 行の中の `_` は、型の穴（章4.2）ではなく glob として働く。
- 反変の注釈がないと、`catch` はその effect を引けない（`catch` が `io` を引くには `f(a: [io] _)` が要る。T2）。
- 引けない effect の arm を `catch` に書くと、**エラー**になる（確定, 2026-11-06）。許可（反変の注釈）に含まれない effect の arm は決して実行されないので、静的に報告する。

### 5.5b 共変の注釈を検査する時点　〔確定, 2026-11-05〕

共変位置の注釈（T3）が「見えている具体 effect」を検査する時点は、**その binding（相互再帰なら SCC 全体）の推論が終わった時点、一般化の直前**である。ソースで注釈を見た順や、本体の中の順序には依らない。

- 戻り値の注釈は本体より前に書くが、本体が起こす具体 effect も見える（`my f(g): [io] _ = undet::choice [1, 2]` はエラー）。
- 引数の注釈から分かっている effect（`g: _ -> [undet] _`）も見える。
- 相互再帰では、同じ SCC の他の member の effect も見える。書く順番を入れ替えても結果は同じ。
- 呼び出し側で、一般化された変数に後から入る effect は見ない。それは型の具体化（代入）であって、注釈の再検査ではない（T3）。
- 入れ子の `my` は、その `my` 自身の推論が終わった時点で自分の注釈を検査し、外側の binding の終わりを待たない。

出典: `main:web/docs/ja/reference/type-theory.md` §effect 注釈の意味の表、[traps.md](traps.md) の T2・T3

## 5.6 effect family の copy　〔可視性の規則は確定、細部は仮採用〕

```yulang
act original:
    our tick: () -> never

act local = original with:
    our label = "local"
```

- `act copy = source` は alias ではなく、**新しい effect family** を作る。`local::tick` は `original::tick` の別名ではない。
- source から継承するのは `pub` / `our` だけ。source の `my` は copy 先の公開面にも `with:` にも**現れない**。
- source の `our` member が source の `my` の helper に依存している場合、**helper も copy の private として一緒に持っていく**（確定, 2026-11-04）。
  copy 先でも member は動き、helper は外から見えないまま。source の実装詳細を変えても copy が壊れない。

```yulang
act source:
    my helper = 10
    our tick: () -> never
    our twice = helper * 2

act copy = source          // twice は copy でも動く。helper は copy の private
```

- main の素材は「依存すると copy 先で解決できなくなる（ill-formed）。意図した規則」と書いていたが、この章では採らない。
- private の helper が source の operation を呼んでいるときは、copy 先では **copy の operation** を呼ぶように付け替える（確定, 2026-11-04）。
  copy は新しい family なので、source の operation を呼び続けると、copy を handle しても helper が起こす effect が handler に届かない。

```yulang
act source:
    my helper () = tick ()
    our tick: () -> never
    our twice () = helper ()

act copy = source          // copy::twice の中の tick は copy::tick
```

出典: `main:web/docs/ja/reference/effects.md` §effect family の copy、`main:spec/2026-06-25-act-copy.md`

## 5.7 `error` 宣言　〔固定する仕様〕

```yulang
error path_err:
    not_found path
    denied path
```

- `error` は `enum`、throw する operation を持つ `act`、`impl Throw`、`impl Display`、`wrap` helper をまとめて作る短縮形。`from` 付きの宣言には `up` も作る。
  **何を作るかは言語の仕様として固定する**（確定, 2026-11-04）。標準ライブラリの実装詳細ではない。
- **variant は値の constructor と effect の operation の両方**になる。期待型が error なら値、effect の位置なら operation。
- **`wrap` は、error effect を handle して `result` に戻す**helper（確定, 2026-11-06）。**`up` は、error effect を別の error effect へ cast する**helper で、`from` 付きの宣言にだけ作られる。型は次のとおり（確定, 2026-11-06）。`path_err::wrap : [path_err] 'a -> result 'a path_err`、`app_err::up : [path_err] 'a -> [app_err] 'a`（`app_err` が `path from path_err` を持つとき。`path_err` の operation を handle して `app_err::path e` として投げ直す。継続は再開しない）。`from` 付きの宣言の `app_err::wrap` は、`from` で結んだ狭いエラーも同時に handle し、`err (app_err::path e)` のように包んで `result` に入れる。
- record payload も許す（章4.5）。

出典: `main:web/docs/ja/reference/effects.md` §error 宣言、`main:web/docs/ja/guide/pitfalls.md`

## 5.8 effect 行の method　〔曖昧時の扱いは確定、他は仮採用〕

```yulang
use std::control::nondet::*
(each [1, 2, 3]).list
```

- `.list` / `.once` / `.logic` のような method は、receiver の型ではなく**effect 行**から選ばれる。
- 同じ行の複数の effect が同名の method を持つと、行が絞られるまで selection は曖昧になる。
- `x.method` の探索は階層ごとに行い、前の階層（field/`with:` の method → role の method → effect 行）で見つかったものが勝つ（確定, 2026-11-04）。後ろの階層は前で見つからなかったときだけ調べる。同じ階層に複数の候補があれば曖昧エラー。
- 推論が終わっても曖昧なままなら、**曖昧エラー**（確定, 2026-11-04）。`impl` の候補が複数あるとき（章6.2）と同じ扱いで、
  利用者が `p::run e` のように path で指定して直す。行の中の順序で選ぶことはしない（行は集合として扱う）。

## 確認してほしい点

なし（N1 は I8 で解決）。
