# 落とし穴

初心者が引っかかりやすい挙動と、覚えておくと楽な経験則をまとめています。

## `f(x)` と `f (x)` と `f: x`

```yulang
f(x)    // 呼び出し
f (x)   // f を「グループ化された式 x」に裸 application
f: x    // colon application
```

似て見えますが parser は別物として扱います。`f(x)` は C 風の呼び出し、`f (x)` は空白が ML 風の裸 application を作ります。`f: x` は colon application です。迷ったら、呼び出しなら括弧を関数名に詰める、bare application なら括弧を外す、で覚えてください。

シンボルが `:` の後ろに続くとき、**`f:foo` と `f :foo` は別物** です。意図的に空白を入れて区別します。

## ML 引数の中ではドットの空白が効く

トップレベルではどちらも同じ field 選択になります。

```yulang
xs.map double      // (xs.map) double
xs .map double     // 同じ — `.map` は xs に付く
```

空白で意味が変わるのは、ドットつき式が裸の application の引数として書かれているときだけです。ML 引数の文脈では、空白が引数を一区切りにして、次のドットを *外側* の式に付けます。

```yulang
f xs.map           // f (xs.map)
f xs .map          // (f xs).map
```

`xs.map` を引数として渡したいときは詰めて書きます。それ以外は `xs.map` でも `xs .map` でも好きに書けます。

## 改行で裸 application は閉じる

```yulang
f x y

f x
    y    // 裸 application ではない。これは新しい statement
```

改行は裸 application のチェインを終わらせます。複数行に渡って引数を並べたいときは、brace / colon block を使うか、字下げで継続式の一部にしてください。

## `our` と `pub` の違い

`our` は binding を **囲んでいる companion module へ** export します。`with:` 内の method や `act` 内の operation で使う標準形です。

`pub` は binding を **module の外へ** export します。他の file から `use` する top-level の helper に付けます。

`with:` の中ではどちらでも companion 経由で見えますが、`pub` を付けるとその module の type pane にもその値が現れます。

## `error E:` の variant は constructor 兼 operation

```yulang
my err: fs_err = fs_err::not_found "/x"    // 値
fs_err::not_found "/x"                      // effect operation
```

同じ名前が文脈で振る舞いを変えます。期待型が error ADT なら constructor、effectful な位置なら operation を発火します。周囲が意味を決めないときは明示的に注釈してください。

## `fail e` は魔法ではない

`fail` は `\e -> e.throw` を prefix 演算子として export したものです。`fail` を `e.throw` で置き換えても同じように動きます。呼び出し地点が少し賑やかになるだけで、`fail` の利点は読みやすさだけです。

## 参照は effect、メモリ穴ではない

```yulang
my $count = 0
my f() = &count = $count + 1
```

`$count` と `&count` は handled `var` effect として展開されます。`f` を使う関数は、ref binding がそのスコープ内にない限り、対応する `var` 行を型に持ちます。「どこからでも見える可変変数」を期待しないでください。

## 小さい effect も型に乗る

```yulang
my f() =
    say "hi"       // 行に [console] が乗る
    42
```

`f` の effect 行は空ではありません。呼び出し側で行を消したければ handler を入れます（`run_console: f()`）。effect の混入は推論に見えるので、「ちょっと出力するだけ」の関数も自分の存在を主張します。

## anyhow 風はない

Yulang のエラーは **名指しで捕まえます**。任意のエラーを受ける `catch _ -> ...` や `Display` 経由の実行時 dispatch は提供していません。エラーは `from` で集約し、`up` で持ち上げ、`wrap` で値に閉じます。すべて明示的にやります。anyhow が欲しくなるときは、適切な `from` を持つ広めの `error E: ...` を書く方向で考えてください。

## 推論結果に残る変数

```text
twice : Add<α> => α -> α
```

推論結果の `α` や `β` はエラーではなく、binding が多相なので残った residual な型変数です。具体型に固定したいときは binding に注釈します。

## パターンの `_` は「何でも」ではなく fresh 変数

```yulang
case xs:
    [_, _] -> "two elements"
    _      -> "other"
```

`_` はそれぞれが独立した wildcard で、同じ値である必要はありません。同じ値を 2 回 bind したい場合は名前を付けて、ガードで比較します。

```yulang
case (a, b):
    (x, y) if x == y -> "same"
    _ -> "different"
```

## 演算子の import は構文的

```yulang
use my_ops::(+)
```

演算子は名前を括弧で囲んで import します。スコープに入る前にその演算子を使う式があると、name error ではなく parse error になります。

## おかしいときに見る場所

- `yulang check path/to/file.yu` は residual な制約や role を出すので、どこで止まっているかがだいたい見えます。
- 「推論が通らない」関数は、`Cast` が無い、effect tail が未確定、method selection が具体情報待ち、のどれかであることが多いです。

## 関連ページ

- [構文スタイル](../reference/syntax-style) — 空白の正確なルール
- [イディオム](../reference/idioms) — 落とし穴を回避する書き方
- [リファレンス](../reference/) — 機能の詳細
