# 落とし穴

よく似た Yulang の形でも、異なる方法で構文解析、名前解決、型推論される場合があります。
このページでは、そのような場面で従う規則を項目ごとに示します。

## `f(x)` と `f (x)` と `f: x`

```yulang
f(x)    // 呼び出し
f (x)   // f を「グループ化された式 x」に裸 application
f: x    // colon application
```

三つの形は異なる構文として解析されます。
`f(x)` は C 風の呼び出しで、`f (x)` の空白は ML 風の裸 application を作ります。
`:` の後ろにシンボルが続く場合も構文が変わるため、`f:foo` と `f :foo` は別物です。

C 風の呼び出しでは括弧を関数名に詰め、bare application では括弧を外します。
シンボルへの colon application は `f:foo`、シンボル `:foo` の bare application は `f :foo` と書き分けます。

## ML 引数の中では dot の空白が効く

トップレベルでは、どちらも同じ field `selection` になります。

```yulang
xs.map double      // (xs.map) double
xs .map double     // 同じ — `.map` は xs に付く
```

この一致は、dot つき式を bare application の引数にすると崩れます。
ML 引数の文脈では、空白が現在の引数を終わらせ、次の dot を *外側* の式に付けます。

```yulang
f xs.map           // f (xs.map)
f xs .map          // (f xs).map
```

`xs.map` を引数として渡し、dot を `xs` に付ける場合は詰めて書きます。
それ以外は `xs.map` と `xs .map` のどちらでも同じです。

## 改行で裸 application は閉じる

```yulang
f x y

f x
    y    // 裸 application ではない。これは新しい statement
```

改行は裸 application のチェインを終わらせるため、上の `y` は新しい statement を始めます。
複数行にわたって application を続ける場合は、brace / colon block を使うか、字下げして継続式の一部にします。

## `our` と `pub` の違い

二つの export keyword は異なる方向を指します。
`with:` の中ではどちらも companion 経由で他の module から見えますが、`pub` はその値を module 自身の型 pane にも公開します。

`with:` 内の method や `act` 内の operation のように、囲んでいる companion module へ binding を export する場合は `our` を使います。
下流の module が `use` する top-level helper のように、module の外へ export する場合は `pub` を使います。

## `error E:` の variant は constructor 兼 operation

```yulang
my err: path_err = path_err::not_found path    // 値
path_err::not_found path                       // effect operation
```

同じ名前が文脈で振る舞いを変えます。
期待型がエラー ADT なら式は constructor になり、effectful な位置なら operation を発火します。

周囲のコードだけで意味が決まらない場合は、注釈を加えます。

## `fail e` は魔法ではない

`fail e` は特別なエラー構文に見えますが、`fail` は `\e -> e.throw` を prefix 演算子として export したものです。
`e.throw` に置き換えても同じように動き、呼び出し地点が少し賑やかになるだけです。

異なるエラーの挙動を求めてではなく、読みやすさのために `fail e` を選びます。

## 参照は effect、メモリ穴ではない

```yulang
my $count = 0
my f() = &count = $count + 1
```

`$count` と `&count` は mutable cell への直接アクセスに見えますが、handled `var` effect として展開されます。
これらを使う関数は、ref binding がその scope 内にない限り、対応する `var` effect row を型に持ちます。

ref は宣言された scope 内で使い、外部の可変変数として扱わないようにします。

## 小さい effect も型に乗る

```yulang
my f() =
    say "hi"       // 行に [console] が乗る
    42
```

`f` は 1 回出力するだけでも effect row が空ではありません。
effectful な operation は型推論から見えます。

呼び出し側で effect row を消す必要がある場合は、`run_console: f()` のような handler を入れます。

## anyhow 風はない

書きたくなる `catch _ -> ...` という形は、任意のエラーを捕まえません。
Yulang のエラーは名指しで捕まえ、`Display` 経由の実行時 dispatch は行いません。

エラーは `from` で集約し、`up` で持ち上げ、`wrap` で値に閉じます。
anyhow 風の境界が必要な場合は、適切な `from` を持つ広めの `error E: ...` を定義します。

## 推論結果に残る変数

```text
twice : Add<α> => α -> α
```

この出力の `α` はエラーではありません。
binding が多相なので残った residual な type variable です。

residual を具体型に固定する必要がある場合は、binding に注釈します。

## pattern の `_` は何にでもマッチする wildcard

```yulang
case xs:
    [_, _] -> "two elements"
    _      -> "other"
```

`_` は任意の値にマッチし、名前を bind しません。
同じ `_` を繰り返すと等値比較に見えますが、各 wildcard は独立しているため、異なる値にもマッチします。

2 つの位置が同じ値であることを要求する場合は、それぞれに名前を付け、guard で比較します。

```yulang
case (a, b):
    (x, y) if x == y -> "same"
    _ -> "different"
```

## 演算子の import は構文的

```yulang
use my_ops::(+)
```

演算子を使う式は通常の未解決名に見えますが、その演算子は import が scope に入るまで構文解析されません。
import より前に使うと、name エラーではなく parse エラーになります。

演算子は名前を括弧で囲んで import し、使う式より前に import を置きます。

## 型推論の失敗を適切な層で調べる

「推論が通らない」関数には、`Cast` が無い場合、effect tail が未確定な場合、method selection が具体情報を待っている場合があります。

まず `yulang check path/to/file.yu` を使います。
成功時は何も出力せず、失敗時だけ diagnostic を出します。
推論された binding 型や role constraint を含む compiler IR を調べる場合は、`yulang dump path/to/file.yu --poly` を使います。

## 関連ページ

- [構文スタイル](../reference/syntax-style)：空白の正確なルール
- [イディオム](../reference/idioms)：落とし穴を回避する書き方
- [リファレンス](../reference/)：機能の詳細
