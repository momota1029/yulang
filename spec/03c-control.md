# 章3c 制御構文・参照

状態の凡例は [README](README.md)。この章は `for` / `last` / `next` / `redo`、`sub` / `return`、label、`$x` / `&x`、`do` を扱う。
これらは標準ライブラリ（prelude）の面と、少数の構文でできている。parser 専用の予約語ではないものが多い。
effect と handler の意味は章5 に回す。

## 3c.1 `for`　〔要確認〕

```yulang
for x in 0..10:
    say x
```

- `for x in xs:` は `Fold` を実装する値を走査する。body は関数に落ち、`for` 式そのものは `()` を返す。
- **`0..10` は閉区間**（11 回反復する）。半開区間は `0..<10`。

```yulang
for x in 0..<10:     // 10 回
    say x
```

出典: `main:web/docs/ja/reference/control-flow.md` §for
注意: 閉区間が既定なのは Rust や Python と逆なので、罠に当たる（T5）。

## 3c.2 `last` / `next` / `redo`　〔要確認〕

```yulang
for x in 0..:
    if x == 10: last      // ループを抜ける
```

- `last` は現在のループから抜ける。`next` は次の反復へ進む。`redo` は同じ反復をやり直す。
- これらは prelude で定義された演算子で、`loop` effect に接続される。予約語ではない。

## 3c.3 label　〔要確認〕

```yulang
for 'outer x in 0..:
    for y in 0..:
        if y == 3: last 'outer
```

- label は `'outer` のように `'` で始める。`last 'outer` / `next 'outer` / `redo 'outer` は、その label のループを対象にする。

## 3c.4 `sub` と `return`　〔要確認〕

```yulang
sub:
    for x in 0..:
        if x == 5: return x
    0
```

- `sub:` は早期 return の範囲を作る。`return value` は直近の `sub:` から抜ける。値なしの `return` は `()` を返す。
- label 付きの `sub` もある。

```yulang
sub 'done:
    'done.return 42
    0
```

- 深い入れ子の代わりに、`sub:` と `return` で成功経路を平らに保つのが推奨の書き方。

出典: `main:web/docs/ja/reference/control-flow.md`、`main:web/docs/ja/reference/idioms.md`

## 3c.5 `case` と `catch` の label（再帰）　〔要確認〕

`case 'label value:` と `catch 'label action:` は、arm の集合全体に再帰の名前を付ける。body から `'label next` を呼ぶと、同じ arm 集合が `next` に再適用される。

```yulang
my result = case 'count 3:
    0 -> "done"
    n -> 'count (n - 1)
```

- label は個々の arm ではなく、arm 集合に属する。

出典: `main:web/docs/ja/reference/control-flow.md` §case と catch のラベル

## 3c.6 局所の参照 `$x` と `&x`　〔要確認〕

```yulang
my incremented =
    my $count = 0
    &count = $count + 1
    $count
```

- `my $count = 0` は局所の可変な参照を作る。`$count` は読み出し、`&count = value` は更新。
- これらは handled な `var` effect に展開される。したがって、更新は**型システムから見える**（effect 行に `var` が乗る）。
  参照は宣言された scope の中で使い、外部の可変変数として扱わない。
- State は純粋な継続スレッディングで実現される（メモリ上の穴ではない）。

出典: `main:web/docs/ja/guide/pitfalls.md`「参照は effect、メモリ穴ではない」、`main:web/docs/ja/reference/idioms.md`

## 3c.7 `do`　〔要確認・素材が少ない〕

```yulang
my x = effectful do
rest
```

- `do` は継続を切り出す印。`do` の後ろに続く文が lambda として切り出され、`do` の位置に渡される。
  effectful な API を、見た目上は direct style で書くための構文。

出典: `main:notes/design/yulang-language-report.md` §6.9 のみ。

## 3c.8 effectful な条件　〔章5 へ〕

`if` の条件が非決定的な場合（`all` / `any`）は、`std::control::junction` が提供する effectful な真偽値として扱われる。
通常の `bool` の条件は通常の経路を通る。意味は章5 で書く。

## 確認してほしい点

- **F1** `0..10` が閉区間なのは意図した仕様でよいか（`0..<10` が半開）。罠 T5 として載せる。
- **F2** `do` は、`my x = f do` の形以外にどんな形があるか。素材が少ないので、あなたの言葉で説明してほしい。
- **F3** `last` / `next` / `redo` は、`for` 以外（`sub:` の中など）で使えるか。
- **F4** ブロックコメント `/* ... */` が使えると、リファレンスの一つ（構文スタイル）にあった。章1.2 に足してよいか。
