# レコードリテラル直後のメソッド呼び出しが解決しない

発見日: 2026-07-26
状態: 未修正
発見経緯: `derives` の DERIVE-D / DERIVE-E を手で動作確認しているときに 2 回踏んだ。
derives とは無関係で、既存の挙動である。

## 症状

レコードリテラルの直後にメソッドを続けると、role 実装が見つからないと言われる。

```yu
struct point { x: int, y: int } derives Eq

point { x: 1, y: 2 }.eq point { x: 1, y: 2 }
```

```console
compile error [yulang.unresolved-method]: no role implementation satisfies this method call
    --> line 3, column 22
  detail: no role implementation satisfies this method call for receiver
          {x: int, y: int} -> {x: int, y: int} -> bool
```

`Debug` でも同じ。

```yu
struct inner { v: int } derives Debug
struct outer { name: str, part: inner } derives Debug

outer { name: "a", part: inner { v: 1 } }.debug
```

```console
  detail: ... for receiver {name: std::text::str::str, part: inner} -> std::text::str::str
```

## 束縛を挟めば通る

```yu
my o = outer { name: "a", part: inner { v: 1 } }
o.debug            -- "outer { name: \"a\", part: inner { v: 1 } }"
```

`==` 演算子も通る。

```yu
point { x: 1, y: 2 } == point { x: 1, y: 2 }    -- true
```

したがって導出された impl 自体は正しく、レコードリテラルとメソッド呼び出しの
結合のしかたの問題である。

## 診断そのものにも誤りがある

`detail` が「receiver」として表示しているのは、**受信者の型ではなくメソッドの型**である。

- 1 例目の受信者は `{x: int, y: int}` だが、表示は `{x: int, y: int} -> {x: int, y: int} -> bool`
- 2 例目の受信者は `{name: str, part: inner}` だが、表示は `{name: str, part: inner} -> str`

どちらも `Eq.eq` / `Debug.debug` のメソッド型をそのまま出している。
受信者の型が読めないので、利用者はどこが悪いのか判断できない。

hint の `add or import an impl for the receiver type` も、この場合は誤った助言になる。
impl は存在していて、解決に失敗しているのは別の理由である。

## 着手前に確認すること

- レコードリテラル直後の `.method` が、どの段階で受信者を取り違えるか。
  パーサの結合か、lowering のメソッド解決か。
- `==` が通るのに `.eq` が通らない差はどこか。演算子経由と直接のメソッド呼び出しで
  受信者の決まり方が違うのか。
- `detail` に渡している型が受信者ではなくメソッドである件は、この構文に固有か、
  `yulang.unresolved-method` 全体の問題か。後者なら影響範囲は広い。
- 他のリテラル（tuple、list、string）でも同じか。レコードに固有か。

## 関連

- `notes/design/2026-07-26-derives-clause-design.md`（この確認の対象だった機能。本件とは独立）
