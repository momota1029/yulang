# アイデア: lambda への label (`\'self x -> ... 'self.again y`) (2026-11-07)

状態: **今は足さない。** ユーザーが以前に考えて、だるくて辞めた案。2026-11-07 の雑談で再検討し、見送りと決めた。
署名: Claude (Sonnet 5.5)、案の発案はユーザー。

## 案

```yulang
my sum_to = \'loop acc i ->
    if i > 100: acc
    else: 'loop.again (acc + i) (i + 1)
```

`'loop` は lambda の「ここに戻る」ための取っ手。`'loop.again a b` は、引数 `a b` で lambda の先頭に戻る。
`case 'count n: ... 'count.again (n - 1)`(spec 3c.5)と同じ流儀の、label の操作。

## 設計の分かれ目

`again` は「脱出して、戻る」動き(`last` / `return` と同じ流儀)なので、**ジャンプだけ**にするのが筋。
`1 + 'loop.again x` のように戻り値を使う書き方は、普通の再帰(名前で呼ぶ)に任せる。
ジャンプだけなら、継続を捕まえずにコンパイルできる(effect の抜け道)ので、スタックが伸びず、速い。

## 見送った理由

- 末尾再帰は、`with:` の局所関数で書ける。

  ```yulang
  my sum_to n = loop 0 1 with:
      our loop acc i = if i > n: acc else: loop (acc + i) (i + 1)
  ```

- 名前の無い lambda の再帰、という狭い場面でしか、label の出番が無い。

## それでも label にだけできること

- **入れ子の callback の奥から、外側の関数の先頭へ、新しい引数で戻る**。普通の再帰では、callback から値を返して、外で判定して、
  もう一度呼ぶ形になる。
- label は値なので、補助関数に渡して、その中から `again` を呼べる(`for 'outer` で既に成り立っている仕組みの延長)。

## 足すとき

仕組み(label が値、`again` が effect の操作)は既にあるので、後から足しても、既存の規則を壊さない。
「callback の奥から、外側の関数の先頭へ戻りたい」という具体的な需要が出たら、そのときに足す。
