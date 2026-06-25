# キャスト

Yulang は expected-type 境界で暗黙の cast を挿入する。cast の出どころは 2 つ：
明示的な `cast` 宣言と、`enum` / `error` の variant に付けた `from` マーカー。

## 明示的な cast

```yulang
struct user_id { raw: int }

cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }
```

`cast(x: A): B = body` は、標準の `Cast A` role の impl として lower される。
associated type `to` は `B` になり、body が変換後の値を返す。

## cast が挿入される場所

推論された値の型と既知の期待型がぶつかる境界で、compiler は `Cast` 呼び出しを
挿入する。主な場面は次の通り：

- binding や引数の型注釈
- 関数の引数
- 分岐の合流（2 つの arm が同じ型に揃う必要がある場所）
- effect arm の結果型

```yulang
my id: user_id = 1
my back: int = id

my use_int(n: int) = n + 1
use_int id   // user_id が int に暗黙 cast される
```

挿入される cast は、変換される値の role method `x.cast`。期待型のない裸の
式では cast されないので、`id` だけなら依然として `user_id`。

## 診断

```yulang
my n: int = "abc"
// missing Cast str -> int impl
```

該当する impl が無ければ「specific な source/target ペアの Cast が見つからない」
として報告される。候補が複数ある場合は ambiguous cast として弾かれる — Yulang は
勝手にどれかを選ぶことをしない。

## `from` 付きの variant

```yulang
enum app_err:
    path from path_err
    parse from parse_err
```

`enum`（または `error`）の variant に `from` を付けると、次の 2 つが生成される：

- variant 自体 — `app_err::path` は `path_err` を包む
- `Cast path_err -> app_err` の impl。`e` を `app_err::path e` に写す

source 型は payload 1 つ、source と target は両方 nominal である必要がある。

`error` 宣言の `from` は、`wrap` と `up` も拡張して narrower error を同時に
捕まえるようにする。詳細は [エラー](./errors) を参照。

## newtype ラッパーのパターン

プリミティブを struct でくるんで型レベルの区別を入れるのは、よくあるパターン：

```yulang
struct seconds { value: int }

cast(x: seconds): int = x.value
cast(x: int): seconds = seconds { value: x }

my one_minute: seconds = 60
my doubled: seconds = one_minute.value * 2
```

wrapper は型システム上のアイデンティティを保ったまま、cast 経由で通常の演算と
噛み合う。

## 制限

現在の cast 宣言は nominal な source / target 型を対象とする。小さい wrapper や
error 集約には向いているが、汎用の structural conversion system として使う
ものではない。

cast は遅延しない：境界に到達した時点で body が走る。重い変換は通常の関数として
書き、呼び出し地点を明示する方がよい。

## 関連ページ

- [構造体とロール](./structs) — 背後の role 機構
- [エラー](./errors) — `from` ベースのエラー集約
- [値と型](./types) — nominal type と推論の関わり
