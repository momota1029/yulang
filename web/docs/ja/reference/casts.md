# cast

Yulang は expected-type 境界で暗黙の cast を挿入する。
cast は、明示的な `cast` 宣言と、`enum` / `error` の variant に付けた `from` marker から生成される。

## 明示的な cast

```yulang
struct user_id { raw: int }

cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }
```

`cast(x: A): B = body` は、`A` から `B` への暗黙の変換規則を登録する。
body が変換後の値を返す。
この宣言は標準の `Cast` role を実装しない。

## cast が挿入される場所

推論された値の型と既知の期待型がぶつかる境界で、compiler は登録済みの変換規則を適用する。
主な適用箇所を次に示す。

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

選ばれた `cast` 宣言の body が変換を行い、compiler は role method `x.cast` を挿入しない。
標準ライブラリには `.cast` method を持つ別の `std::core::convert::Cast` role があるが、`cast` 宣言はその role を実装せず、呼び出しもしない。
期待型のない裸の式では cast されないので、`id` だけなら依然として `user_id` である。

## 診断

```yulang
my use_bool(x: bool) = x
use_bool 42
// error: no implicit cast from int to bool
```

該当する source/target ペアの変換規則がなければ、compiler は暗黙の cast が見つからないと報告する。
一致する宣言が複数ある場合は ambiguous cast として拒否し、Yulang は勝手にどれかを選ばない。

## `from` 付きの variant

次の抜粋では、`path_err` と `parse_err` が nominal エラー型として定義済みであるとする。

```yulang
enum app_err:
    path from path_err
    parse from parse_err
```

`enum`（または `error`）の variant に `from` を付けると、次の 2 つが生成される：

- variant 自体。`app_err::path` は `path_err` を包む
- `path_err` から `app_err` への変換規則。`e` を `app_err::path e` に写す

source 型は payload 1 つ、source と target は両方 nominal である必要がある。

`error` 宣言の `from` は、`wrap` と `up` も拡張して narrower エラーを同時に捕まえるようにする。
詳細は [エラー](./errors) を参照。

## newtype wrapper の pattern

primitive を struct で包むと、型レベルの区別を加えられる。

```yulang
struct seconds { value: int }

cast(x: seconds): int = x.value
cast(x: int): seconds = seconds { value: x }

my one_minute: seconds = 60
my doubled: seconds = one_minute.value * 2
```

wrapper は型システム上のアイデンティティを保ったまま、cast 経由で通常の演算と噛み合う。

## 制限

現在の cast 宣言は nominal な source / target 型を対象とする。
小さい wrapper やエラー集約には向いているが、汎用の structural conversion system として使うものではない。

cast は遅延しない：境界に到達した時点で body が走る。
重い変換は通常の関数として書き、呼び出し地点を明示する方がよい。

## 関連ページ

- [struct と role](./structs)：nominal wrapper 型の宣言
- [エラー](./errors)：`from` ベースのエラー集約
- [値と型](./types)：nominal 型と推論の関わり
