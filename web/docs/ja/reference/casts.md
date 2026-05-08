# キャスト

Yulang には明示的な `cast` 宣言と、`from` variant から生成される cast があります。

## 明示的な Cast

```yulang
struct user_id { raw: int }

cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }
```

`cast(x: A): B = body` は、標準の `Cast A` role の実装として lower されます。
associated type `to` は `B` になります。

implicit cast は、型注釈、関数引数、branch join などの expected-type boundary で
挿入されます。

```yulang
my id: user_id = 1
```

利用できる `Cast` impl がなければ missing impl、複数候補があれば ambiguous cast
として報告されます。

## `from` Variant

```yulang
enum app_err:
    fs from fs_err
```

`enum` または `error` の variant に `from` を付けると、source type から外側の
enum / error type への `Cast` impl が生成されます。`error` の場合は、throwing
operation と `Throw` impl も生成されます。

## 制限

現在の `cast` 宣言は nominal な source / target type を主な対象にしています。
小さな wrapper type や error aggregation には向いていますが、一般的な structural
conversion system として使うものではありません。
