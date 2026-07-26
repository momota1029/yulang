# `std::testing`

`std::testing` は、lazy な assertion 演算子と、`yulang test` が使う `assertion` effect を提供する。
prelude は両方の演算子を re-export する。

この module はデータ型を導入しない。
test の検出は周囲の test 機構に属する。
その機構は [module](../modules#test-module) を参照。

## lazy な assertion 演算子

`assert condition` は bool の結果を要求する。
`expected assert_eq actual` は、両方の operand が同じ型として推論されることを要求する。

```yulang
mod test assertions:
    my truth = assert (2 + 2 == 4)
    my equality = (2 + 2) assert_eq 4
```

このファイルを `yulang test --show-passes` で実行すると、2 件の成功を表示する。
`assert_eq` の左 operand が `expected`、右 operand が `actual` である。

どちらの演算子も lazy である。
`assert condition` は条件を thunk にし、`assert_eq` は各 operand を別の thunk にする。
test runner は `assertion` effect を処理するときに、その thunk を評価する。

## assertion effect

演算子を展開すると、`assertion` effect の 2 個の operation を呼ぶ。

| Operation | シグネチャ |
|---|---|
| `assertion::assert check` | `(() -> [_] bool) -> [assertion] ()` |
| `assertion::assert_eq (expected, actual)` | `(() -> [_] 'a, () -> [_] 'a) -> [assertion] ()` |

thunk を渡せば、operation を直接呼ぶこともできる。

```yulang
mod test direct_operations:
    my truth = assertion::assert (\() -> true)
    my equality =
        assertion::assert_eq ((\() -> 4), (\() -> 4))
```

組み込みの test runner が `assertion` を処理する。
別の入口からこの operation を実行するコードには、対応する handler が必要である。

## 失敗時の表示

`assert` は、thunk が `false` を返すと現在の test を失敗させる。
`assert_eq` は、2 個の thunk が等しくない値を返すと失敗させる。
test runner は演算子の位置を示す。
`assert_eq` では、左の値を `expected`、右の値を `actual` として表示する。

現在の `assert_eq` のシグネチャには、`Eq`、`Display`、`Debug` の要求がない。
ただし、両方の operand は同じ型として推論されなければならない。

## 早見表

| 記法 | 結果 |
|---|---|
| `assert condition` | bool 式を lazy に `assertion` へ送る |
| `expected assert_eq actual` | 同じ型の 2 値を lazy に `assertion` へ送る |
| `assertion::assert check` | bool の thunk を `[assertion]` で実行する |
| `assertion::assert_eq (expected, actual)` | 同じ型の 2 個の thunk を `[assertion]` で実行する |

## 関連ページ

- [module → Test module](../modules#test-module)：test の検出と実行
- [effect](../effects)：effect 宣言、operation、handler
- [標準ライブラリ一覧](./)：すべての module の一覧
