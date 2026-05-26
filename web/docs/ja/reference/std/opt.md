# `std::opt`

`opt 'a` は省略可能な値を表す。variant は 2 つ：

```yulang
pub enum opt 'a = nil | just 'a
```

prelude が `opt` / `just` / `nil` を re-export しているので、ユーザコードは
修飾なしで書ける。

## 構築

```yulang
nil
just 42
just "hello"
```

## パターンマッチ

```yulang
case maybe_text:
    just text -> text.len
    nil       -> 0
```

`opt` の variant は網羅的：`opt 'a` に対する `case` は両方の arm（または
ワイルドカード）が必要で、推論はそれで安定する。

## よくある形

```yulang
// デフォルト値で埋める
case maybe_text:
    just text -> text
    nil       -> "(no file)"

// 失敗しうるステップを連鎖
case parse_int s:
    just n  -> just (n * 2)
    nil     -> nil
```

優れたコンビネータが欲しいときは `result`（[std::result](./result)）に持ち
上げるか、必要なヘルパーだけプロジェクトで書く。

## 早見表

| 操作 | シグネチャ |
|---|---|
| `nil` | `opt 'a` |
| `just(x)` | `'a -> opt 'a` |

## 関連ページ

- [`std::result`](./result) — 失敗に情報を持たせたいとき
- [パターン → enum パターン](../patterns) — variant のパターン
- [エラー](../errors) — effect として表現する型付きエラー
