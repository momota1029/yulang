# `std::data::opt`

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
my maybe_text = just "hello"

case maybe_text:
    just text -> text.len
    nil       -> 0
```

compiler は `case` 式の網羅性を検査しない。
一致する arm が一つだけでも受理する。

```yulang
case just 1:
    just x -> x
```

この式は `nil` arm がなくても `1` を返す。
どちらの値も処理する必要がある場合は、両方の variant またはワイルドカードを使う。

## よくある形

```yulang
my maybe_text = just "notes"
my s = "21"

// デフォルト値で埋める
case maybe_text:
    just text -> text
    nil       -> "(no file)"

// 失敗しうるステップを連鎖
case s.to_int:
    just n  -> just (n * 2)
    nil     -> nil
```

より多くのコンビネータが必要なら、プロジェクトのコードで `result`（[std::data::result](./result)）に変換するか、必要なヘルパーだけを定義する。

## 早見表

| 操作 | シグネチャ |
|---|---|
| `nil` | `opt 'a` |
| `just(x)` | `'a -> opt 'a` |

## 関連ページ

- [`std::data::result`](./result) — 失敗に情報を持たせたいとき
- [パターン → enum パターン](../patterns) — variant のパターン
- [エラー](../errors) — effect として表現する型付きエラー
