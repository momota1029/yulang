# `std::result`

`result 'ok 'err` は、失敗しうる計算の値表現。エラー effect を値に閉じて、
保持・返却・パターンマッチしたいときに使う。

```yulang
pub enum result 'ok 'err:
    ok 'ok
    err 'err
```

prelude が `result` / `ok` / `err` を re-export している。

## 構築

```yulang
ok 1
ok "yes"
err "missing config"
err fs_err::not_found "p"
```

## パターンマッチ

```yulang
case maybe_n:
    ok n  -> n + 1
    err e -> 0
```

## コンビネータ

```yulang
my doubled = (ok 21).map (\x -> x * 2)       // ok 42

(ok 1).and_then (\x -> ok (x + 1))           // ok 2
(ok 1).and_then (\_ -> err "stop")           // err "stop"
(err "stop").and_then (\x -> ok x)           // err "stop"

(ok 1).unwrap_or 0                            // 1
(err "boom").unwrap_or 0                      // 0
```

| ヘルパー | 振る舞い |
|---|---|
| `r.map f` | `ok` 値に `f` を当て、`err` はそのまま |
| `r.and_then f` | `ok` 値で `f` を走らせる（`f` が再び `result` を返す）|
| `r.unwrap_or fallback` | `ok` 値を取る、`err` なら `fallback` |

## `error E:` と `wrap` との関係

```yulang
case fs_err::wrap: read_text_or_throw path
of
    ok text -> use text
    err e   -> e.show
```

`E::wrap` は thunk を走らせ、対応するエラー effect を捕まえて
`result 'ok E` を返す。effect ベースのエラーと値表現の標準的なブリッジ。

`from` で集約したエラーでは、`wrap` がリンクされた narrower error も同時に
捕まえる。詳細は [エラー](../errors) を参照。

## 早見表

| 操作 | シグネチャ |
|---|---|
| `ok(x)` | `'a -> result 'a 'err` |
| `err(e)` | `'err -> result 'ok 'err` |
| `r.map f` | `result 'a 'err -> ('a -> 'b) -> result 'b 'err` |
| `r.and_then f` | `result 'a 'err -> ('a -> result 'b 'err) -> result 'b 'err` |
| `r.unwrap_or fallback` | `result 'a 'err -> 'a -> 'a` |

## 関連ページ

- [エラー](../errors) — `error E:` と catch-by-name
- [`std::opt`](./opt) — エラー側が情報を持たないとき
- [キャスト](../casts) — result 風 wrapper との変換
