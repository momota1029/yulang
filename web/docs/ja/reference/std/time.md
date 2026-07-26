# `std::time`

`std::time` は、純粋な instant と duration の値、壁時計へのアクセス、単位 constructor、算術、比較、固定された UTC 表示を提供する。

`instant` は、Unix epoch からの経過ナノ秒を保持する時間軸上の一点である。
`duration` は、符号付きのナノ秒数である。
どちらも公開データとして表す。

| 型 | 公開 field | 意味 |
|---|---|---|
| `instant` | `epoch_nanos: int` | Unix epoch からの経過ナノ秒 |
| `duration` | `nanos: int` | ナノ秒単位の符号付き時間長 |

どちらの値も直接構築するだけなら決定的であり、テスト用の値を作るときに使える。
現在時刻の取得は effectful であり、host の時計を通る。

## clock へのアクセス

`clock::now()` のシグネチャは `() -> [clock] instant` である。
`clock` host act は `std::time::now` としても re-export され、prelude からも使える。

```yulang
my current = std::time::clock::now()
(current.epoch_nanos, current.show)
```

最初の結果は、host が返した現在の Unix epoch ナノ秒数である。
2 番目の結果は、同じ instant を RFC 3339 の UTC 形式で表す。
どちらの値も実行ごとに変わる。

`clock::now()` は壁時計を読む。
host の時計が戻れば値も戻るため、性能計測には使ってはならない。

## instant の算術

instant の算術関数は、duration の加算と減算、および 2 個の instant 間の符号付き duration を求める。

```yulang
my start = std::time::instant { epoch_nanos: 10 }
my stop = std::time::instant { epoch_nanos: 25 }
my elapsed = std::time::instant_since stop start

(
    elapsed.nanos,
    (std::time::instant_add start elapsed).epoch_nanos,
    (std::time::instant_sub stop elapsed).epoch_nanos,
)
```

結果は `(15, 25, 10)` になる。
`instant_since` の引数を逆にすると、負の duration を返す。

instant の算術には、この名前付き関数を使う。
現在の `instant` は `+` と `-` を実装していない。

## duration の構築と算術

各単位 constructor は `int` を受け取り、`duration` を返す。
大きな単位は、ナノ秒の正確な整数倍である。

```yulang
my total = std::time::days 1 + std::time::hours 2 + std::time::mins 3 + std::time::secs 4

(
    (std::time::nanos 5).nanos,
    (std::time::micros 2).nanos,
    (std::time::millis 3).nanos,
    total.nanos,
    (std::time::duration_add (std::time::secs 2) (std::time::secs 3)).nanos,
    (std::time::duration_sub (std::time::secs 5) (std::time::secs 3)).nanos,
    (std::time::hours 2 - std::time::mins 30).nanos,
)
```

最初の 3 個の値は `5`、`2000`、`3000000` になる。
`duration` は `Add` と `Sub` を実装する。
したがって、`+` と `-` は `duration_add` と `duration_sub` と同じ振る舞いになる。

## 比較と表示

`instant` と `duration` は `Eq` と `Ord` を実装する。
instant は `epoch_nanos` field、duration は `nanos` field を比較する。

```yulang
my epoch = std::time::instant { epoch_nanos: 0 }
my later = std::time::instant { epoch_nanos: 1 }
my gap = std::time::duration { nanos: 1 }

(
    epoch < later,
    gap == (std::time::nanos 1),
    epoch.show,
    epoch.debug,
    gap.debug,
)
```

結果は `(true, true, "1970-01-01T00:00:00Z", "instant { epoch_nanos: 0 }", "duration { nanos: 1 }")` になる。
`instant.show` は RFC 3339 の UTC 形式を使い、小数秒末尾の不要な 0 を取り除く。
`Debug` は公開された構造表現を保つ。
`duration` は `Debug` を実装するが、`Display` は実装しない。

## 対象範囲

`std::time` は、カレンダー、タイムゾーン、ロケール依存の書式化、解析、タイマー、休止、期限、単調時計を提供しない。
うるう秒の扱いは host の時計に従い、それ以外は未規定である。

## 早見表

| 操作 | シグネチャ |
|---|---|
| `clock::now()` | `() -> [clock] instant` |
| `instant_add(t, delta)` | `instant -> duration -> instant` |
| `instant_sub(t, delta)` | `instant -> duration -> instant` |
| `instant_since(later, earlier)` | `instant -> instant -> duration` |
| `duration_add(x, y)` | `duration -> duration -> duration` |
| `duration_sub(x, y)` | `duration -> duration -> duration` |
| `nanos(count)` | `int -> duration` |
| `micros(count)` | `int -> duration` |
| `millis(count)` | `int -> duration` |
| `secs(count)` | `int -> duration` |
| `mins(count)` | `int -> duration` |
| `hours(count)` | `int -> duration` |
| `days(count)` | `int -> duration` |
| `x + y` / `x - y` | `duration -> duration -> duration` |
| `x == y`、`x < y`、ほかの比較 | `instant -> instant -> bool` または `duration -> duration -> bool` |
| `t.show` | `instant -> str` |
| `t.debug` | `instant -> str` または `duration -> str` |

## 関連ページ

- [`std::io::file`](./fs)：ファイルのメタデータは `opt instant` を含むことがある
- [effect](../effects)：host act と effect handler
- [標準ライブラリ一覧](./)：すべての module の一覧
