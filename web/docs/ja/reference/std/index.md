# 標準ライブラリ一覧

この一覧では、標準ライブラリに含まれるすべての module、その役割、詳しい参照ページの有無を調べられる。

`std` は root の集約 module である。
`std::core`、`std::control`、`std::data`、`std::io`、`std::text` は child module を宣言する。
`std::io` は child module の公開名も re-export する。
`std::num` は数値 role と child module の `frac` をまとめる。

prelude を無効にしない限り、entry file は `std::prelude::*` を import する。
prelude は、通常のプログラムが module path なしで使う演算子、role、型、constructor、effect、I/O helper を re-export する。
link のある module 名から、その module を説明するページへ移動できる。
**未文書化**は、この一覧より詳しいページがまだないことを表す。
**暫定**は、その module が安定した表面に含まれないことを表す。綴りは変わる見込みであり、プログラムが依存してはならない。

## 入口 module と暗黙 import

| Module | 役割 | 文書 |
| --- | --- | --- |
| `std` | 標準ライブラリの top-level module 12 個を宣言する。 | 未文書化 |
| `std::control` | 制御構文の effect、非決定性、エラー、可変参照をまとめる。 | 未文書化 |
| [`std::core`](./core) | core role と演算子をまとめ、`id` と `compose` を定義する。 | 参照あり |
| `std::data` | collection role と、list、optional、range、result の型をまとめる。 | 未文書化 |
| `std::io` | console、file、network I/O の surface をまとめて re-export する。 | 未文書化 |
| `std::text` | bytes、char、str、path、parse、config、Yumark の support をまとめる。 | 未文書化 |
| [`std::prelude`](../modules) | entry file が明示的な import なしで受け取る標準名を re-export する。 | 参照あり |

## Control module

| Module | 役割 | 文書 |
| --- | --- | --- |
| [`std::control::flow`](../control-flow) | effect による早期 return、loop、ラベル付き loop 制御を実装する。 | 参照あり |
| [`std::control::junction`](./nondet#junction) | effectful な `all` と `any` によって、比較を `Fold` の値へ広げる。 | 参照あり |
| [`std::control::nondet`](./nondet) | 非決定性計算の二分岐、棄却、探索 helper、結果 collector を提供する。 | 参照あり |
| [`std::control::throw`](../errors) | エラー値と `.throw` や `fail` が発火する effect を結ぶ `Throw` role を定義する。 | 参照あり |
| [`std::control::var`](../../guide/cookbook) | effect を使う参照と、局所的な可変 binding の基礎になる `get` と `set` を実装する。 | 参照あり |

## Core module

| Module | 役割 | 文書 |
| --- | --- | --- |
| [`std::core::cmp`](./core#std-core-cmp) | `Eq` と `Ord` の role、および標準 impl を定義する。 | 参照あり |
| [`std::core::convert`](./core#std-core-convert) | `Cast` role と、標準の path 変換規則および数値変換規則を定義する。 | 参照あり |
| [`std::core::fmt`](./core#std-core-fmt) | display と debug の role、書式指定、標準 impl を定義する。 | 参照あり |
| [`std::core::ops`](../operators) | 制御、range、算術、比較、bool の標準演算子を宣言する。 | 参照あり |
| [`std::core::seq`](./core#std-core-seq) | `Len` と `IsEmpty` の role、および標準 sequence 型の impl を定義する。 | 参照あり |

## Data module

| Module | 役割 | 文書 |
| --- | --- | --- |
| [`std::data::fold`](./list) | fold、探索、包含判定、非決定的な要素選択を持つ `Fold` を定義する。 | 参照あり |
| [`std::data::index`](./list) | container と key の型から index 後の値の型を決める `Index` role を定義する。 | 参照あり |
| [`std::data::list`](./list) | persistent list、変換、slice、sort、可変参照 view を提供する。 | 参照あり |
| [`std::data::opt`](./opt) | optional 値を `nil` または `just` で表す型を定義する。 | 参照あり |
| [`std::data::range`](./core#std-data-range) | 上限や下限の有無を持つ整数 range を表し、その値を fold する。 | 参照あり |
| [`std::data::result`](./result) | 成功と失敗を値で表し、map、chain、fallback の操作を提供する。 | 参照あり |

## Text module

| Module | 役割 | 文書 |
| --- | --- | --- |
| [`std::text::bytes`](./text#std-text-bytes) | byte 長、比較、連結、index、slice、UTF-8 `prefix` の decode を提供する。 | 参照あり |
| [`std::text::char`](./text#std-text-char) | char の比較、文字列化、空白、句読点、word の分類を提供する。 | 参照あり |
| [`std::text::config`](./text#std-text-config) | 暫定の section 付き key/value config を parse し、値や入力ファイルを読み取る。 | **暫定** |
| `std::text::parse` | string match の読み取り、検索、編集、置換に使う effect ベースの parser combinator API を提供する。 | 未文書化 |
| [`std::text::path`](./text#std-text-path) | `path` と `bytes` を相互に変換し、lossy UTF-8 decode によって `path` を表示する。 | 参照あり |
| [`std::text::str`](./str) | 文字位置による index、slice、検索、変換、可変な line view を提供する。 | 参照あり |
| `std::text::yumark` | Yumark document algebra を定義し、HTML node または Markdown へ描画する。 | 未文書化 |

## I/O module

| Module | 役割 | 文書 |
| --- | --- | --- |
| [`std::io::console`](./core#std-io-console) | stdout と stderr への出力、warning effect、終了 effect を提供する。 | 参照あり |
| [`std::io::file`](./fs) | text file の読み書き、metadata、scope 付き編集、host-backed buffer を提供する。 | 参照あり |
| `std::io::net` | host-backed listener、server request の受付、bytes response を提供する。 | **暫定** |

## 数値と primitive の module

| Module | 役割 | 文書 |
| --- | --- | --- |
| [`std::bool`](./num#std-bool) | `bool` の等値比較、否定、文字列化を提供する。 | 参照あり |
| [`std::float`](./num#std-float) | `float` の比較、算術、文字列化 `primitive` を提供する。 | 参照あり |
| [`std::int`](./num#std-int) | `int` の比較、算術、除算、剰余、10 進と 16 進の文字列化 `primitive` を提供する。 | 参照あり |
| [`std::num`](./num#std-num) | 算術と 16 進表示の `role` と標準 `impl` を定義し、child `module` の `frac` を宣言する。 | 参照あり |
| [`std::num::frac`](./num#std-num-frac) | 正規化した有理数の算術、比較、`float` 変換、文字列化を提供する。 | 参照あり |

## 補助 module

| Module | 役割 | 文書 |
| --- | --- | --- |
| [`std::testing`](./testing) | lazy な assertion 演算子と assertion effect を定義する。 | 参照あり |
| [`std::time`](./time) | instant、duration、clock、単位 constructor、算術、比較、書式化を提供する。 | 参照あり |
