# レコードリテラル直後のメソッド呼び出しが解決しない

発見日: 2026-07-26
状態: **結論済み（2026-07-27）。診断は修正、結合は現状維持がユーザ判断**
発見経緯: `derives` の DERIVE-D / DERIVE-E を手で動作確認しているときに 2 回踏んだ。
derives とは無関係で、既存の挙動である。

## 症状

レコードリテラルの直後にメソッドを続けると、role 実装が見つからないと言われる。

```yu
struct point { x: int, y: int } derives Eq

point { x: 1, y: 2 }.eq point { x: 1, y: 2 }
```

```console
compile error [yulang.unresolved-method]: no role implementation satisfies this method call
    --> line 3, column 22
  detail: no role implementation satisfies this method call for receiver
          {x: int, y: int} -> {x: int, y: int} -> bool
```

`Debug` でも同じ。

```yu
struct inner { v: int } derives Debug
struct outer { name: str, part: inner } derives Debug

outer { name: "a", part: inner { v: 1 } }.debug
```

```console
  detail: ... for receiver {name: std::text::str::str, part: inner} -> std::text::str::str
```

## 束縛を挟めば通る

```yu
my o = outer { name: "a", part: inner { v: 1 } }
o.debug            -- "outer { name: \"a\", part: inner { v: 1 } }"
```

`==` 演算子も通る。

```yu
point { x: 1, y: 2 } == point { x: 1, y: 2 }    -- true
```

したがって導出された impl 自体は正しく、レコードリテラルとメソッド呼び出しの
結合のしかたの問題である。

## 診断そのものにも誤りがある

`detail` が「receiver」として表示しているのは、**受信者の型ではなくメソッドの型**である。

- 1 例目の受信者は `{x: int, y: int}` だが、表示は `{x: int, y: int} -> {x: int, y: int} -> bool`
- 2 例目の受信者は `{name: str, part: inner}` だが、表示は `{name: str, part: inner} -> str`

どちらも `Eq.eq` / `Debug.debug` のメソッド型をそのまま出している。
受信者の型が読めないので、利用者はどこが悪いのか判断できない。

hint の `add or import an impl for the receiver type` も、この場合は誤った助言になる。
impl は存在していて、解決に失敗しているのは別の理由である。

## 着手前に確認すること

- レコードリテラル直後の `.method` が、どの段階で受信者を取り違えるか。
  パーサの結合か、lowering のメソッド解決か。
- `==` が通るのに `.eq` が通らない差はどこか。演算子経由と直接のメソッド呼び出しで
  受信者の決まり方が違うのか。
- `detail` に渡している型が受信者ではなくメソッドである件は、この構文に固有か、
  `yulang.unresolved-method` 全体の問題か。後者なら影響範囲は広い。
- 他のリテラル（tuple、list、string）でも同じか。レコードに固有か。

## 関連

- `notes/design/2026-07-26-derives-clause-design.md`（この確認の対象だった機能。本件とは独立）

## 結論 2026-07-27

二つの独立した問題に分かれた。片方は修正し、片方は現状維持をユーザが決定した。

### 1. 診断の誤り — 修正した

**この構文に固有ではなく、role メソッドの未解決診断すべてに効いていた。**
`RoleMethodCheckOutcome.receiver` に入るのが `use_.method_ty`——メソッド自身の型だった
（`crates/specialize/src/specialize2/task_solver/finish.rs:53`, `:61`, `:100`）。
production の formatter 経路は1本しかないので
（`crates/yulang/src/source/mod.rs:4300`）、全ての role メソッド解決失敗が影響していた。

| | 変更前 | 変更後 |
|---|---|---|
| レコードリテラル | `{x: int, y: int} -> {x: int, y: int} -> bool` | `{x: int, y: int}` |
| `1.foo`（impl 無し） | `int -> int` | `int` |

`1.foo` が壊れていたことが、この問題が構文固有でなかったことを示している。
メソッド型の表示は落とした。受信者が正しくなれば、失敗の説明にならないため。

hint（`add or import an impl for the receiver type`）は現状維持。
「候補 impl が無い」と「候補はあるが適合しない／受信者を取り違えた」を区別するには、
表示中の受信者と role 候補の適合性を結ぶ検証済みの情報が要る。現在の resolution payload は
メソッド署名の解決結果しか持たない（`crates/specialize/src/lib.rs:48`）。
**データが支えられない区別を診断に発明しない。**

### 2. 結合規則 — 現状維持（ユーザ判断）

原因は resolution ではなく parse の結合だった。CST が示すとおり:

```text
point { x: 1, y: 2 }.eq   →   point ({ x: 1, y: 2 }.eq)
```

`.eq` は `point` の適用結果ではなく、`point` の ML 引数である brace group の中に付く。

**曖昧さは実在する。** Yulang の `{...}` はレコード構築専用の構文ではなく、一般の
brace 文ブロックである（`crates/parser/src/expr/core.rs:110`）。したがって
`point { x: 1 }.eq` は「`point` にブロックを適用」とも「構築結果を選択」とも読める。
parser のバグではない。

他のリテラル受信者（tuple / list / string / 括弧）はいずれも正しく動く。
問題は「識別子 + 空白 + brace 引数」という形に固有。

**ユーザ判断: 現状のまま、括弧を明示形とする。**

```yu
(point { x: 1, y: 2 }).eq (point { x: 1, y: 2 })   -- これが正しい書き方
```

既存の regression も括弧付きで書いている
（`tests/yulang/regressions/runtime/derive_debug_structural.yu:17`）。
専用のレコード構築構文を導入する案と、後置演算子の優先度を変える案は、
いずれも `f { block }.field` の既存の意味を裁定する必要があり、
得られるものに対して波及が大きいため採らない。

診断の受信者が正しくなったことで、この形を踏んだときに何が起きているかは
以前より読めるようになっている。
