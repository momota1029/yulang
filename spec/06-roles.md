# 章6 role・method・cast

状態の凡例は [README](README.md)。この章は `role` / `impl` / `where`、`x.method` の解決、`cast` を扱う。
role の解決アルゴリズム（不変区間規則、level 管理、関連型の再帰的な解決）は仕様ではなく核の計算体系（Lean）の側で扱う。ここは利用者から見える意味だけ。

## 6.1 `role`　〔要確認〕

```yulang
role Add 'a:
    our a.add: 'a -> 'a

role Index 'container 'key:
    type value
    our container.index: 'key -> value
```

- `role` は、型が実装できる method と、省略可能な associated type（`type value`）の集まり。型引数を複数持てる。
- method header `our a.add: ...` の `a` は、実装対象の型の値（receiver）を表す。
- method は default の本体を持てる。
- `role` も companion module を作る。

出典: `main:web/docs/ja/reference/structs.md` §Role

## 6.2 `impl`　〔要確認〕

```yulang
impl Add int:
    our x.add y = std::int::add x y

impl Index str int:
    type value = char
    our s.index i = std::text::str::index_raw s i
```

- role 名の直後の型が最初の型引数を埋め、後ろの型が残りを埋める。
- `impl` の中の `our` が候補として公開される。`my` は `impl` の中の helper。
- 足りない method、role にない method は検査で報告される。
- `struct` の `with:` の中にも `impl` を書ける。その場合、外側の struct が role の最初の型引数として前に足される。

```yulang
struct box 'a { value: 'a } with:
    impl Index int:
        type value = 'a
        our b.index i = b.value
```

- **`impl` は、それを含むファイルが読み込まれたときにだけ候補になる。** 読み込まれていないファイルの `impl` は、method 選択にも role の解決にも入らない。
  読み込まれた後の可視性は、通常の module の可視性（`my` / `our` / `pub`）に従う。

出典: `main:web/docs/ja/reference/structs.md` §impl、`main:spec/2026-06-04-method-selection.md` §impl候補の有効範囲

## 6.3 `where`　〔要確認〕

```yulang
my twice(x: 'a) =
    where 'a: Add
    x.add x
```

- `where` は型変数に role の制約を付ける。binding・`role`・`impl` の body の中に書ける。
- `role` の body の `where` は、その role の method に継承される。`impl` の body の `where` は、その `impl` が候補になるための前提になる。

## 6.4 `x.method` の解決　〔要確認〕

`x.method` は、すぐには解決されない。**`x` の型の下界が分かって、その型に `.method` があるとき**に初めて解決される。

```yulang
x.add y
```

- 候補の探し方は、まず receiver の型に結びついた field と、`with:` で定義した method。次に role の method と effect 行の method。
- `x` が `ref 'e 'a` なら、`'a` に対して同じ探し方をする。
- method が解決されるまで、それを含む SCC は解かれない。
- SCC がこれ以上変化しなくなったとき、解決していない method は、role の method か record の field として解釈される。

出典: `main:spec/2026-06-04-method-selection.md`、`main:web/docs/ja/reference/modules.md` §Dot selection

## 6.5 `cast`　〔要確認〕

```yulang
struct user_id { raw: int }

cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }
```

- `cast(x: A): B = body` は、`A` から `B` への**暗黙の変換規則**を登録する。
- 推論された値の型と、既知の期待型がぶつかる境界で、登録された規則が適用される。

```yulang
my id: user_id = 1          // int → user_id
my back: int = id           // user_id → int
my use_int(n: int) = n + 1
use_int id                  // 引数の境界で int に変換される
```

- 適用される境界: binding や引数の注釈、関数の引数、分岐の合流（2 つの arm が同じ型に揃う場所）、effect arm の結果型。
- **期待型のない裸の式では変換されない。** `id` だけなら `user_id` のまま。
- 該当する規則がなければ「暗黙の cast が見つからない」エラー。一致する規則が複数あれば ambiguous で拒否される（Yulang は勝手に選ばない）。
- cast は遅延しない。境界に着いた時点で body が走る。重い変換は普通の関数にして、呼び出しを明示する。
- 現状の対象は nominal な型どうし。汎用の構造的変換の仕組みではない。

### `from` 付き variant

```yulang
enum app_err:
    path from path_err
    parse from parse_err
```

- variant に `from` を付けると、variant そのもの（`app_err::path` が `path_err` を包む）と、`path_err` から `app_err` への変換規則が作られる。
- payload は 1 つ、source と target はどちらも nominal でなければならない。
- `error` 宣言の `from` は、`wrap` と `up` も広げて、狭いエラーを同時に捕まえるようにする。

出典: `main:web/docs/ja/reference/casts.md`

### 注意: `cast` 宣言と `Cast` role は別物

標準ライブラリには `.cast` method を持つ `std::core::convert::Cast` という role があるが、`cast` 宣言はこの role を**実装しない**し、呼びもしない（罠 T6）。

## 確認してほしい点

- **I1** `impl` の候補は、読み込まれたファイルのものだけ、で仕様としてよいか。同じ role と型に対して複数の `impl` が読み込まれた場合は、エラーか、曖昧として拒否か。
- **I2** `x.method` の探す順（struct の field と `with:` の method → role → effect 行）は仕様か。同じ名前が複数の段にあるときの優先は。
- **I3** 解決できなかった method を「role か field とみなす」最終段の規則は、仕様として書いてよいか。
- **I4** 暗黙の cast は、連鎖する（`A → B → C`）か。しないなら、仕様として「しない」と書く。
- **I5** `cast` 宣言と `Cast` role を同じ名前にしているのは意図か。罠として載せたが、名前を変える予定があるか。
