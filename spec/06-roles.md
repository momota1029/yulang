# 章6 role・method・cast

状態の凡例は [README](README.md)。この章は `role` / `impl` / `where`、`x.method` の解決、`cast` を扱う。
role の解決アルゴリズム（不変区間規則、level 管理、関連型の再帰的な解決）は仕様ではなく核の計算体系（Lean）の側で扱う。ここは利用者から見える意味だけ。

## 6.1 `role`　〔仮採用〕

```yulang
role Add 'a:
    our a.add: 'a -> 'a

role Index 'container 'key:
    type value
    our container.index: 'key -> value
```

- `role` は、型が実装できる method と、associated type（`type value`）の集まり。associated type は、role 側に default（`type value = char`）がなければ `impl` で必ず `type value = ...` と指定する。default があれば省略できる（確定, 2026-11-04）。型引数を複数持てる。
- method header `our a.add: ...` の `a` は、実装対象の型の値（receiver）を表す。
- method は default の本体を持てる（確定, 2026-11-04）。`impl` が書かなければ default が使われ、書けば上書きする。本体のない method（型 signature だけ）は `impl` が必ず書く。

```yulang
role Eq 'a:
    our a.eq: 'a -> bool
    our a.ne b = not (a.eq b)          // default の本体

impl Eq int:
    our x.eq y = ...                   // ne は書かない
```

- `role` も companion module を作る。

出典: `main:web/docs/ja/reference/structs.md` §Role

## 6.2 `impl`　〔曖昧時の扱いは確定、他は仮採用〕

```yulang
impl Add int:
    our x.add y = std::int::add x y

impl Index str int:
    type value = char
    our s.index i = std::text::str::index_raw s i
```

- `impl` は具体的な型にも、型引数を持つ一般的な型（`impl Display (list 'a)`）にも、一部の型引数だけを決めた型（`impl Display (list int)`）にも書ける（確定, 2026-11-04）。候補が重なれば曖昧エラー、重ならなければ共存する。
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
- 同じ role と型に対して複数の `impl` が候補になる場合は**曖昧**として拒否される（確定, 2026-11-04）。

出典: `main:web/docs/ja/reference/structs.md` §impl、`main:spec/2026-06-04-method-selection.md` §impl候補の有効範囲

## 6.3 `where`　〔仮採用〕

```yulang
my twice(x: 'a) =
    where 'a: Add
    x.add x
```

- `where` は型変数に role の制約を付ける。binding・`role`・`impl` の body の中に書ける。`act` の operation の署名にも、署名の下に `where` を書ける（確定, 2026-11-05）。
- **`where` は書かなくても、未解決の role 制約が型に自動で付く**（確定, 2026-11-05）。`my twice(x) = x.add x` は `'a -> 'a where 'a: Add` と推論される。`x` の型が分からないまま現れた role の method は、その制約を残したまま進み、一般化のとき、環境由来でない型変数に付いた制約を型に持ち上げる。使う側で型変数が決まるたびに、その制約の解決が走る（`twice 1` なら `Add int`）。hover にも `where` が出る。
- **関連型は、新しい型変数と等式で表す**（確定, 2026-11-05）。`my first(c) = c.index 0` の型は、戻り値に型の射影（`'c::value` のような式）を書かず、新しい型変数 `'v` を置いて、制約の側に関連型の等式を持たせる。

  ```text
  first : 'c -> 'v where 'c: Index(int, value = 'v)
  ```

  `'c` が決まって `impl` が選ばれたとき、その `impl` の `type value = ...` が `'v` に代入される。型はいつも「変数＋制約」の形で、型の等価判定に関連型の簡約を持ち込まない。表記は旧版（`main:spec/2026-06-06-syntax-design.md`）の dump 表示 `Index(key, value = item)` に合わせる（暫定。通常引数を括弧に入れるか、`impl Index str int` のように並べるかは章7で決める）。
- **関連型の変数は普通の型変数で、等式は先に束縛しない**（確定, 2026-11-05）。`'v` には、`'c` が決まる前でも他の型との一致の制約が積まれる（上の `first xs` の結果を `str` として使えば `'v ≥ …` / `'v ≤ str` が積まれる）。`impl` が選ばれて `type value = ...` が分かったとき、等式 `'v = value` の制約が足されて、それまでに積まれた制約と合わなければ、その時点で型エラーになる。`'v` に関連型専用の規則はない。
- **一般化できない束縛に残った未解決の role 制約は、同じファイル（module）の終わりまで待つ**（確定, 2026-11-05）。`my z = default ()` のように値でない束縛は一般化されず、`'a: Default` は単相の変数のまま残る。同じファイルの使い方で決まればそれでよく、ファイルの終わりでも決まらなければ、その時点でエラーにする（どの型の `Default` か決まらない）。決まっていない型変数は、ファイルの境界を越えて公開されない。
- **`impl` の `where` は、head より構造的に小さくなければならない**（確定, 2026-11-05）。`impl` の `where` に書く各条件 `C t₁ … tₙ` は、次の二つを満たす。満たさない `impl` は宣言時に拒否される。解決の深さに上限は置かない。
  1. 条件の型の大きさの合計が、`impl` の head の型の大きさの合計より**真に小さい**（型構築子と型変数を一個ずつ数える）。
  2. どの型変数も、条件の中での出現回数が head の中での出現回数を超えない。

  ```yulang
  impl Display (list 'a):
      where 'a: Display          // 良い: 'a は list 'a より小さい。list (list int) → list int → int と降りて止まる

  impl Foo 'a:
      where (list 'a): Foo       // 拒否: 条件のほうが大きい。Foo int → Foo (list int) → ... と終わらない
  ```

  この条件のもとで、role の解決は必ず停止する。
- **`impl` の `type name = ...` の右辺は、他の role の associated type を参照できない**（確定, 2026-11-05）。右辺に書けるのは具体的な型・型構築子・その `impl` の head に現れる型変数だけで、associated type は head の型引数から決まる一つの型になる。解決の途中で別の associated type を展開する必要は生じない。他の role の associated type を右辺で引ける構文は、必要が出てから足す。
- `role` の body の `where` は、その role の method に継承される。`impl` の body の `where` は、その `impl` が候補になるための前提になる。

## 6.4 `x.method` の解決　〔確定〕

`x.method` は、すぐには解決されない。**`x` の型の下界が分かって、その型に `.method` があるとき**に初めて解決される。

```yulang
x.add y
```

- 候補の探し方は、まず receiver の型に結びついた field と、`with:` で定義した method。次に role の method と effect 行の method。
  **この順序は仕様**で、同じ名前が複数の段にあるときは**この順で先に見つかったものが選ばれる**（確定, 2026-11-04）。
- `x` が `ref 'e 'a` なら、`'a` に対して同じ探し方をする。
- **receiver の型が union のとき**（確定, 2026-11-05）。union のメンバーのうち、その method を**持つ型が一つだけ**なら、その型の method に決まる。決まったら、receiver はその method の receiver 型への**普通の cast 境界**として扱われる（章6.5）。他のメンバーはその型へ cast され、規則がなければ「暗黙の cast が見つからない」エラーになる。method を持つメンバーが**二つ以上**あれば曖昧エラーで、利用者に型の注釈を入れさせる（メンバーの並び順では選ばない）。

  ```yulang
  my x = if c: 1 else: user_id_value     // int | user_id
  x.add 2                                 // Add を持つのは int だけ → int の add に決まり、user_id 側は int へ cast
  x.show                                  // int にも user_id にも show がある → 曖昧エラー
  (x: int).show                           // 注釈で期待型を与える。user_id 側が int へ cast される
  ```

- method が解決されるまで、それを含む SCC は解かれない。
- SCC がこれ以上変化しなくなったとき、解決していない method は、role の method か record の field として解釈される（確定, 2026-11-04）。

出典: `main:spec/2026-06-04-method-selection.md`、`main:web/docs/ja/reference/modules.md` §Dot selection

## 6.5 `cast`　〔境界と合流は確定、他は仮採用〕

```yulang
struct user_id { raw: int }

cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }
```

- `cast(x: A): B = body` は、`A` から `B` への**暗黙の変換規則**を登録する。
- `cast` は他の module の型どうしにも書ける（確定, 2026-11-04）。有効になるのは、その `cast` が `use` で見える範囲だけ（D6 の method と同じ規則）。同じ `A → B` が複数見えたら曖昧エラー。
- 推論された値の型と、既知の期待型がぶつかる境界で、登録された規則が適用される。

```yulang
my id: user_id = 1          // int → user_id
my back: int = id           // user_id → int
my use_int(n: int) = n + 1
use_int id                  // 引数の境界で int に変換される
```

- cast が入るのは、**期待型が分かっている境界**: binding や引数の注釈、関数の引数。
- **分岐の合流**（`if` / `case` の arm、effect arm の結果）で型が違うときは、cast を入れず**union として一度持つ**（確定, 2026-11-04）。
  その後で期待型が現れたら、その型へ cast される。何も期待されていなければ、**曖昧さを警告する**（エラーではない）。

```yulang
my x = if c: 1 else: user_id_value     // int | user_id の union。どちらの型になるかはここでは決まらない
my n: int = x                           // 期待型 int が来たので、user_id の側が int に cast される
my y = x                                // 何も期待されていない → 曖昧さの警告
```

- union の値に期待型が来たとき、各メンバーを別々に扱う。期待型と同じメンバーはそのまま通り、違うメンバーはその型への cast を探す。**一つでも cast が見つからないメンバーがあれば、型エラーにする**（暗黙の cast が見つからない。実行時に失敗させる扱いはしない。確定, 2026-11-05）。

```yulang
my y = if c: 1 else: "text"            // int | str
use_int y                               // エラー: str から int への暗黙の cast が見つからない
```

- 変換の定義を変にするほうが悪い、という立場。合流は許し、どちらに寄るかは期待型に任せる。
- **期待型のない裸の式では変換されない。** `id` だけなら `user_id` のまま。
- 該当する規則がなければ「暗黙の cast が見つからない」エラー。一致する規則が複数あれば ambiguous で拒否される（Yulang は勝手に選ばない）。
- cast は遅延しない。境界に着いた時点で body が走る。重い変換は普通の関数にして、呼び出しを明示する。
- **cast は関数の型の内側にも通る**（確定, 2026-11-05）。期待される関数型 `A' -> B'` に、値の関数型 `A -> B` が cast で合うとき（`A'` から `A` へ、`B` から `B'` へそれぞれ cast できるとき）、関数は包み直される。引数側は反変、戻り値側は共変に cast が入る。包み直しは境界に着いた時点で作られ、中の cast は呼び出しのたびに走る。

```yulang
my apply_to_id(f: user_id -> int) = f id_value
my inc(n: int) = n + 1
apply_to_id inc            // OK: inc : int -> int は、引数側に user_id → int の cast が入った関数として渡る
```

- **cast は、方向を持つ位置に沿って通る**（確定, 2026-11-05）。関数の引数（反変）・戻り値（共変）に加えて、tuple の成分・record のフィールド・variant の payload（いずれも共変）にも通る。通るときは成分ごとに cast して、新しい値を作る。変換の量は型の大きさで決まり、データの大きさには依らない。

```yulang
my p = (id_value, "a")            // (user_id, str)
my q: (int, str) = p              // 成分ごとに cast: (int, str)
```

- **nominal な型の型引数（`list 'a`・`ref`・`box 'a` など）は不変で、cast も通らない**（確定, 2026-11-05）。不変な引数は `(lower, upper)` の区間として持ち、実際の引数は一つの型に決まる。すでに型が決まった `list user_id` は `list int` の場所には渡せない。
- **配列（list）の literal の要素型は `int | '_a` のように、後で決まる部分を持つ**（確定, 2026-11-05）。`'_a` は値制限で一般化されない弱多相の変数で、後の使い方で決まる。`my e = []` の `'a` が後で決まるのと同じ仕組み。`'_a` が決まったとき、literal の要素は**構築位置に遡って**、その型への境界として cast される。literal の各要素は、`'_a` が決まるまで保留された境界を持つ。

```yulang
my xs = [1]                    // list (int | '_a)。'_a は弱多相
my ys: list user_id = xs       // '_a := user_id。要素 1 に int → user_id の cast が入り、xs は list user_id として作られる
```

  - 同じファイルの終わりまでに `'_a` が決まらなければ、cast なしで要素の型の合流（上の例では `int`）に決まる（章6.3の、ファイルの終わりまで待つ規則と同じ）。
  - 値を作る場所以外（すでに型が決まった `list user_id` の値）では、中身は cast されない。
- 現状の対象は nominal な型どうしと、それを引数・戻り値に持つ関数型。汎用の構造的変換の仕組みではない。
- **cast は連鎖する**（`A → B → C`, 確定, 2026-11-04）。
  連鎖の経路が複数ある場合は、**どれを選んでもよい**（どの経路が選ばれるかは仕様が決めない。プログラムはそれに頼ってはならない）。
  連鎖の深さに制限はない（確定, 2026-11-04）。
- **cast は、型が合わないときにだけ探す**（確定, 2026-11-05）。期待型と値の型が既に合っていれば、cast の規則があっても適用しない。明示された cast 規則がなければ、無理に変換しない。連鎖は各位置（関数の引数・戻り値、tuple の成分など）で独立に探す。
- 同じ `A → B` を直接与える規則が複数ある場合は、上のとおり ambiguous で拒否される。連鎖の経路が複数ある場合とは扱いが違う。

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
同じ名前は意図的で、変える予定はない（確定, 2026-11-04）。

## 確認してほしい点

なし（I1〜I6 は反映済み。J4 で cast の有効範囲を確定）。
