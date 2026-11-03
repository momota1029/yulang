# 章1 字句・layout・演算子

状態の凡例は [README](README.md)。この章は短くして、**確認してほしい点を最後にまとめた**。
構文木の形（CST）は `syntax-reference/` が扱うので、ここでは「利用者から見える意味」だけを書く。

## 1.1 ソースと識別子　〔要確認〕

- ソースファイルは UTF-8 のテキストで、1ファイルが1つの module になる。
- 識別子は小文字で書く（型名・module 名も含む）。型変数は `'a`、effect 行の変数も `'b` のように `'` で始める。
- `$a` は参照 `a` の読み出し、`&a = value` は更新（State は純粋な継続スレッディング）。

出典: ユーザーの言語設計メモ（memory）、`main:docs/language/overview.ja.md` §block と binding

## 1.2 コメント　〔要確認〕

```yulang
// 行コメント
-- 行 doc（doc token）

---
block doc。中身は Yumark として読まれる
---
```

- `//` 相当の通常コメントと、doc として扱われるコメントがある。block コメントは入れ子にできる。
- doc コメントは構文上の要素であり、型推論や実行には効かない。

出典: `main:notes/design/yulang-language-report.md` §4.2
注意: 出典の記述では通常コメントの綴りが確認できなかった。**綴りはあなたに確認したい**（確認 C1）。

## 1.3 ブロックと layout　〔要確認〕

ブロックは、インデント（`:` で始める）と波括弧の両方で書ける。意味は同じ。

```yulang
if cond:
    a
else:
    b

if cond { a } else { b }
```

- 改行は文の区切りになる。波括弧の中では `;` や `,` も文脈によって区切りになる。
- 改行は**裸の application を閉じる**。次の行は新しい文になる。続けたいなら、字下げして継続式にするか、`:` / `{}` を使う。

```yulang
f x y        // 1 つの文

f x
    y        // 2 つの文: `f x` と `y`（裸 application は改行で閉じる）
```

出典: `main:web/docs/ja/guide/pitfalls.md`「改行で裸 application は閉じる」、`main:notes/design/yulang-language-report.md` §4.3

## 1.4 呼び出しの 3 つの形　〔要確認〕

見た目が似ていて、別の構文として読まれる。

```yulang
f(x)    // 呼び出し
f (x)   // f を「グループ化された式 x」に裸 application
f: x    // colon application（`:` の後ろ全体が引数）
```

- `f x: body` は `f x (body)` に近い。`(f x:) body` ではない。
- ML 風の引数の中では、dot の前の空白が効く。

```yulang
f xs.map      // f (xs.map)
f xs .map     // (f xs).map
```

出典: `main:web/docs/ja/guide/pitfalls.md`、`main:web/docs/ja/reference/syntax-style.md`

## 1.5 演算子は宣言で決まる　〔要確認〕

演算子はパーサに固定されていない。`nullfix` / `prefix` / `infix` / `suffix` の宣言で作り、
**その宣言を import したファイルだけ**が、その演算子を読める。

```yulang
pub prefix(not) 8.0.0 = std::bool::not
pub infix (+) 5.0.0 5.0.1 = \x -> \y -> x.add y
pub suffix (..) 8.0.0 = std::data::range::from_included
```

- 結合力は `5.0.0` のような dot 区切りの数で書く。大きいほど強く結合する。
- infix は左右の結合力の組を持ち、左右を非対称にすると結合方向が決まる（`5.0.0 5.0.1` は左結合）。
- `lazy infix` の本体は、両辺を thunk（`() -> value`）として受け取る。`and` / `or` の短絡評価はこれで実現する。
- 標準の演算子表（`+`, `==`, `and` など）は std の prelude が定義する。**言語そのものではなく標準ライブラリの章で扱う**。

出典: `main:web/docs/ja/reference/operators.md`

## 確認してほしい点

- **C1** 通常の行コメントの綴りは何か。（`//` なのか、`--` は doc だけなのか）
- **C2** keyword は固定の一覧として仕様に載せるか。実装は文脈ごとに語を見ていて、一覧を持たない。
  載せるなら、予約語として使えない語（`my`, `our`, `pub`, `use`, `case`, `catch`, `do`, `if`, `else`, `elsif`, `for`, `in`, `with`, `where`, `mod`, `type`, `struct`, `enum`, `role`, `impl`, `act`, `cast`, `as`, `via`, `mark` など）の確定版が要る。
- **C3** 結合力の数値（`8.0.0` など）は仕様の一部か、prelude の実装詳細か。
  main の 2 つの文書で食い違っていた（報告書は `not` を `70`、リファレンスは `8.0.0`）。後者が新しいと見ている。
- **C4** 識別子は「全て小文字」でよいか。型変数・effect 行変数の `'` 以外に、大文字を許す場所があるか。
