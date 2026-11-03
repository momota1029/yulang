# 章1 字句・layout・演算子

状態の凡例は [README](README.md)。この章は短くして、**確認してほしい点を最後にまとめた**。
構文木の形（CST）は `syntax-reference/` が扱うので、ここでは「利用者から見える意味」だけを書く。

## 1.1 ソースと識別子　〔識別子の大小は確定、他は要確認〕

- ソースファイルは UTF-8 のテキストで、1ファイルが1つの module になる。
- 識別子は大文字と小文字を**区別する**が、どちらで書くかは**強制されない**（Linux のファイル名と同じ）。
  標準ライブラリと慣習では小文字で書く（型名・module 名も含む）。
- 型変数は `'a`、effect 行の変数は `'b` のように `'` で始める。
- `$a` は参照 `a` の読み出し、`&a = value` は更新（State は純粋な継続スレッディング）。

出典: ユーザーの言語設計メモ（memory）、`main:docs/language/overview.ja.md` §block と binding

## 1.2 コメント　〔要確認〕

```yulang
// 行コメント（確定）
-- 行 doc（doc token）

---
block doc。中身は Yumark として読まれる
---
```

- `//` 相当の通常コメントと、doc として扱われるコメントがある。block コメントは入れ子にできる。
- doc コメントは構文上の要素であり、型推論や実行には効かない。

通常の行コメントの綴りは `//`（確定, 2026-11-04）。block コメントの綴りと `--` / `---` の扱いは要確認。

出典: `main:notes/design/yulang-language-report.md` §4.2

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

- 結合力は `5.0.0` のような dot 区切りの数列で書く。大きいほど強く結合する。
  桁数は 3 つに固定されない。`70` は `70.0.0.0...` を表すので、短く書いても誤りではない。
  （main の古い文書の `not = 70` と新しい文書の `8.0.0` は別の値。新しい `8.0.0` を採る。確定）
- infix は左右の結合力の組を持ち、左右を非対称にすると結合方向が決まる（`5.0.0 5.0.1` は左結合）。
- `lazy infix` の本体は、両辺を thunk（`() -> value`）として受け取る。`and` / `or` の短絡評価はこれで実現する。
- 標準の演算子表（`+`, `==`, `and` など）は std の prelude が定義する。**言語そのものではなく標準ライブラリの章で扱う**。

出典: `main:web/docs/ja/reference/operators.md`

## 1.6 予約語　〔一部確定〕

予約語は固定の一覧ではなく、**文脈ごとに見える**。大きく 3 つに分かれる（確定, 2026-11-04）。

1. **文頭予約語** — 文の先頭に現れて、その文の種類を決める語。
2. **式中予約語** — 式の途中に現れて、式の形を決める語。
3. 〔3つ目: 未記入〕

実装が文の先頭で見ている語の例: `use`, `my`, `mod`, `struct`, `enum`, `error`, `type`, `role`, `impl`, `cast`, `act`, `for`,
および演算子宣言の `prefix` / `infix` / `suffix` / `nullfix`。
`if` に続く `elsif` / `else` は、直前の `if` に対応して見える語として扱われている。
どの語がどの分類に入るかは、分類を確認してから表にする。

## 確認してほしい点

- **C2'** 予約語の 3 分類のうち、3 つ目は何か。文頭・式中のほかに、`else` / `elsif` のような「対応する語に続いて見える語」がそれに当たるのか。
