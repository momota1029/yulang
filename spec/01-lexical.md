# 章1 字句・layout・演算子

状態の凡例は [README](README.md)。この章は短くして、**確認してほしい点を最後にまとめた**。
構文木の形（CST）は `syntax-reference/` が扱うので、ここでは「利用者から見える意味」だけを書く。

## 1.1 ソースと識別子　〔識別子の大小は確定、他は仮採用〕

- ソースファイルは UTF-8 のテキストで、1ファイルが1つの module になる。
- 識別子は大文字と小文字を**区別する**が、どちらで書くかは**強制されない**（Linux のファイル名と同じ）。
  標準ライブラリと慣習では小文字で書く（型名・module 名も含む）。
- 型変数は `'a`、effect 行の変数は `'b` のように `'` で始める。
- `$a` は参照 `a` の読み出し、`&a = value` は更新（State は純粋な継続スレッディング）。

出典: ユーザーの言語設計メモ（memory）、`main:docs/language/overview.ja.md` §block と binding

## 1.2 コメント　〔仮採用〕

```yulang
// 行コメント（確定）
/* block コメント（確定。入れ子にできる） */
-- 行 doc（doc token）

---
block doc。中身は Yumark として読まれる
---
```

- `//` 相当の通常コメントと、doc として扱われるコメントがある。
- doc コメントは構文上の要素であり、型推論や実行には効かない。

通常の行コメントの綴りは `//`、block コメントは `/* ... */`（確定, 2026-11-04）。block コメントは入れ子にできる（確定, 2026-11-04。旧パーサも同じ）。`--` / `---` の doc コメントの付き先は次のとおり（確定, 2026-11-04）。

```yulang
-- ① 直前の行: 次の宣言の doc
my f x = x

my g x = x   -- ② 同じ行の末尾: この宣言の doc

my h x =     -- ③ `=` の直後: この宣言の doc
    x + 1
```

- 付き先は宣言と、そのメンバー（struct の field、enum の variant、role の method、act の operation）に限る。
- ①は直前の行。②③は「その行で始まった宣言」に後ろ向きに付く。`---` ブロックは①の位置だけ。
- 宣言の外（引数の途中、式の中、演算子の隣など）の `--` は doc にならず、独立コメントのまま。
- ①と②③を両方書いたら、どちらも残して連結する。
- 実 parser は今、①だけを実装している。②③とメンバーへの付与は未実装（parser の穴として `spec/parser-gaps.md` に起票する）。

出典: `main:notes/design/yulang-language-report.md` §4.2

## 1.3 ブロックと layout　〔字下げ継続は確定、他は仮採用〕

ブロックは、インデント（`:` で始める）と波括弧の両方で書ける。意味は同じ。

```yulang
if cond:
    a
else:
    b

if cond { a } else { b }
```

- 改行は文の区切りになる。波括弧や括弧の中では `;` や `,` も文脈によって区切りになる。
- **次の行の字下げが基準より深ければ、前の式の続き。同じか浅ければ、新しい文**（確定, 2026-11-04）。

```yulang
f x
    y         // 字下げが深い → 同じ式の続き。f x y（y は 3 つ目の引数）

f x
y             // 字下げが同じ → 新しい文

xs
    .map f    // 字下げが深い → xs.map f
```

- 長い application は、続きの行を深く字下げして複数行に折れる。`:` や `{}` は必須ではない。
- 括弧の中では、基準は開き括弧の直後の行の字下げ。基準より深い改行は現在の項目の続きで、基準以下の改行は次の項目の区切りになる。

出典: `main:notes/design/yulang-language-report.md` §4.3、`syntax-reference/ja/src/cross-cutting/layout-aware-separator-authority.md`
注意: `main:web/docs/ja/guide/pitfalls.md` の「改行で裸 application は閉じる」は、この規則と逆のことを書いており、古い。起こし直すときに採らない。

## 1.4 呼び出しの 3 つの形　〔仮採用〕

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

## 1.5 演算子は宣言で決まる　〔仮採用〕

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

## 1.6 予約語　〔大別は確定〕

予約語は固定の一覧ではなく、**文脈ごとに見える**。大きく 2 つに分かれる（確定, 2026-11-04）。

1. **文頭予約語** — 文の先頭に現れて、その文の種類を決める語。
2. **式中予約語** — 式の途中に現れて、式の形を決める語。

本当に文脈に依存するのは `else` / `elsif` で、直前の `if` に対応するときだけ予約語として見える。
これは分類ではなく、個別の例外的な場合である。

実装が文の先頭で見ている語の例: `use`, `my`, `mod`, `struct`, `enum`, `error`, `type`, `role`, `impl`, `cast`, `act`, `for`,
および演算子宣言の `prefix` / `infix` / `suffix` / `nullfix`。
どの語がどちらに入るかの表は、章3 で式を書くときに作る。

## 確認してほしい点

なし（C1〜C4 は反映済み）。章1の要確認は 1.1・1.3〜1.5 の細部のみ。
