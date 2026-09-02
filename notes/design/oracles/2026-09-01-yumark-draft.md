# 11. Yumark ドラフト

> ステータス: Draft

この文書は、Yulang 系の文書 Markup Language である **Yumark** の初期仕様メモです。
Yumark は Markdown 互換を目指すものではなく、文書を値として扱える **Markup Language** として設計します。

## 0. 位置づけ

- Yumark は単なる軽量記法（LML）ではなく、構造を明示できる文書 ML とする
- Markdown / CommonMark との完全互換は非目標
- ただし主要な inline 記法との実用的互換はできるだけ保つ
- Yulang の offside 感と `:` の本文捕捉規則をできるだけ共有する
- 計算は Yumark 独自式を持たず、`\ident(...)` 形で Yulang に委譲する
- Yumark と Yulang は共通 CST 上で扱う（相互埋め込みがあるため、最初から統合が前提）

## 1. 基本原則

- Yumark は文書データを表す
- 文書は値である
- 文書 inline の主軸として `[]` を使う
- Yulang 式や値引数は `\ident(...)` の形で受け取る
- fenced code block は doctest 等で使う生テキストであり、展開対象にしない
- 組み込み構文は最小限に絞る

## 2. ブロック構文

Yumark の主要ブロックは次のとおり。

- 見出し
- リスト
- fenced code block
- 引用ブロック
- 段落
- コマンドブロック

### 2.1 見出し

見出しは `#` によって始まる。

```yumark
# Heading
## Heading
```

`:` のない見出しは Markdown 風の暗黙 section を作る。
見出しの内容は、次の「同じレベル以上の見出し」が現れる直前まで続く。
ただし `#.` / `##.` / `###.` のような close 記法によって、対応する深さまでを明示的に閉じられる。

```yumark
# Intro

first paragraph
- item

## Detail
```

```yumark
# Intro

first paragraph

## Detail
detail paragraph
##.

back to intro
#.
```

見出しは `:` によって明示 section を導入できる。
この `:` は必ず改行を伴い、インデント本文を取る。

```yumark
# Intro:
  first paragraph
  - item
```

### 2.2 リスト

リストは Markdown 風のマーカーを持つ。

```yumark
- item
1. item
10. item
```

項目の本文開始位置よりも後ろに続く nonblank 行は、その項目の継続本文として扱う。
継続行がリストマーカーで始まる場合は子リストとみなす。

### 2.3 fenced code block

コードブロックは fenced code block のみを持つ。
インデントコードブロックは持たない。

````yumark
```rust
fn main() {}
```
````

### 2.4 引用ブロック

Yumark は2種類の引用記法を持つ。

**明示ブロック記法（推奨）**

`>>>` で開始し、`>>>` で閉じる。明示的な閉じを必須とする。

```yumark
>>>
quoted text
>>>
```

入れ子にするには `>>>>` のように `>` を重ねる（fenced code block の backtick と同様の方式）。

```yumark
>>>>
outer
>>>
inner
>>>
>>>>
```

**Markdown 互換記法**

行頭 `>` による Markdown 風の引用も認める。
入れ子は `>>` / `>>>` のように `>` を重ねる。

```yumark
> quoted line
> continued

>> nested quote
```

方針:

- 明示ブロック記法は Yumark ネイティブ。構造が明確でパーサが扱いやすい
- Markdown 互換記法は既存文書との互換用途。深い入れ子はこちらで表現する
- 2つの記法を混在させない

### 2.5 コマンドブロック

コマンドは `\ident` で始まる。
必要に応じて `(...)` で Yulang 引数を取り、`:` を使うと本文を取れる。

```yumark
\if(show_warning):
  \warning:
    long body
```

```yumark
\link("https://example.com"):
  OpenAI
```

## 3. `:` の本文捕捉

Yumark は Yulang と同様に `:` を「本文捕捉」や「文書作用」に使う。
ただし block と inline で役割を分ける。

### 3.1 block での `:`

block では `:` は本文導入として使う。

一般形:

```text
head ":" newline indented_body
```

規則:

- `head:` の直後には必ず改行が来る
- `head:` の直後にインデント本文を置ける
- 本文は dedent で終わる

この規則は少なくとも次に適用する。

- `# heading:`
- `\command:`
- `\if(...):`
- `\elsif(...):`
- `\else:`

### 3.2 inline での `:`

inline では `:` は左側の文書グループに文書作用子を適用する。

一般形:

```text
"[" doc "]" ":" ident
"[" doc "]" ":" ident "(" yulang_args? ")"
```

例:

```yumark
[important]:bold
[OpenAI]:link("https://openai.com")
[careful]:warning
```

ここで `[]` の中身は任意の inline `Doc` でよい。
改行は許されるが、空行を含んではならない。

## 4. インライン構文

### 4.1 文書グループ

`[ ... ]` は inline 文書グループである。
中には任意の inline `Doc` を置ける。

```yumark
[text]
[[nested]:bold]
```

規則:

- 改行は許される
- 空行は許されない
- 単独の `[doc]` も有効な inline group である
- 中には任意の inline `Doc` を置ける
- ただし block 構文は置けない
- すなわち paragraph の中に現れうる要素だけを `[doc]` 内に置ける

### 4.2 Markdown 互換リンク・画像

実用的互換のため、少なくとも次を認める。

```yumark
[OpenAI](https://openai.com)
![logo](logo.png)
```

規則:

- `[doc](dest)` は link として扱う
- `![alt](src)` は image として扱う
- `]` の直後に `(` が来たときだけ link / image になる
- `[]` 系の他構文との曖昧性は、直後の記号で分岐すればよい

### 4.3 文書作用

`[doc]:ident` と `[doc]:ident(...)` は inline 文書作用である。

```yumark
[text]:bold
[OpenAI]:link("https://openai.com")
```

方針:

- link だけを特別扱いせず、一般の文書作用を同じ枠で表せる
- `ident` は少なくとも識別子である
- `(...)` の中身は Yulang 引数として解釈する

### 4.4 Yulang 値の呼び出し

`\ident` は Yulang の値を呼び出す。
必要に応じて `(...)` で引数を渡し、`:` 本文や文書作用と組み合わせられる。

```yumark
Hello, \name
Hello, \name;

\note(level):
  body
```

`;` は名前の終端を明示するための省略可能な区切りである。
`\name;text` のように名前の直後に識別子文字が続く場合に使う（Perl の `${name}` に近い）。

方針:

- `\ident` / `\ident;` / `\ident(...)` はすべて同じ枠組みで、Yulang の値を呼び出す
- 「コマンド」と「値参照」を別物として区別しない
- Yumark 独自の式文法は導入しない
- `(...)` の中身は Yulang パーサに委譲する
- `[]` と役割を分離することで、文書 group と値引数の混線を避ける
- 参照先が `Doc` 値である場合は、文脈に応じて文書として展開する

## 5. 組み込み構文

通常のコマンドとは別に、少なくとも次を組み込み構文として持つ。

- `\my`
- `\use`
- `\if`
- `\elsif`
- `\else`

これらは一般コマンド定義によって上書きできない。

### 5.1 `\my`

`\my` は局所束縛を導入する。

- スコープは本文だけ
- 本文は `{...}` または `: ...`
- `(...)` には Yulang の `binding header` に近いヘッダを置ける
- 単なる変数束縛だけでなく、引数つき文書定義も許す
- `\my(head){body}` は意味的には `my head = mark { body }` と等価である
- したがって `\my(f x){...}` のような引数つき定義を許してよい
- ここで `head` は一般式ではなく、`my` の左辺に置ける binding head 相当である

例:

```yumark
\my(warning(x)){
  \box(class["warning"]){\x;}
}
```

```yumark
\my(f x){
  [x]:bold
}
```

### 5.2 `\use`

`\use` は Yulang モジュールから定義をインポートする。
スコープはそれ以降の文書全体。

```yumark
\use(my_lib::templates)

\warning:
  imported component
```

方針:

- `\use` がないと `\my` によるローカル定義しか使えない
- `\use` があると共有テンプレートライブラリを利用できる
- `(...)` の中身は Yulang の `use` 宣言に準ずる

### 5.3 `do` 引数

`do` は「現在のブロックにおける以降の内容すべて」を本文として渡す特別引数である。

```yumark
\body_margin(do)

# Chapter 1
content

# Chapter 2
content
```

これは次と等価だが、インデントを必要としない。

```yumark
\body_margin:
  # Chapter 1
  content

  # Chapter 2
  content
```

規則:

- `do` を受け取るコマンドは、それ以降の同一インデントレベルのブロック全体を本文とする
- `\cmd(do)` は文書の任意の位置に置ける（先頭が典型的）
- `\cmd(do)` を複数並べると自然に入れ子になる。各 `do` は「それ以降すべて」を取るため、後続の `\cmd(do)` ごと内側に包まれる

```yumark
\count_words(do)
\render(do)

# Content
body text
```

これは次と等価である。

```
\count_words{
  \render{
    content
  }
}
```

閉じ括弧なしで入れ子のラッパーを書ける記法として機能する。

### 5.4 `\if` / `\elsif` / `\else`

これらは制御構文として特別扱いする。

```yumark
\if(cond):
  shown
\elsif(other):
  fallback
\else:
  default
```

規則:

- `\if(cond){doc}` と `\if(cond): ...` を許す
- `\elsif(cond){doc}` と `\elsif(cond): ...` を許す
- `\else{doc}` と `\else: ...` を許す
- `\elsif` / `\else` は直前の同一レベルの `\if` 連鎖に結びつく

## 6. 文書は値

Yumark では文書そのものを値として扱う。

- 束縛対象は文書を含む任意の値でよい
- `\name` が `Doc` 値を参照した場合は文脈に応じて展開する
- Yumark を Yulang から組み立てる場合も、文字列生成ではなく `Doc` 値を返すモデルを基本とする

## 7. コードブロック

fenced code block の中身は doctest 等で使う生テキストとして扱う。

規則:

- Yumark コマンド展開をしない
- `[]` や `{}` を構文として解釈しない
- `\` は特別記号として解釈しない
- コードブロック内容を文書変換で編集しない

## 8. 非目標

v0.1 では次を扱わない。

- GFM / CommonMark 互換
- HTML 互換
- YAML front matter
- インデントコードブロック
- `\our`
- 一般ユーザー定義制御構文
- 本格的な Yulang 宣言文の持ち込み

## 9. スキャンと文書パース方針

Yumark の文書パースは、inline / block を別系統に分けず、layout-sensitive な単一の Doc Pratt パーサとして扱う。
違いは「どこで止まるか」という mode / stop 条件だけに置く。

- 通常文書
- `[]` 内文書
- `{}` 内文書
- `:` による indented body
- `--` doc comment の行内文書

これらは別パーサではなく、同じ枠組みで扱う。

### 9.1 スキャナ境界

Yumark のスキャナは「通常の 1 token 列」を返すよりも、次のような chunk を返すものとする。

```rust
struct MarkChunk {
    text: Box<str>,
    trivia_before: Box<str>,
    prefix: MarkPrefix,
    nud: MarkNud,
}
```

```rust
struct MarkPrefix {
    line_start: bool,
    indent_col: usize,
    quote_depth: usize,
    blank_before: bool,
}
```

方針:

- `text` は「次の構造境界の直前までの生テキスト」
- `trivia_before` はその境界の直前にあった改行・空白などのロスレス情報
- `prefix` は構文判断用の layout 情報
- `nud` は「その位置で見つかった次の構造境界」を表す
- `nud` は常に存在するものとし、`None` にはしない
- `Span` を持たない設計を採る間は、raw sigil は `MarkNud` 側が保持する

したがって、改行・空行・終端・閉じ記号は明示的な `MarkNud` として返す。
一方、dedent や section/list 境界の判定は parser 側が `prefix` を見て行う。

最小限、`MarkNud` は次のような集合を持つ。

```rust
enum MarkNud {
    End {
        sigil: Box<str>,
    },
    Newline {
        sigil: Box<str>,
    },
    BlankLine {
        sigil: Box<str>,
    },

    CloseBracket {
        sigil: Box<str>,
    },
    CloseBrace {
        sigil: Box<str>,
    },

    Heading {
        level: usize,
        sigil: Box<str>,
    },
    SectionClose {
        level: usize,
        sigil: Box<str>,
    },
    ListDash {
        sigil: Box<str>,
    },
    ListNum {
        sigil: Box<str>,
    },
    QuoteFence {
        depth: usize,
        sigil: Box<str>,
    },
    QuotePrefix {
        depth: usize,
        sigil: Box<str>,
    },

    Backslash {
        sigil: Box<str>,
    },
    LBracket {
        sigil: Box<str>,
    },
    BangLBracket {
        sigil: Box<str>,
    },
    EmStar {
        sigil: Box<str>,
    },
    StrongStar {
        sigil: Box<str>,
    },
}
```

ここで `QuotePrefix.sigil` は quote prefix 全体の raw text を保持する。
したがって `>` の連続だけでなく、`>` の間や末尾にある空白も含みうる。
（例: `"> "`, `">> "`, `"> > "`, `">>>   "`）

また `CloseBracket` / `CloseBrace` は、常時有効な一般トークンではなく、
現在の mode がそれらを停止条件として要求しているときにだけ返る。

方針:

- `MarkNud` は「構文境界の理由」を表す
- `(` や `:` のような tail 記号は `MarkNud` に入れない
- `# ` / `## ` / `10. ` / `>>>` のような raw sigil は lossless のために `MarkNud` が保持する
- `![` と `**` は 1 つの NUD starter として認識する
- `ContextEnd` 専用トークンは設けない

### 9.2 NUD と tail の分離

Yumark スキャナは、すべての記号を常時トークン化して返すわけではない。
返すのは次の 2 種類だけである。

- 境界トークン（改行・空行・終端・mode 依存 close）
- 文書構造を開始しうる NUD starter

少なくとも次を NUD starter とする。

- 見出し開始 `#...`
- section close `#.` / `##.` / `###.`
- リスト開始 `- ` / `1. ` / `10. `
- 明示引用開始 `>>>`
- Markdown 互換引用開始 `>` / `>>` / `>>>`
- `\`
- `[`
- `![`
- `*` / `**`

少なくとも次を境界トークンとする。

- `End`
- `Newline`
- `BlankLine`
- 現在の mode に応じた閉じ記号（`CloseBracket` / `CloseBrace`）

注意:

- `Newline` / `BlankLine` を見たときに「本当に現在コンテキストを終了するか」は parser が判断する
- dedent, sibling list, section close-by-level などは `prefix` と次の starter を使って parser が判定する

### 9.2.1 NUD 判定順

`scan_mark_nud` は、長い sigil やより制約の強い構文を先に判定する。
少なくとも次の順序を守る。

1. mode 依存の閉じ記号と文書終端
   - `End`
   - `CloseBracket`
   - `CloseBrace`
2. 空行と改行
   - `BlankLine`
   - `Newline`
3. 行頭専用の長い sigil
   - `SectionClose`
   - `Heading`
   - `ListNum`
   - `ListDash`
   - `QuoteFence`
   - `QuotePrefix`
4. inline / command 開始記号のうち、複数文字のもの
   - `BangLBracket`
   - `StrongStar`
5. inline / command 開始記号のうち、1文字のもの
   - `Backslash`
   - `LBracket`
   - `EmStar`

方針:

- `**` は `*` より先に判定する
- `![` は `[` より先に判定する
- `#.` は `#` より先に判定する
- `10. ` は `- ` や通常 text より先に判定する
- `QuoteFence` は `QuotePrefix` より先に判定する
- 行頭専用の構文は `prefix.line_start = true` のときだけ判定する

一方、次のような記号はグローバルにはトークン化しない。

- `(`
- `)`
- `:`
- `{`
- `}`
- `;`

これらは NUD が成立した後の tail として、その parselet が局所的に読む。

例:

- `[doc]` を読んだ後だけ `(dest)` や `:ident(...)` を読む
- `\ident` を読んだ後だけ `(...)`, `{...}`, `: ...`, `do`, `;` を読む

この方針により、`(` や `:` が文脈なしに text を不必要に分断することを避ける。

### 9.3 `--` doc comment

`--` doc comment も専用の別パーサは作らず、同じ Doc Pratt パーサを
「改行または EOF で停止する mode」として用いる。

方針:

- block NUD は無効
- inline markup は有効
- 終端は改行または EOF

### 9.4 強調記法の最小方針

v0.1 の強調記法は `*` と `**` のみを持つ。

- `*...*` は emphasis
- `**...**` は strong emphasis
- `_` は強調記法としては使わず、常に通常テキストとして扱う

方針:

- `_` は識別子や snake_case と衝突しやすいため、v0.1 では強調記法から外す
- 強調用の NUD starter は `*` と `**` のみとする
- CommonMark 的な `_` delimiter rule は導入しない

### 9.5 リスト項目コンテキスト

リスト項目の構造判定には、少なくとも次の 3 つを区別して保持する。

```rust
struct ListItemContext {
    sigil: Box<str>,
    indent_col: usize,
    content_col: usize,
}
```

用語:

- `sigil`
  - 項目開始の生記号列
  - 例: `"- "`, `"1. "`, `"10. "`
- `indent_col`
  - 行頭から、リストマーカー先頭までの列位置
- `content_col`
  - リストマーカーの後で、本文が始まる列位置

例:

```text
    - item
```

このとき

- `sigil = "- "`
- `indent_col = 4`
- `content_col = 6`

となる。

```text
    10. item
```

このとき

- `sigil = "10. "`
- `indent_col = 4`
- `content_col = 8`

となる。

方針:

- リストの入れ子や継続判定に本質的なのは番号そのものではなく列位置である
- `ListNum` は数値を別フィールドで保持せず、raw な `sigil` のみを持てばよい
- 継続行か子リストかの判定には `content_col` を使う
- 親コンテキストからの離脱判定には `indent_col` を使う

### 9.5.1 継続行・子リスト・復帰

ある `ListItemContext { sigil, indent_col, content_col }` を開いているとき、
次行の扱いは少なくとも次の規則で決める。

1. 空行
   - 空行は項目内部の段落区切りである
   - 空行だけでは直ちに親へ復帰しない
2. `indent_col < item.indent_col`
   - 現在のリスト項目は終了し、親コンテキストへ復帰する
3. `indent_col >= item.content_col` かつ行頭がリストマーカーで始まらない
   - 現在の項目の継続本文として扱う
4. `indent_col >= item.content_col` かつ行頭がリストマーカーで始まる
   - 子リスト開始として扱う
5. `indent_col == item.indent_col` かつ行頭が同種または他種のリストマーカーで始まる
   - 現在の項目を閉じ、同じ深さの次項目として扱う

規則 4 と 5 が重なる場合は、より具体的な規則 5 を優先する。

ここで「行頭がリストマーカーで始まる」は、現在行の `prefix.line_start = true` の位置から
`ListDash` または `ListNum` が成立することを意味する。

例:

```yumark
- item
  continued line
```

- 2 行目は `indent_col >= content_col` かつリストマーカーで始まらない
- したがって 1 項目目の継続本文である

```yumark
- item
  - child
```

- 2 行目は `indent_col >= content_col` かつリストマーカーで始まる
- したがって子リストである

```yumark
- item one
- item two
```

- 2 行目は `indent_col == item.indent_col` かつリストマーカーで始まる
- したがって同じ深さの次項目である

```yumark
  - item
next
```

- 2 行目は `indent_col < item.indent_col`
- したがって親コンテキストへ復帰する

## 10. CST 方針メモ

Yumark と Yulang は最初から共通の CST 上で扱う。

最小限、次のようなノードが必要になる。

- `YmDoc`
- `YmHeading`
- `YmSection`
- `YmImplicitSection`
- `YmExplicitSection`
- `YmSectionClose`
- `YmList`
- `YmListItem`
- `YmQuoteBlock`
- `YmCodeFence`
- `YmParagraph`
- `YmCommand`
- `YmCommandArgs`
- `YmCommandBody`
- `YmMy`
- `YmIf`
- `YmElsif`
- `YmElse`
- `YmInlineRef`
- `YmInlineGroup`
- `YmInlineLink`
- `YmInlineImage`
- `YmInlineApply`
- `YmInlineApplyHead`
- `YmInlineApplyArgs`
- `YmYulangArgs`
- `YmDocArg`

方針:

- `[doc]` / `[doc](dest)` / `[doc]:op(...)` は見た目が近くても別ノードに分ける
- `# Heading` と `# Heading:` も別ノード系列に分ける
- close 記法 `#.` / `##.` は独立ノードとして保持する
- CST では可能な限り構文差を保存し、共通化は AST 以降で行う

## 11. 例

````yumark
\my(warning(x)):
  \box(class["warning"]):
    \x;

# Intro:
  Hello

  \if(show_warning):
    [careful]:warning
  \else:
    plain text

  - item one
    continued line
    - nested item

# Chapter

plain paragraph with [OpenAI](https://openai.com)
and [important]:bold text.

## Detail
more text
##.

>>>
quoted block
>>>

```rust
fn main() {}
```
````
