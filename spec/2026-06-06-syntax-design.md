# Yulang 構文仕様メモ

作成日: 2026-06-06

この文書は、2026-06-06 時点の `crates/yulang-parser` 実装から抽出した
Yulang の構文仕様である。型推論、lowering、runtime の意味論は扱わない。
ここで「受理する」と書くものは、parser が CST として組み立てる表面構文を指す。

確認元は次である。

- parser 実装:
  - `crates/yulang-parser/src/lib.rs`
  - `crates/yulang-parser/src/scan/*`
  - `crates/yulang-parser/src/stmt/*`
  - `crates/yulang-parser/src/expr/*`
  - `crates/yulang-parser/src/pat/*`
  - `crates/yulang-parser/src/typ/*`
  - `crates/yulang-parser/src/string/*`
  - `crates/yulang-parser/src/mark/*`
- parser tests:
  - `crates/yulang-parser/tests/stmt_grammar.rs`
  - `crates/yulang-parser/tests/expr_grammar.rs`
  - `crates/yulang-parser/tests/pat_grammar.rs`
  - `crates/yulang-parser/tests/type_grammar.rs`
  - `crates/yulang-parser/tests/mark_grammar.rs`
  - `crates/yulang-parser/tests/trivia_grammar.rs`
- 抜き取り確認:
  - `yulang parse --as stmt`
  - `yulang parse --as expr`
  - `yulang parse --as type`

既存 test に直接例がある構文を中心に書く。実装からは確認できるが test 例が薄い枝は、
その旨を本文で明示する。意図や将来仕様ではなく、現在の parser の挙動を書く。

## 記法

- `A?` は 0 回または 1 回。
- `A*` は 0 回以上。
- `A+` は 1 回以上。
- `A | B` は選択。
- `TOKEN` は scanner が作る token。
- `Node(...)` は主な CST node。
- 「空白あり」は `TriviaInfo::Space` または継続可能な newline を含む。
- 「空白なし」は `TriviaInfo::None` を指す。

## 字句

### trivia

trivia は token の前後に保持され、CST にも出る。

- space / tab / newline
- line comment: `//` から行末まで
- block comment: `/* ... */`
- quote prefix: Yumark block quote 用の `>` prefix

block comment は入れ子を扱う。未閉じ block comment は EOF で空の
`BlockCommentEnd` を補って trivia として回復する。

`TriviaInfo` は parser の layout 判断に使われる。

- `None`: trivia なし
- `Space`: 改行を含まない trivia
- `Newline { indent, quote_level, blank_line }`

indent は最後の改行以後の space / tab / `>` を数えた値である。
line comment は末尾 newline を含まなければ `Space` 扱いであり、newline まで含めて読むと
`Newline` になる。block comment も内部または直後に newline を含まなければ `Space` 扱いである。
空行を含む trivia は `blank_line: true` になる。
operator scanner の `pre_ws` は `leading_info != None` で判定する。ただし expression tail
では、現在の `env.indent` 以下の newline は operator 判定の前に式を止める。そのため、
tail 位置で operator 判定に届く newline は、基本的に現在行より深い indent の継続行である。

### identifiers

通常 identifier は次の形。

```text
ident = (Unicode XID start | "_") (Unicode XID continue)* ("?" | "!")?
```

`?` / `!` は末尾に 1 個だけ付けられる。

sigil identifier は次の形。

```text
sigil_ident = ("$" | "&" | "_" | "'") ident
```

`_bar` は通常 identifier ではなく `SigilIdent` として読まれる文脈がある。
一方、`_` 単独は `ident` として読める。

symbol は次の形。

```text
symbol = ":" ident
```

symbol は式・パターンの先頭、または空白後の tail で読まれる。
空白なしの `f:foo` は `Symbol(":foo")` ではなく、`f` に対する `:` application と
`foo` として読まれる。

### numbers

number は次のいずれか。

```text
digits
digits "." digits
digits exponent
digits "." digits exponent
"." digits
"." digits exponent

exponent = ("e" | "E") ("+" | "-")? digits
```

`1.` は number ではない。operator 定義の binding power では、通常 number scanner とは
別に `digits ("." digits)*` を読む。

### keywords

scanner が keyword 候補として知っている語は次である。

```text
do if else elsif case catch
my our pub use type struct enum error role impl cast act mod
as for in with where via rule
prefix infix suffix nullfix lazy
```

keyword は文脈依存で読む。文脈で意味を持たない keyword 候補は `Ident` に戻る。

- statement head scanner は keyword 候補をそのまま token 化し、declaration / statement dispatch
  に使う。
- visibility 後 scanner は `pub struct` / `our act` などの declaration keyword だけを
  keyword として残し、それ以外は binding pattern の `Ident` にする。
- expression / pattern / type scanner は、その文脈で syntax または stop として意味を持つ
  keyword だけを残す。
- declaration 名、field 名、variant 名、path segment は name scanner で読み、keyword 候補も
  `Ident` として扱う。

たとえば statement head の `error fs_err:` は `ErrorDecl` になるが、`my error = 1` の
`error` は binding 名であり、`mod error;` の `error` は module 名である。

### punctuation

式 scanner の主な punctuation は次である。

```text
... -> :: ( ) [ ] { } \ ' , : = ; |
```

パターン scanner は `..` を spread 用に読む。
型 scanner は `'` を effect row prefix 用に読む。

doc comment token は statement scanner でだけ `---` / `--` として読まれる。
`---` は block doc comment、`--` は line doc comment の入口である。

## module と statement 境界

公開入口 `parse_module_to_green` は `Root` node を作り、先頭 trivia を読み、
`parse_statement` を繰り返す。

statement parser は最初に statement head scanner で 1 token を読む。
その token が declaration / statement keyword なら、その種類で dispatch する。
それ以外は、先に読んだ token を expression parser の NUD として渡し、expression statement
として読む。

statement の入口になる主な token は次である。

```text
my our pub use mod type struct enum error role impl cast act for
lazy prefix infix suffix nullfix where
-- ---
```

それ以外で式として読めたものは expression statement になる。

## list と block の共通規則

### brace statement block

`{ ... }` を statement block として読む場所では `BraceGroup` node になる。
中身は `parse_statement` の繰り返しである。

区切りは次である。

- `,`
- `;`
- newline による暗黙区切り

`}` で閉じる。

### indent statement block

`:` や `=` の後に newline があり、その indent が現在の base indent より大きい場合、
`IndentBlock` が始まる。block は同じ indent 以上の行を statement として読み続ける。
indent が block indent より小さくなると block が終わる。

block 内の各 statement は、その statement を読み始めた行の indent を `env.indent` として
expression parser に渡す。expression tail は、次の token の leading trivia が
`Newline { indent }` で、かつ `indent <= env.indent` のとき現在の式を止める。
`indent > env.indent` の newline は継続行として扱われ、operator / field / path /
ML application などの tail を続けられる。

例外として、`if` expression 本体は arm の後ろに続く `elsif` / `else` を専用に探す。
そのため `else` / `elsif` は `if` と同じ indent の次行でも同じ `IfExpr` に入る。

例:

```yu
1
  + 2
```

上は `1 + 2` と同じ `InfixNode` になる。

```yu
f
  x
```

上は `f x` と同じ `ApplyML` になる。

一方、現在 indent と同じ深さまで戻る newline は式を止める。

```yu
f
x
```

この形は 1 つの expression としては `f` で止まる。module / block parser では、次の
`x` が次 statement として処理される。

### delimited list

`(...)` / `[...]` / `{...}` の中の list は文脈ごとに区切り token が違う。
多くの list では newline も暗黙区切りになる。

delimited list の `base_indent` は、open token の直後が深い newline ならその indent、
そうでなければ外側の `env.indent` になる。list item を 1 つ読んだあと、
`Newline { indent }` が `indent <= base_indent` なら暗黙 separator になる。
`indent > base_indent` は item の継続として扱われ、式 parser へ渡る。

expression / pattern / type / use group の汎用 delimited list では、separator の直後に
closing token が来る trailing separator も受理される。一方、`struct` field や `enum`
variant の brace body は別の item parser を使うため、trailing comma は空 item を
読もうとして invalid recovery になる。

例:

```yu
[
  f
    x
  g
]
```

`f` の次行 `x` は `f x` の継続であり、`g` は list の次 item になる。

brace statement block は indent で block 自体を閉じない。`}` が出るまで statement block
を続ける。ただし各 statement の開始行 indent は expression の継続判定に使われる。

## statement

### visibility と binding dispatch

`my` / `our` / `pub` はまず visibility または binding head として読む。
直後が declaration keyword なら、その declaration に visibility を付ける。
それ以外は binding になる。

```yu
my x = 1
our f x = x
pub use std::prelude::*
pub struct point { x: int, y: int }
```

binding は `Binding` node を作り、内部に `BindingHeader` と必要なら `BindingBody` を持つ。

```text
binding =
  ("my" | "our" | "pub") pattern ("=" binding_body)?
```

`binding_body` は inline expression または indent statement block である。
parser は `pub x` のような body なし binding も受理する。

### `mod`

```text
mod_decl =
  visibility? "mod" ident (
      ";"
    | brace_statement_block
    | ":" decl_body
  )
```

`decl_body` は inline statement、semicolon 終端、または indent statement block である。

例:

```yu
mod Foo;
mod Foo { x; y }
mod Foo:
  my x = 1
```

### `use`

`use` は専用 scanner を使う。通常の式 token とは違い、version suffix や
parenthesized operator segment を扱う。

```text
use_decl =
  visibility? "use" use_spec

use_spec =
    use_group
  | "mod" use_path
  | use_path
  | use_operator_segment

use_path =
  use_segment (("/" | "::") use_segment)* use_suffix*

use_segment =
    ident
  | "*"
  | use_group
  | use_operator_segment

use_operator_segment = "(" use_op_name ")"
use_group = "{" use_spec (("," | newline) use_spec)* ","? "}"
```

`use_op_name` は 1 文字以上で、whitespace と `:` / `(` / `)` / `{` / `}` / `[` / `]` /
`,` / `;` / `/` を含まない文字列である。operator segment 内では ident や `*` も
`OpName` として出る。

suffix として読めるもの:

- `as ident`
- version suffix: `v` + digit + ASCII alnum / `.` / `-` / `+`
- `with` anchor path
- glob 後の `without` list

suffix は通常 path / glob / operator segment / brace group の後で読まれる。
`with` / `without` は use 専用 scanner では keyword 相当の tag になるが、CST token kind は
`Ident` である。

例:

```yu
use std::io
use std::io::*
use mod math::*
use a/b::c
use std::io::{Read, Write}
use m::(+)
use m::{(+), id}
use std::io as io
use yulang/std::prelude v0.1.3
use ui/widget::a with program::ui
use {a, b} as ab
use {a, b} with root
use m::* without (+), id
```

`without` の直後は ident / glob / parenthesized operator / brace group を読める。
実装上、`without { ... }` の後にさらに `with ...` を続ける形は同じ `UseDecl` に
取り込まれず、後続 token として外へ出る。

`use { ... }` の brace group 内では、newline は indent に関係なく item separator になる。

### `type`

```text
type_decl =
  visibility? "type" ident type_vars type_tail

type_vars = (ident | sigil_ident)*
```

`type_tail` は次のいずれか。

- `impl` に続く impl tail
- `with` block
- `=` type_rhs
- role-like body
- 何もなし

`type_vars` は newline / EOF / `with` / `impl` で止まる。

alias:

```yu
type id 't = 't
type T = Int;
```

`type_rhs` の後は次を受ける。

- `with` block
- `;`
- `:` declaration body
- `{...}` statement block
- outer list stop (`]` / `)` / `}` / `,`)

`type ... impl ...` は `TypeDecl` の中に `Impl` token と impl tail を持つ。
抜き取り確認では次の形が `TypeDecl` として読まれた。

```yu
type Box 't impl Eq int via Ord;
```

`type ... with` の中に direct child として `struct self` を書いた場合、その `struct self` は
nested type 宣言ではなく、外側 `type` の constructor payload として読む。

```yu
type t 'a with:
  struct self:
    field: 'a
```

これは `t: { field: 'a } -> t 'a` 相当の constructor を外側 module の value namespace に作る。

### `struct`

```text
struct_decl =
  visibility? "struct" ident type_vars struct_body? with_or_stop

struct_body =
    "{" named_struct_fields "}"
  | "(" tuple_struct_fields ")"
  | ":" indent_named_struct_fields
```

named field:

```text
struct_field = ident (":" type)?
```

tuple field:

```text
struct_tuple_field = type
```

例:

```yu
struct S { x: Int, y: String }
struct Pair(int, str)
struct S:
  x: Int
  y: String
```

body の後には `with` block、`;`、または outer list stop が続けられる。

### `enum`

```text
enum_decl =
  visibility? "enum" ident type_vars enum_body? with_or_stop

enum_body =
    "{" enum_variant ("," enum_variant)* "}"
  | ":" indent_enum_variants
  | "=" inline_or_indent_enum_variants
```

inline `=` body の variant 区切りは `|` である。
indent body では各行の先頭に `|` を置ける。
brace body の区切りは `,` である。

variant:

```text
enum_variant =
  ident (
      "from" type
    | "{" named_struct_fields "}"
    | "(" tuple_struct_fields ")"
    | type+
  )?
```

例:

```yu
enum opt 't = nil | just 't
enum shape = circle int | rect int int
enum tree =
  leaf
  | node int
enum E { A, B }
enum E { A { x: int }, B(int, str) }
enum E = A with:
  our x.foo = true
```

### `error`

`error` は `ErrorDecl` node を作る。name の後ろには `type_vars` を読める。
body は `enum_body` と同じ variant parser を使う。

```text
error_decl =
  visibility? "error" ident type_vars enum_body?
```

```yu
error fs_err:
  not_found str
  denied str

error io_err:
  fs from fs_err
```

### `role`

```text
role_decl =
  visibility? "role" type role_body

role_body =
    ";"
  | brace_statement_block
  | ":" decl_body
```

`role` の head は identifier ではなく `type` parser で読む。

例:

```yu
role Eq;
role Printable:
  our print: Self -> ()
role Eq {
  our eq: Self -> Self -> Bool
}
```

`role` head の parse では `via` が stop に入っているが、`role ... via ...` は
role body として処理されず invalid token になる。

### `impl`

```text
impl_decl =
  visibility? "impl" impl_head impl_body

impl_head =
  type ("," type)* ("via" type)?

impl_body =
    ";"
  | brace_statement_block
  | ":" decl_body
  | empty
```

例:

```yu
impl Eq Int;
impl Int: Eq;
impl Eq via Ord;
impl Int: Eq {
  our eq = id
}
impl Index lines int:
  type value = str
  our xs.index i = ...
impl lines: Index int:
  type value = str
  our xs.index i = ...
```

`impl` は複数の type を `,` で並べられる。`via` の後には type を 1 つ読む。
role の impl は、prefix 形の `impl Role First Rest...` と receiver-first 形の
`impl First: Role Rest...` の両方を書ける。どちらも同じ role impl として読む。
receiver-first で左側へ出せるのは role の第1通常引数だけで、第2引数以降は role 名の
後ろに通常の type argument として置く。

### `cast`

```text
cast_decl =
  visibility? "cast" "(" pattern ")" ":" type ("=" cast_body | ";")

cast_body =
    expr
  | indent_statement_block
```

例:

```yu
cast(x: user_id): int = x.raw
pub cast(x: int): user_id = user_id { raw: x }
```

### `act`

```text
act_decl =
  visibility? "act" act_name act_tail

act_name =
  (ident | sigil_ident) ("::" (ident | sigil_ident))*
```

`act_tail` は次の形を受ける。

- type parameter list: 空白ありの `(` (type (`,` type)* `,`?)? `)`
- type arguments: type (`,` type)*
- `= type` による source type
- `with` block
- `;` / `{...}` / `:` body
- 何もなし

実装上、`act local('t)` のように name と `(` の間が空白なしだと、`act_name` の直後で
tail が終わり、`(` は後続 token として invalid recovery に回る。空白ありの
`act local ('t)` は type parameter list として読まれる。

例:

```yu
act Console::Read;
act local 't = var 't
act local ()
act local ('t, int) = var 't with { our x = 1 }
```

### `for`

`for` は statement であり、式ではない。

```text
for_stmt =
  "for" for_label? pattern "in" expr for_body

for_label = sigil_ident_starting_with_apostrophe

for_body =
    ":" inline_or_indent_body
  | brace_statement_block
```

label は `'outer` のような `SigilIdent` で、直後が `in` の場合は label ではなく
pattern 側へ残る。

例:

```yu
for x in xs:
  x

for 'outer x in xs:
  x

for x in xs { x }
```

### `where`

```text
where_clause =
  "where" (":" indent_where_constraints | where_constraint)

where_constraint =
    type
  | type ":" type ("," type)*
```

indent block 内の constraint は semicolon も item separator になる。
inline の `where T: Eq; U: Ord` は、現在の parser では `where T: Eq` の後に
semicolon が外へ返り、`U: Ord` は別 statement として読まれる。
複数 constraint は `where:` block に置くのが実装に沿う。

例:

```yu
where:
  Self: Sized
  Int: Add
  container: Index key
```

role predicate も impl と同じく、role の第1通常引数を左側の receiver として書く。
`where Index container key` と `where container: Index key` はどちらも同じ role predicate
として読む。関連型を持つ predicate の dump 表示は `where container: Index(key, value = item)`
のように role call の括弧内へ置く。

### operator definition

```text
op_def =
  visibility? "lazy"? fixity "(" op_name ")" bp* "=" op_body

fixity = "nullfix" | "prefix" | "infix" | "suffix"
```

operator definition の `op_name` は 1 文字以上で、whitespace と
`(` / `)` / `[` / `]` / `{` / `}` / `\` / `,` / `;` / `"` / `'` を含まない文字列である。
`use` の operator segment より除外文字が少なく、`:` や `/` も読める。

binding power 数:

- `nullfix`: 0 個
- `prefix`: 1 個
- `suffix`: 1 個
- `infix`: 2 個

binding power token は `digits ("." digits)*`。

body は inline expression または indent statement block である。
operator definition は parser の local operator table も更新する。

例:

```yu
nullfix (+) = x
prefix (not) 70 = x
infix (+) 50 50 = x
suffix (!) 80 = x
pub lazy infix (and) 20 20 = x
infix (+) 5.0.1 5.0.2 = x
```

### doc comment statement

```text
doc_comment_decl =
    "--" inline_yumark
  | "---" block_yumark "---"
```

`--` は line doc comment として inline Yumark を読む。
`---` は block doc comment として Yumark document body を読み、閉じ `---` を
`DocComment` token として出す。

block doc comment 内の fenced code の info line が `yulang` で始まる場合、
fence body は Yulang statement parser で読まれる。

## expression

式 parser は Pratt parser である。operator table と trivia によって prefix / infix /
suffix / nullfix の判定が変わる。

### primary expression

式の primary は主に次である。

```text
expr_primary =
    ident_like
  | sigil_ident
  | number
  | symbol
  | "do"
  | "..."
  | string_lit
  | rule_lit
  | rule_expr
  | "(" expr_list? ")"
  | "[" list_exprs? "]"
  | brace_statement_block
  | "\" lambda
  | "'" quoted_mark
  | if_expr
  | case_expr
  | catch_expr
  | prefix_op expr
  | nullfix_op
```

`do` は CST 上は atom である。

`...` は `YadaYada` token の nullfix expression になる。

`{ ... }` は expression primary として出た場合も statement block の
`BraceGroup` である。record literal 専用 node はなく、`{x: 1}` は
`BraceGroup` 内の `Expr(Ident("x") ApplyColon(...))` として読まれる。

### expression tail

primary の後に続けられる tail は次である。

```text
expr_tail =
    "." field
  | "::" path_segment
  | "(" expr_list? ")"
  | "[" expr_list? "]"
  | ":" apply_colon_rhs
  | "=" assign_rhs
  | "with" ":" statement_body
  | "as" type
  | infix_op expr
  | suffix_op
  | expr_primary_as_ml_arg
```

`:` / `=` / `with` / `as` は、infix RHS や ML argument 内では親 parser に返る。
最外層 tail としてだけ有効になる。

### call と ML application

空白なしの `(` は `ApplyC` である。

```yu
f(x, y)
```

`(` の前に空白または継続 newline がある場合、その `(` は call group ではなく
parenthesized expression の primary になり、全体として `ApplyML` の引数になる。

```yu
f (x)

f
  (x)
```

通常の隣接引数も `ApplyML` である。

```yu
f x y
f { g x }
```

identifier 同士は lexing の都合で空白や continuation が必要である。
group / string などは scanner 上 tail primary として読まれるため、空白なしでも
`ApplyML` になりうる。

`ApplyML` の引数を読んでいる間は、引数の内部 tail は空白に敏感になる。
`ml_arg` 中に leading trivia がある tail が来ると、現在の引数をそこで止めて外側に返す。
空白なしの tail は引数の内部に残る。

例:

```yu
f 1+2
```

上は `f (1 + 2)` の形、つまり `ApplyML` の引数内に `+` が入る。

```yu
f 1 + 2

f 1
  + 2
```

上は `(f 1) + 2` の形、つまり `+` が外側の infix になる。

同じ理由で、標準 `..` のような空白なし infix は ML 引数内に残る。

```yu
each 1..2 + each 1..2
```

この形では、各 `1..2` がそれぞれの `each` の引数になり、外側の `+` が
2 つの `ApplyML` をつなぐ。

### field と path

field は `.field` を 1 token として読む。

```yu
x.foo
(x, y).foo
```

field tail は `(` / `[` と違い、前に空白があっても field として読まれる。
浅い newline では tail 判定の前に式が止まり、深い newline では継続できる。

```yu
x .foo

x
  .foo
```

method call に見える形は、構文上は field tail の後ろに call / application tail が
続いただけである。空白なしの `(` は `ApplyC`、空白ありの `(` は parenthesized
expression を引数にする `ApplyML` になる。

```yu
x.foo(a)   // Field + ApplyC
x.foo (a)  // Field + ApplyML(Paren)
```

path separator は `::` である。右側 path segment として次を許す。

- `Ident`
- `SigilIdent`
- `prefix`
- `infix`
- `suffix`
- `nullfix`
- `mod`

例:

```yu
Foo::bar::baz
x.foo::bar
```

`::` も前後の空白を許す。field と同じく、浅い newline では式が止まり、深い newline
では path tail として続く。

```yu
Foo :: bar

Foo
  ::bar
```

### list / index / spread

list literal は `Bracket` node である。

```yu
[1, 2]
[
  1
  2
]
[1, ..xs, 3]
```

list item の `..expr` は `ExprSpread` になる。`..<` で始まる token は list spread としては
読まない。

空白なしの tail `[...]` は `Index` である。

```yu
xs[0]
xs[2..]
xs[..2]
```

### colon application

```text
apply_colon =
  expr ":" (inline_expr ("," inline_expr)* | indent_statement_block)
```

例:

```yu
f: x + y
f: x, y + z
f:
  x
  y
```

空白なしの `f:foo` は `f` への colon application であり、`foo` は expression として読む。

### assignment suffix

```text
assign =
  expr "=" (inline_expr | indent_statement_block)
```

assignment は expression tail であり、binding の `=` とは別 node (`Assign`) になる。

### with block suffix

```text
with_block =
  expr "with" ":" (inline_statement | indent_statement_block)
```

例:

```yu
y with:
  my y = 1
```

### type annotation suffix

```text
expr_as =
  expr "as" type
```

例:

```yu
x as int
```

### if

```text
if_expr =
  if_arm ("elsif" if_arm_tail)* else_arm?

if_arm =
  ("if" | "elsif") expr (":" inline_or_indent_body | "{" expr_list? "}")

else_arm =
    "else" ":" inline_or_indent_body
  | "else" "{" expr_list? "}"
  | "else" expr
```

例:

```yu
if x: 1 else: 0

if x:
  1
else: 0
```

`if` / `elsif` の brace body は expression list の `BraceGroup` であり、
statement block ではない。

`elsif` / `else` は、前 arm の後ろに空白で続く形と、`if` の base indent 以上の newline
に続く形を読める。newline の次 token が `elsif` / `else` でない場合、`IfExpr` はそこで
終わる。

### lambda

```text
lambda =
    "\" pattern* "->" inline_or_indent_body
  | "\" "." field_tail
  | "\" sigil_ident_starting_with_apostrophe pattern* "->" body
  | "\case" case_lambda
  | "\catch" catch_lambda
```

例:

```yu
\x -> x + 1
\() x -> x
\.foo(1)
\.method1(a, b).method2(c, d)
\'self x -> 'self x
\case: 1 -> 41, _ -> 0
\catch: value -> value
```

`\case` / `\catch` は backslash と keyword の間に空白がない場合だけ専用 lambda になる。
recursive lambda label も backslash と sigil ident の間に空白がない場合だけ有効である。
method lambda は backslash の trailing trivia に関係なく、次に `.field` が見えれば
`MethodLambdaExpr` になる。そのため `\.foo` と `\ .foo` はどちらも method lambda である。

### case / catch

```text
case_expr =
  "case" case_label? expr ":" case_arms

case_lambda =
  "\case" case_label? ":" case_arms

case_label = sigil_ident_starting_with_apostrophe
```

case arms:

```text
case_arm =
  pattern (("if" | "where") expr)? "->" body
```

`case` は colon 後の inline arm list と indent arm block を許す。
inline arm list は `,` 区切りである。
`case` expression 自体は brace arm block を持たない。`case x { ... }` は `{...}` が
scrutinee expression 側の brace group / ML argument として読まれる。

```yu
case x: 1 -> a, 2 -> b
case x:
  n if n > 0 -> pos
  _ -> neg
case 'go 4: 0 -> 0, n -> n
\case 'go: 0 -> 0, n -> n
```

`catch` は同じ arm parser を使うが、handler name と brace block を許す。
colon 後が inline の場合、`catch` は comma 区切りの inline arm list を読まず、1 arm で止まる。
複数 arm を inline で書く場合は brace block が必要である。

```text
catch_expr =
  "catch" catch_label? expr (":" catch_arms | "{" catch_arms "}")

catch_arm =
  pattern ("," pattern)? (("if" | "where") expr)? "->" body
```

例:

```yu
catch f x:
  Ok v -> v
  Err e, h -> h e

catch f { Err e, h -> h e }
catch f { Ok v -> v, Err e, h -> h e }
\catch: value -> value
```

### operators

`standard_op_table()` が初期状態で持つ operator は次である。

| operator | fixity |
| --- | --- |
| `+` | infix |
| `-` | prefix, infix |
| `*` | infix |
| `/` | infix |
| `%` | infix |
| `..` | nullfix, prefix, infix, suffix |
| `==` | infix |
| `!=` | infix |
| `<` | infix |
| `<=` | infix |
| `>` | infix |
| `>=` | infix |
| `and` | infix |
| `or` | infix |
| `|` | infix, CST node は `PipeNode` |

binding power は parser の `BpVec` で比較する。`+` と `-` は 50、`*` / `/` / `%` は 60、
comparison は 30、`and` は 20、`or` は 10、pipeline `|` は 5 である。
infix は右 binding power に `[lbp, 1]` を使うため、同じ優先順位の chain は左結合になる。

operator table は module parse 中の operator definition で更新される。
prelude や source loader が渡す operator table も expression parse に影響する。

### operator kind 衝突と空白

同じ operator text が prefix / infix / suffix / nullfix の複数 kind を持つ場合、
parser は binding power の前に、operator の前後の trivia と後続 value の有無から
どの kind として読むかを決める。

実装上の入力は次である。

- `pre_ws`: operator token の leading trivia が `None` でなければ true
- `post_ws`: operator token の trailing trivia がある、EOF、または次 token が
  expression stop なら true
- `probe_value_start`: operator の後ろが value start として読めるなら true

NUD 位置では infix / suffix 候補を先に落とす。さらに `probe_value_start == false`
なら prefix 候補も落とす。したがって NUD 位置で実際に残るのは prefix / nullfix だけである。

LED 位置では、`probe_value_start == false` のとき prefix / infix 候補を落とす。
また `post_ws == true` の場合、一度 prefix 候補を落とした候補集合で table を引き、
失敗したときだけ元の候補集合で引き直す。これにより、空白後の ML argument と競合する位置では
suffix / nullfix が prefix より先に選ばれる場合がある。

table は候補集合ごとに次の結果を返す。`P` は prefix、`I` は infix、`S` は suffix、
`N` は nullfix、`-` は該当なしである。この表は、上の NUD / LED の事前フィルタ後の
候補集合に対して使われる。

| kinds | `pre=0 post=0` | `pre=0 post=1` | `pre=1 post=0` | `pre=1 post=1` |
| --- | --- | --- | --- | --- |
| none | - | - | - | - |
| P | P | P | P | P |
| I | I | I | I | I |
| P+I | I | I | P | I |
| S | S | S | S | S |
| P+S | - | S | P | - |
| I+S | I | S | I | I |
| P+I+S | I | S | P | I |
| N | N | N | N | N |
| P+N | P | N | P | N |
| I+N | I | I | I | N |
| P+I+N | I | I | P | N |
| S+N | N | S | N | N |
| P+S+N | N | S | P | N |
| I+S+N | I | S | I | N |
| P+I+S+N | I | S | P | N |

標準 operator では `..` が `P+I+S+N` なので、空白で次のように変わる。

| source | CST 上の読み |
| --- | --- |
| `1..2` | `Infix ".."` |
| `1 ..2` | `ApplyML` の引数として `Prefix ".."` |
| `1.. 2` | `Suffix ".."` のあとに `2` を `ApplyML` |
| `1 .. 2` | `ApplyML` の引数として `Nullfix ".."`、さらに `2` を `ApplyML` |
| `..2` | `Prefix ".."` |
| `.. 2` | `Nullfix ".."` のあとに `2` を `ApplyML` |
| `1..` | `Suffix ".."` |
| `1 ..` | `ApplyML` の引数として `Nullfix ".."` |

operator text が Unicode XID continue で終わる場合、次の文字も Unicode XID continue
なら match しない。これにより、word operator が identifier の一部として切り出されない。

prefix + nullfix だけを持ち、infix / suffix を持たない operator には、
call / path との衝突回避がある。
operator の直後に空白なしで `(` または `:` が来る場合、その operator match は捨てられ、
identifier call / path として読まれる。

例として、`return` が prefix + nullfix operator として登録されている場合:

```yu
return      // Nullfix operator
return x    // Prefix operator
return()    // Ident "return" + ApplyC
return::x   // Ident "return" + PathSep
```

## type

型 parser も Pratt 風である。

### type primary

```text
type_primary =
    ident_like
  | sigil_ident
  | number
  | "for" sigil_ident+ ":" type
  | "(" type_list? ")"
  | "[" type_list? "]" row_prefixed_type
  | "'[" type_list? "]"
  | "{" type_fields? "}"
  | ":{" poly_variant_items? "}"
```

`for` は forall 専用である。forall binder は `SigilIdent` だけを受ける。

```yu
for 'a 'b: 'a -> 'b
```

### type tail

```text
type_tail =
    "->" type
  | "::" type_path_segment
  | "(" type_list? ")"
  | "[" type_list? "]" ("->" type)?
  | type_primary_as_ml_arg
```

`->` は右結合である。

```yu
Int -> String -> Bool
```

ML style type application:

```yu
List Int
Dict String Int
```

C style type call:

```yu
list(int)
```

`(` の前に空白がある場合は `TypeCall` ではなく、`TypeParenGroup` を引数にする
`TypeApply` になる。

```yu
List(Int)  // TypeCall
List (Int) // TypeApply(TypeParenGroup)
```

path:

```yu
std::opt::opt int
Foo :: Bar
```

effect row arrow:

```yu
Int [io] -> String
```

この形は `TypeArrow` の中に `TypeRow` を持つことを抜き取り確認済みである。
`Int [io]` のように `->` が無い場合も parser は `TypeArrow` node を開始し、
row だけを入れて終わる。

### type row / effect row

row node は `[` ... `]` である。現在の parser では bare `[e]` だけを
complete type として EOF まで読む形は失敗する。row は主に次の位置で現れる。

- effect row type: `'[e]`
- row-prefixed type: `[e] T`
- effect arrow tail: `T [e] -> U`

```yu
'[e]
[e] T
T [e] -> U
```

effect row type は apostrophe と row の組である。

```yu
'[e]
'['e]
Foo '['e]
```

### record type

```text
type_record =
  "{" (ident ":" type ("," ident ":" type)* ","?)? "}"
```

field shorthand は型 record では invalid recovery になる。

```yu
{a: A, b: B}
```

### poly variant type

```text
type_poly_variant =
  ":{" (poly_variant_item ("," poly_variant_item)* ","?)? "}"

poly_variant_item =
  ident type*
```

例:

```yu
:{A Int, B}
:{A Int Bool}
```

## pattern

pattern parser は `|` / `as` / `:` を precedence 付きで扱う。
優先順位は低い順に `|`、`as`、type annotation `:` である。

### pattern primary

```text
pattern_primary =
    ident
  | sigil_ident
  | number
  | symbol
  | ":" ident
  | string_or_rule_lit
  | "rule" "{" rule_body "}"
  | "(" pattern_list? ")"
  | "[" pattern_list_or_spread? "]"
  | "{" pattern_fields_or_spread? "}"
```

pattern の `:{name}` ではなく、先頭 `:` は `PolyVariantStart` として `:Name` 形を作る。
`Symbol(":foo")` は `:foo` を 1 token として読める位置で使う。

### pattern tail

```text
pattern_tail =
    "." field
  | "::" ident
  | "as" ident
  | ":" type
  | "|" pattern
  | "(" pattern_list? ")"
  | pattern_primary_as_ml_arg
```

例:

```yu
Foo::Bar
A | B as c: Int
A as x
x: Int
Cons x xs
```

pattern の `(` call も空白なしの場合だけ `ApplyC` になる。空白ありの `(` は
`PatParenGroup` を引数にする `ApplyML` である。

```yu
Some(x)  // ApplyC
Some (x) // ApplyML(PatParenGroup)
```

型付きloweringでは、名前解決できたstruct/enum/error constructor patternは、
constructor関数の通常適用としてpayload型を推測しない。
宣言済みconstructor payloadのsignatureを読み、scrutineeをそのowner型へ制約し、
payload patternの値slotを宣言payload型のlower/upper両側へ接続する。

空白ありの`(`が`PatParenGroup`としてpayloadに来た場合でも、解決済みconstructorのpayload arityが
1ではなく、group内のpattern数がarityと一致するときだけ、そのgroupをpayload列として展開する。
一致しない場合、`PatParenGroup`は通常どおり単一payloadとして扱う。

### pattern list

```text
pat_list =
  "[" ((pattern | ".." pattern) ("," (pattern | ".." pattern))* ","?)? "]"
```

例:

```yu
[head, ..middle, tail]
```

### pattern record

```text
pat_record =
  "{" ((pat_field | ".." pattern) ("," (pat_field | ".." pattern))* ","?)? "}"

pat_field =
  ident
  ident ":" pattern ("=" expr)?
  ident "=" expr
```

例:

```yu
{a, b}
{ width: local_width }
{ width: local_width = 1 }
{ width = 1, ..rest }
```

### string in pattern

pattern 内の通常 `"..."` は rule literal として読まれる。
`"""..."""` のように quote が 3 個以上ある heredoc は `StringLit` として読まれる。

```yu
"hello"          // RuleLit
"hello, :world" // RuleLazyCapture を含む RuleLit
"""hello"""      // StringLit
```

## string literal

string start は `"` を 1 個、または 3 個以上読む。
1 個なら normal string、3 個以上なら heredoc string で、閉じ quote 数は start と同じである。

```yu
"hello"
"""line1
line2"""
```

escape:

```text
\x        // simple escape: next char 1 個
\u{HEX+}  // unicode escape
```

interpolation:

```text
% format_text? "{" interp_body "}"
```

例:

```yu
"%{x}"
"%04{n}"
"%{my x = 41; x + 1}"
"%{ { my x = 41; x + 1 } }"
```

`%` と `{` の間の text は `StringInterpFormatText` になる。
`format_text` が空なら `Display` 表示である。

`format_text` が空でない場合、parser は中身を一つの `StringInterpFormatText` token
として保持し、lowering が次の mini grammar として解釈する。

```text
format_text =
  format_align? format_sign? "#" ? "0"? format_width? format_precision? format_kind?

format_align =
    format_fill? ("<" | ">" | "^")

format_fill =
  any single non-newline character immediately followed by "<" | ">" | "^"

format_sign =
  "+" | "-"

format_width =
  decimal_digit+

format_precision =
  "." decimal_digit+

format_kind =
    "?"  // Debug
  | "x"  // LowerHex
  | "X"  // UpperHex
```

`format_fill` は align marker の直前にある場合だけ読む。
そのため `%04{n}` の先頭 `0` は zero padding、`%0>4{n}` の `0` は fill character
である。

例:

```yu
"%{x}"      // Display
"%?{x}"     // Debug
"%x{n}"     // LowerHex
"%X{n}"     // UpperHex
"%04{n}"    // Display, width = 4, zero_pad = true
"%>8{x}"    // Display, align = right, width = 8
"%_>8{x}"   // Display, fill = '_', align = right, width = 8
"%^10{x}"   // Display, align = center, width = 10
"%.3{x}"    // Display, precision = 3
"%#08x{n}"  // LowerHex, alternate = true, zero_pad = true, width = 8
```

`format_kind` を省略した場合は `Display` である。
`?` は `Debug`、`x` は `LowerHex`、`X` は `UpperHex` を要求する。
`+` sign は format 済み body が `-` で始まらない場合に `+` を先頭へ付ける。
`-` sign は default sign と同じ扱いで、追加の prefix を付けない。

lowering は `format_text` を型推論側の名前分岐へ漏らさず、構造化された
format spec と通常の標準 library 呼び出しへ落とす。
単純な `%{x}` は従来どおり `x.show` へ落としてよい。
`%?{x}` / `%x{n}` / `%X{n}` のような layout 指定を持たない kind-only format は、
それぞれ `x.debug` / `n.lower_hex` / `n.upper_hex` へ直接落としてよい。
width / precision / align / sign / alternate / zero padding を含む場合は、
`std::core::fmt` の formatting protocol に format spec と値を渡す通常呼び出しへ落とす。

interpolation body は、先頭 token が statement block を始める種類なら仮想 brace
statement block として読む。それ以外は `}` を stop にした expression として読む。

statement block として読む先頭 token:

```text
my our pub use mod type struct enum error role impl cast act for
lazy prefix infix suffix nullfix where doc_comment
```

## rule DSL

### rule expression

```text
rule_expr =
  "rule" "{" rule_seq (("|" | newline) rule_seq)* "}"

rule_seq =
  rule_item*
```

rule body 内では ML application は発生しない。空白区切りは PEG sequence の item 並びになる。

rule item:

```text
rule_item =
    ident
  | sigil_ident
  | number
  | string_lit
  | "(" rule_seq (("|" | ",") rule_seq)* ")"
  | "[" expr_list? "]"
```

rule item tail:

```text
rule_tail =
    "=" rule_item
  | "*" | "+" | "?" | "*?" | "+?"
  | "." field
  | "::" ident
  | "(" expr_list? ")"
  | "[" expr_list? "]"
```

実際の quantifier token は `*` / `+` / `?` / `*?` / `+?` である。
rule tail の空白条件は通常 expression と違う。leading trivia が `Space` の tail では
`=` だけが読まれる。quantifier / `.field` / `::` / `(` / `[` は空白なしの場合だけ tail になる。
newline は rule body / rule paren group の separator 側へ返る。

例:

```yu
rule { "hello" }
rule { a b = c(d) e }
rule { a b* | c+ d }
rule { a*? b+? c? }
rule { peg::digit.many }
rule { a=b }
rule { a = b }
```

### rule literal

```text
rule_lit =
  "~\"" rule_lit_part* "\""

rule_lit_part =
    text
  | "{" rule_seq "}"
  | ":" xid_continue+
  | ":{" text_until_close "}"
```

例:

```yu
~"hello"
~"users/{id}"
~"users/{id = ident}/posts"
~"users/:id/posts"
```

pattern 内の通常 `"..."` も `RuleLit` として同じ parser を使う。

## Yumark / quoted mark

Yulang expression では apostrophe の直後が空白なしの `[` または `{` のとき、
quoted mark expression になる。

```yu
'[inline yumark]
'{# Title
}
```

- `'[...]` は `MarkInlineBody`。block 要素は invalid recovery になる。
- `'{...}` は `MarkHeredocBody`。block Yumark document を読む。

`MarkInlineBody` では newline を inline text の継続として読める。ただし newline 後に
heading や list などの block sigil が出ると、その sigil は inline body 内では
invalid recovery になる。

statement doc comment でも Yumark を読む。

```yu
-- inline doc

---
# block doc
---
```

Yumark block scanner が認識する主な block sigil:

- heading: `# `, `## ` など、`#` 1 個以上 + space
- section close: `#.`（inline sigil だが block 位置では `YmSectionClose`）
- code fence: three backticks
- doc block close: `---`
- block quote: `>` または `> `
- unordered list: `- `
- ordered list: digits + `. `
- blank line

Yumark inline scanner が認識する主な inline sigil:

- emphasis: `*...*`
- strong: `**...**`
- bracket inline expression/link text: `[ ... ]`
- image-like inline: `![ ... ]`
- link destination after close bracket: `(url)`
- backslash command/escape sigil: `\`
- close bracket / close brace

`[ ... ]` と `![ ... ]` は `YmInlineExpr` になる。閉じ `]` の直後に `( ... )` が
空白なしで続く場合、`)` または EOF までを `YmLinkDest` として読む。

block 位置の `\ident` は `YmCommand` になる。command 名は通常 identifier scanner で読み、
その後の同じ行は inline text として続く。inline 位置の `\` は現在は専用 escape 展開をせず、
`YmBackslash` sigil として出る。

fence info が `yulang` で始まる場合、その fence body は raw text ではなく
Yulang statement parser で読まれる。
