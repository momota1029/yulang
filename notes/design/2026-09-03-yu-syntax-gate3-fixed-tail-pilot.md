# Draft: yu-syntax Gate 3 fixed-tail pilot

Status: Authoritative

User approval recorded: 2026-09-03。Gate 3 の scope、E2/E3 の境界、direct pilot の
item-handoff 形を承認した。実装はこの文書と親 rewrite plan の範囲に限る。

実装状態: 2026-09-03 に完了した。pilot は production dispatch、legacy parser、Yumark
production bridge から隔離されている。Gate 4 の projection、full call sequence、Expression/RB-E
closure は未着手のまま残る。

Scope: `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md` の Gate 3 を、既に完了した
direct expression/tail pilot の次の一段として具体化する。これは新しい表面文法、production dispatch、
legacy parser の変更を認可しない。

## 1. 正本と gate 境界

正本は recursive-descent rewrite plan の Gate 3、および expression-tail handoff addendum である。
Gate 3 は次の二つだけを扱う。

1. E2: fixed `.` field tail と `::` path tail の直接 pilot。
2. E3 のうち、leading trivia を伴う **現存する outer `)`** を inner expression から wrapper
   owner へ返す borrowed-close witness。

E3 の CallArgument、separator、missing-close recovery はこの gate に含めない。projection (`.(` / `.{`)、
index、full call sequence、terminal colon、全 Expression/RB-E cell は Gate 4 以降に残す。

既存 `grammar::expression`、`grammar::yumark`、public dispatch を呼んだり変更したりしてはならない。
既存 tests の E2/E3 rows は frozen observation として残し、pilot は `rewrite/` 内で直接証明する。

## 2. Item と fixed-tail の分類

`Item` は引き続き leading trivia、identity、extent、logical position、payload を一体で持つ。Gate 3
では `TokenKind` と `TailKind` に次を追加する。

- atomic な `.` Field token と `::` Path token。
- `TailKind::Field` と `TailKind::Path`。
- Gate 4 のために保持する `TailKind::Deferred`。これは既に読んだ一文字の fixed-tail head を
  `Err(Left(item))` で外側へ返すだけであり、recovery や committed output を発生させない。

`::` は必ず一つの current item として消費する。二個の `:` へ分割したり、次 item として stash
したりしない。`.` の直後が `(`、`{`、または `.` の場合は Field として受理せず、`.` だけを
`Deferred` item にして `(` / `{` / 次の `.` は未消費で残す。これは projection と dot-family
の ownership を Gate 4 へ渡すためである。二文字目を item として cache するのではなく、現在 item
の owner を決める lexical 判定だけに使う。

single `:` の terminal/stop 規則は Gate 2 のままにし、Gate 3 は `::` だけを追加する。

## 3. E2 の直接手続き

`rewrite::tail` が受理済み Field/Path を直接所有する。どちらも binding level を持たず、完了後は
`scan_tail_after_accept` へ戻る。従って fixed tail の後の fixed tail、ML tail、binary tail、または
boundary は既存の current-item protocol で一回だけ処理される。

### 3.1 Field

Field branch は leading trivia を `FieldTail` の外へ emit し、`FieldTail` node の中へ `Dot` と
直後の ordinary word を emit する。word は `_` または XID-start で始まり、XID-continue* と
任意の末尾 `?` / `!` を持つ。これは既存 `WordSpan` の語彙を直接、root-range から走査するものであり、
legacy `scan_word` を呼ばない。

word が無ければ `Expression(FieldName)` / `Identifier` の zero-width Missing を FieldTail 内へ
emit する。不正 run があれば同 role/expectation の Error を FieldTail 内へ emit する。どちらも
top-level `OperatorChainItem::MissingOperand` / `Error` は追加せず、AST は
`FixedPostfixTail::Field(FieldTail { name: Recovered::Incomplete, .. })` となる。

### 3.2 Path

Path branch は leading trivia を `PathTail` の外へ emit し、`PathTail` node の中へ `ColonColon`、
post-separator trivia、path segment を emit する。segment は ordinary word または `$` / `&` / `'`
sigil に続く word である。sigil または `_` で始まり `_` そのものではない segment は既存の
`PathSegment::SigilIdentifier` 分類に従う。

RHS 無しは `Expression(PathSegment)` / `Identifier` の zero-width Missing、RHS 不正は同 role の
Error である。AST は `FixedPostfixTail::Path(PathTail { segment: Recovered::Incomplete, .. })` を
持つ。`x:: $name` の separator 後 whitespace は PathTail の子である。

### 3.3 recovery と retry

Field/Path の missing recovery は `StopAtBoundary`、不正 run recovery は `RetrySameSlot` を持つ。
不正 run は whitespace、caller close/stop、`.`, `:`, またはこの pilot が既に認識する tail head
の直前で止まる。一つの recovery record と一つの generic Missing/Error CST node を、受理した
Field/Path owner が即時に publish する。range、diagnostic identity、source order は既存 E2 contract
と一致する。

必要な crate-private API は `FieldTail::new`、`PathTail::new`、read accessor、`PathSegment` の
word からの pure constructor に限る。legacy AST parser や materializer は使用しない。

## 4. E3 borrowed outer-close witness

E3 の追加は call parser の移植ではない。direct pilot に、argument opener を既に所有する caller を
表す小さな `BorrowedArgsOwner` adapter を置く。owner は InlineReference と InlineApply の二種類だけで、
それぞれ既存 `YmYulangArgs` / `YmInlineApplyArgs` node を開く。

adapter は `expr_chain`（root node を開かず `(TailExit, OperatorChain)` を返す既存 nested expression
手続きの sibling）を一回呼ぶ。child が leading space + lexical `)` を持つ
`Err(Right(End { item }))` を返したときだけ、adapter 自身の parenthesis capability で
`BorrowedClose` に変換する。adapter は item の leading trivia と `RParen` を一回だけ emit し、
後続 remainder を untouched で返す。`OperatorChain`、`CallTail`、generic recovery はその close を
emit しない。

この witness の入力行は次の二つである。

```text
\ref(x. )tail
[d]:f(x. )tail
```

いずれも FieldName Missing は space の直前で source-order 0、space+`)` は同一 identity/trivia/
extent/logical position を保つ。`RParen` の direct parent は順に `YmYulangArgs` と
`YmInlineApplyArgs` であり、`tail` は未消費の remainder である。ArgumentList / CallArgument /
separator / closing-delimiter recovery を追加してはならない。

## 5. 受理条件

focused test は少なくとも次を固定する。

| 種別 | literal / assertion |
| --- | --- |
| normal Field/Path | `x.foo::bar::baz` の flat AST source order と FieldTail/PathTail CST |
| spaced path | `x:: $name` の whitespace、sigil segment、range |
| E2 Missing/Error | `x.`, `x.@`, `x::`, `x::123` の role/kind/range/primary `Identifier` |
| same-slot retry | `x::::$name` の Missing Path と次 Path の source order |
| defer | `.(`, `.{`, `..` が recovery/publication 無しで same item handoff になること |
| E3 reference/apply | 上記二 literal の borrowed close owner、leading trivia、recovery order、remainder |
| transaction | rejected fixed tail、Gate 2 layout boundary、selected `R`、frame、`IsCut`、`S` が保たれること |

既存 embedded E2 controls `\ref(x.)`、`\ref(x::123)`、`\ref(x:: 123)`、`[d]:f(x.)` は
変更せず、Gate 3 の observation として残す。E2/E3 の frozen literal や既存 expected output を
現在の出力に合わせて変えてはならない。

## 6. 明示的な非目標と stop 条件

この gate は generic action/materializer、global token stash、source rewind、legacy parser call、
Yumark production bridge、projection migration、E3 item/separator/missing-close、public dispatch を導入
しない。これらのいずれかが必要になった時点で実装を止め、Gate 4 への scope expansion として再設計する。

実装は `crates/yu-syntax/src/rewrite/**` と `grammar/expression.rs` の最小 crate-private constructor
だけを変更する。performance measurement は replay、非線形 scan、新規 hot-path allocation が現れない限り
行わない。verification は focused rewrite table、scoped format/diff check、compiler/recovery と
specification の独立 review に限る。
