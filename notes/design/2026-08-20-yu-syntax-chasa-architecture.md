# `yu-syntax` chasa-based parsing architecture

Status: Proposal。実装、dependency 追加、grammar の拡張はこの文書の scope 外とする。

Revision note: 2026-08-20 のユーザー（chasa 作者かつ Yulang 言語設計者）からの直接 feedback を
反映した。chasa の workspace への取り込み方、operator table の構築時期、full fixity、oracle の
judge table、Rowan CST 構築方法を decision として確定した。

Revision note (broader grammar survey): scanner/layout state の rollback ownership と、header mode の
opaque body scan が operator-independent lexical region を追跡する必要を設計へ反映した。

Revision note (diagnostic closure): header/full reparse の `DiagnosticId` reconciliation を typed
grammar role + parser-native byte range の exact key に固定した。speculative expectation は最遠 group の
typed union を committed recovery record と `SyntaxDiagnostic` に保持し、主表示だけを grammar-role
priority で一件選ぶ。

Revision note (use declaration closure): `yulang2-oracle` の use 専用 scanner / parser と source-level
projection を再照合し、Plain / Mod / Realm / Band の分類、再帰 group、alias、glob、`without` を
表せる Use AST、および group から `HeaderImport` への投影を確定した。version suffix と `with`
anchor は typed syntax として保持するが、source-provider / version resolution の意味は future scope とする。

Revision note (direct full-parse closure): shared recognition core を rollback が必要な local decision に
限定し、accepted branch を recovery 込みで完走する commit-aware continuation と分離した。typed
trivia run、direct Rowan emission、Pratt NUD / LED の probe / commit、canonical `OperatorTable` の
session 構築、および最初の vertical slice に必要な `SyntaxKind` vocabulary を decision として固定した。

Revision note (precedence-neutral operator chain): 2026-08-22 の決定により、dynamic prefix / infix /
suffix operator のbinding powerはCST hierarchyを決めない。本文中のPratt-shaped CST、left-wrap
checkpoint、`Expression::{Prefix,Infix,Suffix}Application`をcurrent designとして述べる箇所は、末尾の
「dynamic operatorのprecedence-neutral surface chainとassociation境界」追補がsupersedeする。operator
spelling / fixity roleのoracle judge、immutable table、sink-free probe、direct emissionは維持する。

Revision note (colon-application closure): precedence-neutral chain追補が予約した
`ColonApplicationTail`について、inline expression list、indented statement block、outer comma ownership、
terminal-chain integration、recoveryを末尾の「lone `:`によるcolon application」追補で確定した。

Revision note (`if`-expression closure): `if` / `elsif` / `else`をterminal colon tailではなく
NUD-positionの`PrimaryExpression`として位置づけ、condition stop、colon-owned single body、既存
`IndentedStatementBlock` reuse、arm continuation、recoveryを末尾の`if`-expression追補で確定した。

Revision note (braced statement-block primary closure): ordinary NUD-positionの`{ statement* }`を、
overloadedなhistorical `BraceGroup`ではなく`BracedStatementBlockExpression`として分離した。comma / semicolon /
implicit-newline separator、empty / trailing-separator validity、shared statement-sequence core、closing recoveryを
末尾のbraced statement-block追補で確定する。

Revision note (first pattern-grammar slice): expression `OperatorChain`とは独立したfixed-precedence pattern Pratt
familyを追加し、identifier / sigil identifier、decimal integer、contiguous symbol、layout-aware comma-or-newline parenthesized pattern、
`as` alias、`|` alternationまでを末尾のpattern追補で確定する。case / catchを含むconsumer wiringと、未成立の
list / type / string-rule / record / constructor-application grammarはfuture scopeへ分離する。

調査対象は `chasa 0.5.0` と、annotated tag `yulang2-oracle` が指す commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`（以下 `yulang2-oracle@a58eefc3`）である。
`chasa` の source は local Cargo registry cache に展開済みだったため、network access は
使っていない。

## Decision summary

`crates/yu-syntax` の full parser は、source 全体を先に
`Vec<LexedToken>` へ materialize する構成を廃止し、`chasa` の `Input<Item = char>` を
grammar が直接消費する構成へ置き換える。

> **Status: 2026-08-22 superseded.**
> 直後のPratt / precedence-climbing維持という段落は、最初のdirect-expression sliceのhistorical decisionである。
> current decisionではNUD / LED positionとoracle judgeによるoperator role recognitionだけを維持し、
> numeric binding powerによるapplication treeの構築はHIR lowering前後のdedicated associatorへ移す。

expression parser は Yulang2 の tagged predictive NUD / LED dispatch と Pratt /
precedence climbing を維持する。ただし operator token は独立 lexer が確定せず、現在の
grammar position（NUD または LED）と immutable session `OperatorTable` を渡された operator scanner が、
character stream 上で spelling、fixity、boundary、後続条件を同時に判定する。

header discovery の現在の二 pattern は context-dependent operator tokenization を必要とせず、
この問題だけについては壊れていない。それでも §4.2.2 の shared grammar authority と
header/full parity を満たすため、`scan_header` も同じ chasa-based scanner と declaration
grammar を restricted mode で呼ぶ構成へ移す。

chasa は crates.io の normal dependency として `=0.5.0` に exact pin する。README が experimental と
している API が通常の `cargo update` で暗黙に更新されないようにしつつ、source を repository に
vendor / copy しない。通常の grammar alternation は `choice` / `or` で表し、明示的な checkpoint /
rollback は、追加 input を読むまで構造的に候補を確定できない場合だけに限定する。

operator declaration は source-leading header に限定される。header discovery が commit した
local operator fact と imported `SyntaxEnvironment` から、full parse 開始前に full-fixity の
`OperatorTable` を一度だけ構築し、parse 中は immutable に参照する。表現は最初の vertical slice
から Yulang2 の `BpVec` と同等の prefix / infix / suffix / nullfix 全 capability を持つ。

CST event buffer と parse 後の replay は置かない。speculative branch には Rowan sink を渡さず、
branch decision が commit された後だけ `GreenNodeBuilder` へ node / token を直接書く。
`longest_match_then` の operator-candidate 探索は input、expectation、軽量な local bookkeeping、
rollback-aware な scanner/layout state を同じ checkpoint で戻す。CST を一度も書かないため、Rowan
structure の rollback は不要である。

header/full の diagnostic identity は、同じ `SourceRevision` 内の typed `GrammarRole` と parser-native
UTF-8 byte range の exact match で照合する。exact match した committed header record は ID と表示内容を
そのまま再利用し、role/range が異なる record は message が同じでも full-origin の新しい ID とする。

recovery commit 時には、`LatestSink` が保持する最遠 active expectation group の distinct candidate を
typed union として全件凍結する。public diagnostic もその union を保持し、主メッセージだけを committed
site との role affinity、明示的な stable tie-break key の順に一件選ぶ。parser branch order や表示文言は
選択規則に含めない。

use declaration は、先頭 word だけを path へ積む flat loop ではなく、use 専用の predictive state
machine で読む。`mod` は use grammar 内の contextual keyword、`realm` / `band` は一般 identifier であり、
それぞれ `realm` + `/`、`band` + `::` の先頭 pattern のときだけ form marker とする。再帰 group は
structured `UseTree` のまま保持し、header fact commit 時に source order で独立した import record へ
展開する。`use mod` は syntax 層では form を保持するだけで、module declaration や source set を
その場で合成しない。

## Problem statement

dynamic operator table に次を登録する。

- infix operator `+!`
- prefix operator `+`
- prefix / nullfix capability を持つ operator `!`

このとき、同じ character run `+!` は grammar position により異なる token boundary を持つ。

```yu
+!a    # + (! a): prefix `+` と prefix `!`
a+!b   # a +! b: infix `+!`
```

`+!a` の先頭は operand をまだ持たない NUD position である。したがって infix-only の
`+!` は使えず、scanner は短い prefix `+` まで戻る必要がある。その直後の `!` は次の
NUD position で prefix operator になる。一方、`a+!b` の `+!` は operand の後の LED
position にあり、最長の infix `+!` が一 token になる。

これは character class と maximal munch だけでは決まらない。token boundary の決定に
「左 operand をすでに読んだか」という parser state が必要だからである。独立 lexer が先に
全 token を確定するには parser position を暗黙に再構築する必要があり、実質的に parsing を
二重化する。

現行実装では、`crates/yu-syntax/src/lib.rs:502-568` の `scan_token`、
`scan_symbol_end`、`starts_distinct_item` が grammar position を受け取らず、symbol character
run を常に greedy に一つの `TokenKind::Symbol` とする。さらに
`crates/yu-syntax/src/parse.rs:320-342` の `lex` がその結果を source 全体について
`Vec<LexedToken>` に固定し、`FullCstBuilder` が `token_index` で後から歩く。この構成では
`+!a` と `a+!b` の両方を正しく扱えない。

## Scope and non-goals

この proposal が決めるものは次である。

- chasa を使う input、scanner、grammar、committed recovery record、direct Rowan sink の責務境界。
- dynamic operator spelling を NUD / LED position で解決する経路。
- header discovery と full parse が shared declaration grammar を使う経路。
- 現在の `HeaderCursor`、`lex`、`FullCstBuilder` のうち残す概念と廃止する実装。
- 実装開始前に固定すべき test と未決定事項。

この slice では次を行わない。

- `chasa` を `Cargo.toml` に追加しない。
- `crates/yu-syntax/src/*.rs` を変更しない。
- expression grammar、recovery、diagnostic、operator table を実装しない。
- Yulang2 parser 全体をそのまま移植しない。
- §18 に残る late `use` / source-set expansion の意味を決めない。

## `chasa 0.5.0` の実 API と design

### Parser values and execution

parser は `ParserOnce`、`ParserMut`、`Parser` のいずれかを実装する value であり、出力は
`Option<Out>` である。`Some` が success、`None` が failure を表し、diagnostic は返り値と
分離された `ErrorSink` に入る。closure は `from_fn_once`、`from_fn_mut`、`from_fn` を通じて
同じ parser trait を実装できる。

主要 combinator は `choice` / `or`、`then` / `seq` / `left` / `right`、`map` / `bind`、
`many` / `sep`、`maybe`、`lookahead`、`not`、`with_range` / `with_span` / `with_seq`、
`label` である。`tag`、`item`、`one_of`、`satisfy` は input item を読む primitive である。

簡単な parser は `Input::test` / `test_with_errors` で走らせられる。Yulang2 のように
environment と sink を持つ parser は、`In::new(input, errors, IsCut)` を作り、`set_env` /
`set_local` した `In` を public entrypoint に渡して駆動する。

### Input, checkpoints, and state

`Input` は `Back` を supertrait に持ち、`Item`、`Pos`、`next`、`checkpoint` / `rollback`、
`commit` を提供する。`SeqInput` は二 checkpoint 間の consumed sequence を `seq` で返す。
`&str` は `Input<Item = char>` と `SeqInput<Seq = &str>` を実装しているため、intermediate
token vector を作らず character stream を直接 parse できる。

`In<I, N, L, E>` は次を一つの parser argument に束ねる
（`chasa-0.5.0/src/input/mod.rs:89-303`）。

| field | role | automatic rollback |
| --- | --- | --- |
| `input` | current character stream | yes |
| `env` | shared parser environment | no |
| `local` | speculative mutable state | yes |
| `errors` | parser expectation sink | combinator が別 checkpoint で制御 |
| `is_cut` | commit propagation | capture scope ごとに制御 |

`In::checkpoint` が保存するのは input checkpoint と `local: RbBack` の checkpoint であり、
`env` ではない。この差は scope、diagnostic、header fact を置く場所の design に直結する。
rollback されるべき mutation を `env` に置いてはならない。一方、direct CST sink は rollback
対象にせず、speculative parser から型/API 上アクセスできないようにする。

`with_seq` は parse 前後の input checkpoint を使い、実際に消費した source slice を返す。
Yulang2 scanner は identifier、number、operator、punctuation、trivia の text をこの方法で
得ている。

`WithCounter<I, C>` は input と position counter の checkpoint を一緒に戻す。ただし標準の
`usize: Counter<char>` は一 character ごとに 1 増える。Yulang3 の public range は UTF-8 byte
offset なので、そのまま diagnostic / header range に使わず、`char::len_utf8()` を加算する
byte counter か byte offset を持つ custom source input が必要である。

### Rollback and cut

chasa の choice/repetition policy は「cut されていない failure なら checkpoint へ戻る」である。

- `choice` は最初の branch 前に input/local と error sink の checkpoint を取り、branch が
  `None` かつ uncut なら rollback して次を試す。cut 後の `None` は hard failure になる
  (`parser/choice.rs:174-205`, `218-345`)。
- `maybe` は uncut failure を rollback して `Some(None)` に変える。cut failure は `None` の
  まま伝播する (`input/mod.rs:447-477`)。
- `lookahead` は success 時にも input/local を戻し、成功 probe の expectation error を消す。
  cut failure だけは rollback しない (`input/mod.rs:396-423`)。
- `many` / `sep` も同じ hard-failure distinction を使う。
- `cut` は現在位置で commit flag を立てる。root cut では `Input::commit` も呼ぶ。
- `cut_on_ok(p)` と `cut_after(p)` は 0.5.0 では同じ `CutIfOk<P>` で、`p` が成功した後だけ
  cut する (`parser/prim.rs:974-1118`)。
- `uncut(p)` は内側の cut を caller へ伝播しない isolated cut scope を作る。

operator candidate を探索している途中では cut してはならない。長い spelling が現在の
fixity で無効だったとき、短い candidate へ戻る必要があるからである。declaration keyword と
必須 introducer を確定し、別 branch ではあり得ない地点に達してから cut する。

### Implementation discipline: `choice` / `or` を通常経路にする

通常の構文上の選択は chasa の `choice` / `or` combinator で表す。手書き checkpoint / rollback を
alternation の標準手段にしてはならず、`choice` / `or` を避けるために独自 dispatcher や rollback
wrapper を増やしてはならない。

明示的な checkpoint / rollback を使ってよいのは、追加 input を読むまで構造的に候補を確定できず、
長い候補を試した後で短い候補の末尾へ戻る必要がある場合だけである。この proposal では
`longest_match_then` による operator-candidate 探索が該当する。これは rollback を他の grammar
branch に広く使ってよいという許可ではない。新しい明示的 rollback を追加する implementation は、
なぜ `choice` / `or` では表せず、どの有限な曖昧区間だけを戻すのかを code review で説明する。

### Trie matching

chasa は operator table storage 自体を提供しない。`parser::trie::TrieState` は、item を一つ
進める `step` と、現在の path が完全な key のとき value を返す `value` だけを要求する
adapter trait である。caller が storage を用意する。

`TrieState::longest_match` は最長 key を返す。今回より重要なのは
`longest_match_then` である。完全な key に達するたびに、まずさらに長い key とその
continuation callback を `maybe` で試す。長い候補の callback が失敗し、その失敗が uncut
なら input を現在の短い候補の末尾へ戻し、短い候補の callback を呼ぶ
(`parser/trie.rs:156-182`)。

したがって callback は「trie に spelling があるか」だけでなく、word boundary、fixity、
whitespace、後続 expression start など grammar position 固有の条件を検査できる。これが
Yulang の context-dependent operator token boundary に直接必要な primitive である。

### Diagnostics

`LatestSink` は最も先へ到達した expectation group を保持し、error sink 自体も checkpoint /
rollback できる。これは speculative scanner error を branch 外へ漏らさないために有効である。

一方、§4.2.2 の exhaustive `SyntaxDiagnostic` は chasa の `LatestSink` だけでは満たせない。
`LatestSink` は parser failure の expectation authority であって、recovery episode、
`Missing` / `Error` node、stable `DiagnosticId` の authority ではない。Yulang3 では
speculative expectation sink と committed recovery/diagnostic log を分ける。

## `yulang2-oracle` の operator parser

### Live operator table

`yulang2-oracle@a58eefc3:crates/parser/src/op.rs:138-216` は `qp_trie` を storage に使う
`OpTable` を定義し、その traversal state を chasa の `TrieState<Item = char>` へ適合させる。
一つの `OpDef` は同じ spelling に対する prefix、infix、suffix、nullfix capability をまとめる。

parser-wide mutable `State` は `ops: OpTable` を持つ
(`crates/parser/src/context.rs:20-35`)。operator declaration parser は name、fixity、binding
power が読めた時点で table を更新する
(`crates/parser/src/stmt/op_def.rs:159-162`, `245-284`)。full parse entrypoint は caller から
渡された operator table を `Env` へ入れる
(`crates/parser/src/lib.rs:61-117`)。したがって expression scanner が参照するのは fixed
lexical table ではなく、その parse session の live syntax environment である。

### NUD and LED select different scanners

Pratt entrypoint `parse_expr_bp` は operand 前に `scan_expr_nud` を呼ぶ
(`crates/parser/src/expr/core.rs:31-38`)。operand を構築した後の tail loop は
`scan_expr_led` を呼ぶ (`crates/parser/src/expr/tail.rs:21-35`)。

両 scanner は primitive scanner の choice より先に operator scanner を試すが、別 entrypoint
を使う。

- NUD: `scan_op_nud` -> `judge_nud`; infix と suffix capability を候補から除く
  (`expr/scan.rs:112-120`, `expr/scan/op/judge.rs:3-14`)。
- LED: `scan_op_led` -> `judge_led`; infix / suffix に加え、multiline argument として使える
  prefix / nullfix も context と whitespace から判定する
  (`expr/scan.rs:264-275`, `expr/scan/op/judge.rs:16-30`)。

`scan_op_with_trie` は live table の state に `longest_match_then` を適用する
(`expr/scan/op/scan.rs:32-81`)。各 complete spelling の callback は次を検査する。

1. identifier-like word operator の末尾 boundary。
2. operator 前後の trivia と EOF / expression stop。
3. call / path と衝突する operator form。
4. 後続が value start かという lookahead。
5. NUD / LED 固有の `judge` table による `OpUse`。

採用した spelling の source text は input checkpoint 間の `I::seq` から得る
(`expr/scan/op/scan.rs:40-46`, `81-105`)。先に作られた symbol token を切り直しているのではない。

### `+!a` / `a+!b` の intended traversal

上記構造が意図する traversal は次である。

`+!a`:

1. expression start なので NUD scanner が走る。
2. trie は `+` を complete candidate として覚えたまま `+!` まで進む。
3. `+!` は infix-only なので `judge_nud` が拒否する。
4. `longest_match_then` 内の `maybe` が input を `+` の直後へ戻す。
5. `+` は prefix candidate で、直後の `!` も prefix value start なので採用する。
6. prefix RHS の recursive NUD scanner が `!` を prefix として読む。

`a+!b`:

1. `a` を読んだ後なので LED scanner が走る。
2. trie は `+` より長い `+!` まで進む。
3. `+!` の infix capability と後続 `b` が LED 条件を満たすため、最長 candidate を採用する。

### Tagged oracle の judge table と調査 fixture

`yulang2-oracle@a58eefc3:crates/parser/src/expr/scan/op/scan.rs:153-167` の
`op_value_start_inner` は、次の predicate を使う。

```rust
kinds.contains(OpKindSet::PREFIX | OpKindSet::NULLFIX)
```

この `contains` は `PREFIX` と `NULLFIX` の両 capability があることを要求する。これは oracle で
確定済みの judge-table semantics であり、Yulang3 は experimental な OR variant へ変えず、
whitespace/fixity judge table とともにこの logic をそのまま採用する。

先の調査では、infix `+!` と prefix-only `+` / `!` を一時 `OpTable` に登録したため、`a+!b` は
`Infix "+!"` として成功した一方、`+!a` の先頭 `+` は `Unknown` / `InvalidToken` へ落ちた。
predicate を `PREFIX || NULLFIX` に変えると両方が成功したが、この結果は oracle の bug を示さない。
調査側が oracle の judge table と異なる fixity 集合を fixture に与えた artifact と考えるべきである。

したがって eventual `+!a` / `a+!b` fixture では、operator spelling ごとの declaration を先に
canonical に固定し、value-start 判定対象の operator が prefix と nullfix のどちらを、または両方を
持つかを明記する。fixture の宣言を確認せずに parse result だけから judge predicate を変更しては
ならない。chasa の character input + `longest_match_then` + uncut rollback が候補境界を戻せることと、
どの fixity 集合を value start と認めるかは別の論点である。

## Rowan CST bridge in `yulang2-oracle`

chasa 自体は Rowan を参照しない。bridge は parser crate の `Lex` と `EventSink` が担う。

`Lex` は token kind、token text、leading trivia summary、lossless trailing trivia を持つ
(`crates/parser/src/lex.rs:416-458`)。scanner は `with_seq` / `I::seq` で consumed source text
を得て `Lex` を返す。parser grammar は次の event を sink へ送る。

- `start(SyntaxKind)`
- `lex(&Lex)`
- `finish()`

`GreenSink` は `rowan::GreenNodeBuilder` を所有し、start/finish を
`start_node` / `finish_node` へ、`Lex` を `token` へ写す
(`crates/parser/src/sink.rs:70-153`)。`lex` は token 本体の直後に `trailing_trivia` の全 part も
Rowan token として出す。file 先頭の trivia は entrypoint が一度だけ先に sink へ渡す
(`crates/parser/src/lib.rs:77-91`)。これが direct char parser でも source text を lossless に
保つ concrete precedent である。

oracle の `State.sink` は chasa の `env` 内にあり、`In::checkpoint` の rollback 対象ではない。
oracle は scanner choice を CST emission 前に終わらせ、grammar-level subtree backtracking を
避ける predictive parser なので、CST を戻す必要がない。Yulang3 もこの sequencing を採用し、
さらに speculative parser から direct sink への access を型/API で除く。

## Current `scan_header` exposure

### Direct answer

現行 `scan_header` の二つの narrow pattern は、context-dependent operator-symbol
tokenization の問題には直接さらされていない。

leading plain `use` は word/path component と dot だけを読む。single-line infix header は
`(` を読んだ後、`HeaderCursor::consume_operator_name` が matching `)` の直前までの source
slice を operator name として返す (`crates/yu-syntax/src/lib.rs:257-283`, `400-415`)。
operator name 内の `+!` を prefix/infix token へ分類しない。body は現 slice では newline
まで opaque に消費するだけである (`lib.rs:422-435`)。body 内の `+!a` が一つの
`TokenKind::Symbol` になっても、その body を式として解釈していないため header fact は変わらない。

これは current scope に限定した答えである。現 `scan_header` は malformed header 後の recovery、
full fixity set、group import、comment/trivia、balanced multiline opaque body をまだ実装していない。
また full parser が header range を CST node boundary として再利用するだけでは §4.2.2 の
「同じ grammar authority」にはならない。したがって、operator ambiguity が今の
`scan_header` を壊していないことは、`HeaderCursor` を architecture authority として残す理由に
ならない。

## Proposed `yu-syntax` architecture

### Workspace integration

implementation change では、`yu-syntax` から crates.io の normal dependency として chasa `=0.5.0` を
参照する。ユーザーの直接確認（2026-08-20）により、chasa source を Yulang repository に vendor / copy
せず、workspace member や path dependency にもしない。exact pin により experimental API が通常の
`cargo update` で暗黙に更新されることを防ぐ。

### Module and responsibility layout

public entrypoint と主役の product は見つけやすい位置に残し、implementation を次の責務へ分ける。

```text
src/
  lib.rs                 public products and re-exports
  header.rs              scan_header orchestration
  parse.rs               parse_file orchestration
  input.rs               byte-positioned chasa source input
  session.rs             ParseEnv, lightweight ParseLocal, committed CST capability
  operator.rs            OperatorTable and chasa TrieState adapter
  sink.rs                direct GreenNodeBuilder bridge and range validation
  scan/
    mod.rs               shared scanner entrypoints and lexical authority
    trivia.rs
    word.rs
    punctuation.rs
    operator.rs           NUD/LED-aware operator matching
    opaque_body.rs
  grammar/
    mod.rs               shared statement-start dispatch
    declaration.rs        shared use/operator header grammar
    expression/
      mod.rs             public expression wiring
      scan.rs
      pratt.rs
    recovery.rs           consume-or-stop and Missing/Error emission
```

これは最終 file 数の固定ではなく、責務 boundary の proposal である。`utils` / `common` のような
用途不明な module は作らない。最初の vertical slice では `declaration.rs` と最小 expression
module だけを作り、grammar family を必要になる前から空 file に分割しない。

### Source input

`SourceInput` は source 全体への reference と current remainder / byte offset を持ち、chasa の
`Back`、`Input<Item = char, Pos = usize>`、`SeqInput<Seq = &str>` を実装する。checkpoint は
remainder と byte offset の小さな copy であり、source text を clone しない。

別案として `&str.with_counter(Utf8ByteCounter)` を使える。どちらの場合も次を contract とする。

- `Pos` は UTF-8 byte offset。
- `seq(start, end)` は元 source の contiguous slice。
- rollback は input と byte offset を同時に戻す。
- full parse は source 全体を一つの `Vec<LexedToken>` へ変換しない。
- scanner result と direct sink は copied `Box<str>` より source `Range<usize>` を受け渡す。

### Parse environment and non-emitting speculative state

chasa の `env` と `local` を意図的に分ける。

`ParseEnv` は speculative branch で mutation しない data を持つ。

- original source
- `ParseMode::{Header, Full}`
- selected `SyntaxEnvironment`
- full mode では、header discovery 後、full parse 開始前に一度だけ構築した immutable `OperatorTable`
- full parse が照合する `HeaderInfo`
- immutable lexical/statement-start authority

`ParseLocal` は rollback される mutable state を持ち、cheap checkpoint を実装する。ここで ownership は
例示ではなく、次の binding rule で決める。

> scanner または layout decision が読む値のうち、speculative な input consumption の結果として
> 変化し得るものは、必ず `ParseLocal`、または `ParseLocal::Checkpoint` と同じ checkpoint / rollback に
> 参加する明示的に scoped な substate が所有する。`ParseEnv` の interior mutation や committed sink に
> 逃がしてはならない。expression 固有に見える state も例外にしない。

現在分かっている scanner/layout-affecting state の完全な inventory は次である。今後 grammar に
scanner/layout decision を追加するときも、名前をこの list に当てはめるのではなく、上の rule で
rollback ownership を判定する。

- 直近に消費した physical newline と current line の indentation を表す `line_indent` / line-start state。
  oracle の `scan_trivia` は trailing trivia の消費だけで `line_indent` を更新する
  (`yulang2-oracle@a58eefc3:crates/parser/src/scan/trivia.rs:13-48`)。したがって trivia を読んだ probe が
  failure した場合、この値も input position と同時に戻らなければならない。
- active block と `:` / `=` などの introducer が定める indentation baseline。単一 scalar へ場当たり的に
  上書きせず、nested scope を表す baseline stack / scoped frame として所有する。
- expression と type の tail continuation を変える `inline` / `ml_arg` mode flag
  (`expr/tail.rs:21-45,273-319`, `typ/parse.rs:194-205,320-338`)。
- grammar の stop-set stack と、`()` / `[]` / `{}` の delimiter stack。outer stop の suspend を含む
  scope change は、失敗 branch の外へ漏らさない。
- Yumark の inline / quoted / block mode、quote depth、line-document continuation、fence kind と
  continuation state (`mark/scan.rs:76-201`)。
- embedded lexical mode stack。少なくとも line comment、nested block comment、normal string、opening
  quote count を sentinel とする heredoc、string interpolation とその local delimiter depth、`~"..."`
  rule literal、quoted / block Yumark、raw / Yulang fence body、および各 region の terminator / nesting
  state を含む。この state は full scanner だけでなく header-mode opaque body scanner も共有する。

scanner/layout state 以外では、staged header fact transaction と operator candidate probe の一時的な
bookkeeping も `ParseLocal` が所有する。

`ParseLocal::Checkpoint` は大きな structure の clone ではなく、scope stack depth と header fact
transaction の length、scalar mode の旧値のような小さな snapshot を保存する。stop / delimiter /
lexical-mode stack は depth の truncate、top frame の mutation は value restore で正確に戻す。
rollback は input position とこれらすべてを一つの operation で restore する。
operator table は `ParseLocal` に置かず、overlay checkpoint も持たない。§4.2.2 の
`HeaderInfo` は source-leading syntax preamble の operator fact をすべて header discovery で確定する。
full parser はそれらを parse 中に追加せず、immutable table を参照するだけである。

direct Rowan sink と committed recovery/diagnostic log は rollback 対象にしない。speculative parser
には input、`ParseLocal`、expectation sink だけを渡す `Probe` capability を与え、CST emission API を
与えない。branch introducer と token boundary が確定した後の parser だけが `CommittedCst` capability
を受け取り、direct sink と committed recovery record を更新できる。この分離により、rollback は
input と軽量 local state だけを戻し、すでに書いた CST や public diagnostic を戻す経路を作らない。

chasa の `ErrorSink` には speculative expectation を置く。recovery が path を確定した時だけ、
期待情報を committed recovery record へ変換する。branch failure の expectation を
`SyntaxDiagnostic` として直接 publish しない。

### Scanner and grammar boundary

scanner は「常に同じ token stream」を返す独立 phase ではない。grammar が現在必要とする
token class の parser を呼ぶ。

word、number、fixed punctuation、trivia は shared char combinator で読む。keyword table は一箇所を
authority とし、scanner、statement dispatch、diagnostic が別の spelling list を持たない。

operator scanner の API は概念的に次の情報を受ける。

```rust
enum OperatorSite {
    Nud,
    Led,
}

fn scan_operator(
    site: OperatorSite,
    leading: TriviaInfo,
    input: In<'_, SourceInput, ParseEnv<'_>, &'_ mut ParseLocal, ParseErrorSink>,
) -> Option<ScannedOperator>;
```

実際の generic signature は chasa / reborrow 制約に合わせる。重要なのは `site` と session table が
token boundary 決定前に渡ることである。ここでいう session table は parse 中に mutate する table では
なく、その file の imported operator と committed header operator を反映して full parse 前に
完成した immutable table である。

`OperatorTable` と `HeaderOperator` は最初の vertical slice から Yulang2 の `BpVec` と同等の
full-fixity representation を持つ。同じ spelling に prefix、infix、suffix、nullfix の capability と
binding power を同時に保持できなければならない。infix + `u16` pair だけの暫定 representation を
作って後で拡張する経路は採らない。

`scan_operator` は `OperatorTable::state().longest_match_then(...)` を使い、candidate callback で
boundary、fixity、whitespace、value-start lookahead を検査する。NUD callback は prefix /
nullfix だけ、LED callback は infix / suffix と grammar が許す argument form だけを認める。
value-start operator 判定を含む whitespace/fixity judge table は oracle の logic をそのまま採用する。
特に `op_value_start_inner` の `contains(PREFIX | NULLFIX)` を OR 条件へ書き換えない。

candidate が確定するまで CST node / token を emit せず、cut もしない。確定後に token range と
trailing trivia を `ScannedOperator` として返す。caller の predictive branch が operator use を
採用した後にだけ direct sink へ書き、必要ならその branch の introducer に cut を置く。

### Expression parser

> **Status: 2026-08-22 partially superseded.**
> 以下はYulang2のactual algorithmを記録するhistorical調査として維持する。ただし
> 「Yulang2のalgorithmを維持する」というYulang3 decisionは末尾のprecedence-neutral chain追補が
> supersedeする。operator role scannerとoracle judgeだけを引き継ぎ、Pratt CST shapeは引き継がない。

Yulang2 の algorithm は維持する。

1. `parse_expr_bp` が NUD scanner を呼ぶ。
2. NUD tag に応じて atom / group / prefix subtree を作る。
3. prefix RHS は prefix binding power を `min_bp` として recursive parse する。
4. operand 完了後、tail loop が LED scanner を呼ぶ。
5. infix / suffix binding power と `min_bp` を比較し、Pratt continuation を進めるか caller へ返す。

この「NUD scanner を呼んでいるか、LED scanner を呼んでいるか」が operator tokenization の
parser state そのものである。別 lexer state machine を追加しない。

grammar-level subtree backtracking は避ける。通常の keyword / punctuation / statement alternation は
`choice` / `or` で構成し、明示的な chasa rollback は `longest_match_then` のように追加 input まで
候補境界が確定しない局所 token-level decision に限定する。これにより source 全体を暗黙に二度
parse せず、operator run の長さに比例する局所 probe だけを行う。

### Header discovery and full parse

`scan_header` と `parse_file` は別 phase product のまま維持する。これは §4.2.2 が必要とする
syntax planning の boundary であり、独立 lexer + parser の二重化とは異なる。

両 entrypoint は同じ `grammar::declaration` と shared statement-start classification を使う。

Header mode:

1. source 先頭から trivia と header starter を読む。
2. shared `use` / operator-header grammar を restricted mode で呼ぶ。
3. mandatory field が一意に確定した declaration fact だけを transaction commit する。
4. operator body は expression parse せず、operator-independent lexical region、delimiter、indentation を
   追跡する shared opaque scanner で次の top-level boundary まで進める。
5. 最初の non-header starter は normal stop とし、error にしない。
6. `HeaderInfo` に coverage、facts、header-origin diagnostics を凍結する。partial GreenNode は返さない。

ここで `opaque` は lexical structure まで無視するという意味ではない。tagged oracle の
`skip_op_def_body` は `scan_stmt_lex` を繰り返しながら `()` / `[]` / `{}` の単一 depth と indentation
だけを追跡する (`stmt/op_def.rs:216-242`)。しかし `scan_stmt_lex` の choice は string、rule literal、
Yumark を独立 lexical region として認識しない (`stmt/common.rs:14-27`)。この形をそのまま port しては
ならない。

shared opaque scanner は direct character stream 上で、外側の delimiter / layout boundary より先に
次の operator-independent lexical region を認識し、region stack と mode-specific terminator を追跡する。

- line comment と nested block comment。block comment の `/* ... */` depth は独立に追跡する
  (`scan/trivia.rs:117-190`)。
- normal string と heredoc。heredoc は opening quote count を保持し、同じ count の quote sequence だけを
  terminator とする (`string/scan.rs:10-17,31-98`)。
- `%{...}` interpolation。outer operator body の brace depth とは別に interpolation-local delimiter を
  balance し、その中で始まる nested lexical region も同じ stack で扱う。
- `~"..."` rule literal。
- quoted / block Yumark と、その quote depth / document continuation。
- raw fence body と Yulang fence body、および各 fence 固有の closing sentinel。

lexical region 内では、region 自身の terminator / nesting を見つける処理を除き、outer body の
delimiter depth と indentation-based boundary detection を suspend する。region stack が空のときだけ
`()` / `[]` / `{}` の outer depth を更新し、depth 0 かつ base indentation 以下の newline を次の
top-level boundary 候補にする。これにより heredoc 内の newline や、ordinary string、interpolation、
rule literal、Yumark、fence body 内の brace を declaration boundary と誤認しない。

この scanner は region の中身を expression として parse せず、dynamic operator spelling / fixity も
判定しない。operator-independent な lexical terminator と nesting だけを boundary detection のために
読むので、header mode を軽量に保つ原則と direct-character-stream architecture の両方を維持する。

Full mode:

1. `HeaderInfo` の committed local operator fact と imported `SyntaxEnvironment` から、full-fixity の
   parse-session `OperatorTable` を一度だけ構築する。partial / uncommitted header fact は含めない。
2. immutable table を `ParseEnv` に置いてから、source 先頭の header declaration を同じ shared
   grammar で再度読む。full parse 中に operator table を更新しない。
3. shared grammar が独立に得た full header projection を `HeaderInfo` と range / path / visibility /
   operator shape で照合する。不一致を silent overwrite しない。
4. body を integrated scanner + grammar で最後まで parse し、committed recovery record と
   diagnostics を集める。
5. header-origin diagnostic は同じ `DiagnosticId` を一度だけ final list に取り込む。

この構築順は §4.2.2 / §18 と照合済みである。§4.2.2 は `HeaderInfo` を source 先頭の syntax
preamble（leading `use` と dynamic operator header）に限定し、§18 が本文側に残す未決定事項は
late `use` / `mod` による semantic dependency と source-set expansion だけである。operator の
別 declaration point は記載されていない。したがって operator declaration は header-scoped とし、
full parse 中の rollback-aware mutable overlay は設計に含めない。

full parse は `HeaderInfo` の range を使って pre-tokenized source を node で包むのではない。
`HeaderInfo` は expected parity input と syntax planning product であり、full CST grammar の代替ではない。

### Direct Rowan sink without parse-event buffering

> **Status: 2026-08-22 partially superseded.**
> direct sink、commit後だけのemission、event buffer / replay禁止は維持する。下記のうち
> Pratt left operandを`start_node_at`でapplication nodeへ包む用途だけを末尾のflat-chain追補がsupersedeする。

`ParseEvent` enum、event buffer、parse 後の Rowan replay layer は作らない。full grammar は branch
decision が確定した後だけ、専用 direct sink を通じて `GreenNodeBuilder::start_node`、`token`、
`finish_node` を呼ぶ。token text は scanner が返した source `Range<usize>` から
`&source[range]` を取り、別の token text buffer を作らない。

この制約は運用上の注意だけにせず、型/API で分ける。

- `Probe` parser は input、rollback-aware な軽量 `ParseLocal`、expectation sink だけへ access でき、
  `GreenNodeBuilder` や recovery emission API を持たない。
- `CommittedCst` parser は branch introducer、operator spelling/fixity、または recovery path が
  確定した後にだけ作られ、direct sink を更新できる。
- `choice` / `or` の speculative arm と `longest_match_then` callback は `Probe` capability で走り、
  accept した scanner result を caller へ返す。caller が commit した後に初めて CST を emit する。

特に operator-candidate 探索中は `builder.start_node` / `builder.token` を一度も呼ばない。探索は
input position、expectation、candidate range、および scanner/layout に影響する `ParseLocal` state を
checkpoint / rollback する。definite spelling と fixity が選ばれた後、その operator token と構文 node を
direct sink へ一度だけ書く。rollback 前に CST structure が存在しないため、CST rollback や
buffer/replay は不要である。

Pratt parser が出力済みの left operand を後から infix / suffix node で包むときは、left operand を
書く直前に `GreenNodeBuilder::checkpoint` を取得し、LED candidate の採用後に
`start_node_at(checkpoint, kind)` を呼ぶ。この Rowan checkpoint は既存 child を親で包む位置を示す
handle であり、speculative CST を巻き戻す marker ではない。従来案の `Marker` / `CompletedMarker`、
forward-parent event は置かない。

direct sink は emission ごとに次を検査する。

- node の start / finish が balanced である。
- token range が source order で重ならず、直前の emitted end と一致する。
- token text は必ず `&source[range]` から取る。
- `Missing` は commit 済み recovery path で zero-width node として直接書き、source byte を持たない。
- `Error` は commit 済み recovery path で直接書き、一 byte 以上を消費する。

parse 終了時に emitted token / trivia range が `0..source.len()` を gap なく一度ずつ覆うことを確認し、
`builder.finish()` を `ParsedFile.green` に格納する。`ParsedFile.green: GreenNode` と
`green.to_string() == source` は architecture contract のまま維持される。recovery record と
diagnostic は CST event ではなく、recovery path の commit 後に一度だけ記録する。

### Recovery and diagnostic ownership

shared recovery layer は header/full の両 mode から呼ばれ、§4.2.2 の safe-point hierarchy と
consume-or-stop guarantee を所有する。operator scanner の「candidate がこの position で無効」は
通常の backtracking failure であり、直ちに diagnostic にしない。候補を尽くし、grammar が
recovery path を commit した地点だけが recovery episode になる。

#### Typed recovery-site identity and header/full reconciliation

header discovery と full parse の照合には、message、presentation range、parser branch の通過順ではなく、
同じ shared grammar が commit した recovery site を表す typed key を使う。概念上の型は次とする。

```rust
pub struct DiagnosticId(DiagnosticIdentity);

struct DiagnosticIdentity {
    revision: SourceRevision,
    origin: DiagnosticOrigin,
    event: RecoveryEventSequence,
    site: RecoverySiteKey,
}

struct RecoverySiteKey {
    role: GrammarRole,
    range: ByteRange,
}

struct ByteRange {
    start: usize,
    end: usize,
}
```

`DiagnosticId` は public には opaque newtype のままにし、hash した `u64` や message/range から作る
文字列にはしない。private inner value は source revision、cause authority、revision 内の recovery event
sequence、typed site key を構造的に保持する。hash collision や表示文言の変更で identity が変わらない
ことを優先する。`RecoverySiteKey` の照合 scope は一つの `SourceRevision` に限定されるため、index 自体は
`HeaderInfo` の revision-scoped committed recovery record table が所有する。

`GrammarRole` は自由文字列ではなく、grammar-owned の closed enum family とする。最初の shared
declaration grammar では少なくとも次の vocabulary を持つ。

```rust
enum GrammarRole {
    Declaration(DeclarationRole),
    ClosingDelimiter {
        owner: ConstructRole,
        delimiter: DelimiterKind,
    },
    Statement(StatementRole),
    Expression(ExpressionRole),
    Pattern(PatternRole),
    Type(TypeRole),
    Layout(LayoutRole),
    Embedded(EmbeddedRole),
    Token(TokenRole),
}

enum DeclarationRole {
    Import(ImportRole),
    OperatorHeader(OperatorHeaderRole),
}

enum ImportRole {
    Path,
    GroupEntry,
    Alias,
}

enum OperatorHeaderRole {
    Name,
    Fixity,
    LeftBindingPower,
    RightBindingPower,
    DefinitionIntroducer,
}
```

`ConstructRole` は `ImportGroup`、`OperatorName`、`ExpressionGroup`、`ArgumentList` のように
delimiter を所有する construct を区別する。同じ byte position の `)` でも、import group と
expression group の recovery を同じ role に潰さないためである。`StatementRole` 以下は各 grammar
family の実装時に同じ原則で closed enum を追加する。任意の `String`、raw Rowan kind、表示用 label を
受ける `Other` variant は置かない。新しい recovery call site は既存 variant を意味が違うまま流用せず、
最も狭い owner/slot variant を追加する。これにより vocabulary の拡張は compile-time に明示され、
同じ role/range へ異なる causal site を誤って集約しない。

range は recovery node が所有する UTF-8 byte range そのものを使う。`Missing` は insertion point の
`p..p`、`Error` は実際に consume した `start..end` である。diagnostic presentation adapter が range を
補正しても、site key は補正前の parser-native range を維持する。header/full の両 phase は同じ
`Arc<SourceText>` と `SourceRevision`、byte-positioned `SourceInput`、shared declaration grammar を使う。
`parse_file` は渡された `HeaderInfo` の revision が source snapshot と一致することを入口で検査し、
一致しない product の照合を compiler invariant violation とする。したがって同じ source の同じ
recovery call site は両 phase で同じ byte range を指す。

周辺コードが編集された snapshot 間で offset を shift したり、role/range を fuzzy に anchor し直すことは
この key の責務ではない。edit 後は新しい `SourceRevision` に対して `scan_header` からやり直し、旧 revision
の `DiagnosticId` と照合しない。cross-revision diagnostic tracking は LSP/presentation layer の別設計とし、
この proposal の scope 外とする。

header discovery は recovery path を commit した順に `event = 0, 1, ...` を割り当て、record と
`RecoverySiteKey -> DiagnosticId` index を `HeaderInfo` に凍結する。full parse の allocator は header が
割り当てた次の event から始める。shared header grammar の reparse が site を commit した時の手順は
次とする。

1. full phase が自身の parser-native role/range から `RecoverySiteKey` を作る。
2. header record table に exact key が一件あれば、その record の recovery kind と expected/consumed
   shape も一致することを parity invariant として検査し、header-origin の `DiagnosticId` と frozen
   diagnostic をそのまま再利用する。full phase の event は新たに消費しない。
3. exact key がなければ message/range の類似度や record sequence で近い header record を探さず、
   full-origin の新しい event と `DiagnosticId` を発行する。role または parser-native range が異なる
   record は、文言が同じでも別 recovery event である。
4. header table の同じ key が複数 record を返す場合は vocabulary が causal site を区別できていない
   compiler invariant violation とし、どれか一件を任意に選ばない。

exact key がなかった場合も、既存の header-origin diagnostic は final list に一度だけ残り、新しい
full-origin diagnostic も独立に残る。shared header grammar の fixture が両者を同一 site と期待していた
場合、この差は header/full recovery parity failure として可視化されるが、fuzzy deduplicate で隠さない。
body recovery は常に full-origin の新しい ID を持つ。final list は §4.2.2 の ordering key で一度だけ
sort / freeze する。

fixture schema の `id = { origin, event }` は `DiagnosticIdentity` の cause authority と event sequence の
test projection であり、production `DiagnosticId` の serialization ではない。`origin = "header"` の ID は
full list へ移っても header のままである。fixture の `full.recovery.role` / `range` は site key の
人間可読な coarse projection で、たとえば `Declaration(Import(Path))` は `import_path`、
`ClosingDelimiter { .. }` は `closing_delimiter`、`Declaration(OperatorHeader(_))` は
`operator_header_entry` と表す。owner、delimiter、operator slot を fixture の `role` 文字列へすべて
直列化しなくても、harness は header で得た opaque 実 ID と full list の実 ID の値同一性を比較するため、
schema の観測モデルと production key の typed precision は矛盾しない。

#### Expectation union and primary message selection

`LatestSink` は speculative parser failure のうち、range の `(start, end)` が最も大きい active group
だけを残す。この range selection と rollback semantics はそのまま使うが、`StdErr` の表示 label を
直接 public diagnostic にしない。`ParseErrorSink` は `LatestSink<usize, ParseExpectation>` を包み、
各 expectation を少なくとも次の typed data として保持する。

```rust
struct SyntaxExpectation {
    role: GrammarRole,
    expected: ExpectedSyntax,
    range: ByteRange,
    sources: ExpectationSources,
}

struct CommittedRecoveryRecord {
    id: DiagnosticId,
    site: RecoverySiteKey,
    kind: RecoveryKind,
    unexpected: Arc<[UnexpectedSyntax]>,
    expectations: Arc<[SyntaxExpectation]>,
    primary_expectation: usize,
}
```

`ExpectationSources` は `Speculative` / `CommittedRecoveryRule` の二 bit を持ち、同じ semantic
candidate が両方から来た場合も一 record で provenance を失わない。
`ExpectedSyntax` は identifier/path/expression のような grammar element、keyword、punctuation、delimiter
kind を typed variant と payload で表す。localized message や `Debug` string は入れない。
`UnexpectedSyntax` は EOF または parser-native byte range と token/category を保持する。candidate の
`range` は expectation が発生した位置であり、diagnostic の primary range ではない。primary range、
`Missing` / `Error` kind、consume range、`DiagnosticId` は committed recovery record が authority の
ままにする。

`ParseExpectation::MergeErrors` は `LatestSink` が渡した同一最遠 group の全 entry を上の typed union へ
変換し、`StdSummary` の追加 `max_start` filter や label-string deduplicate は使わない。primitive parser の
expectation も grammar wrapper が `GrammarRole::Token` などの typed role を付けてから sink へ送り、
untyped label だけが union に入る経路を作らない。

recovery path を commit した瞬間、recovery が token を挿入・consume する前に active expectation group を
一度だけ `take_merged` し、次の手順で record を凍結する。

1. `LatestSink` の最遠 active group にある distinct expectation をすべて取り出す。rollback 済み branch、
   より手前の group、別 recovery episode の expectation は含めない。「全候補」はこの一 group 内の
   semantic union を意味する。
2. `(role, expected, range)` が同じ candidate は一件へ deduplicate し、source provenance は bitset 相当で
   union する。branch ごとの出現回数と挿入順は parser implementation detail として捨てるが、role、
   expected element、range が異なる candidate は落とさない。
3. committed recovery rule が必須要素を知っている場合、その typed candidate も
   `CommittedRecoveryRule` として union する。sink が空、または speculative branch が causal role を
   残さなかった場合でも、`Missing(expected)` や同期した construct の説明が generic
   `syntax error` へ退化しないためである。
4. unexpected token / EOF は candidate list と混ぜず、distinct な structured evidence をすべて
   canonical sort して `Arc<[UnexpectedSyntax]>` に保持する。主メッセージに使う一件は最遠 range、
   typed token order の順で先頭に置く。branch order と debug build の有無で evidence を落とさない。
5. union を下の stable order で canonical sort し、先頭 candidate の index を
   `primary_expectation` とする。candidate が一件もない recovery call は API contract violation とし、
   grammar-owned fallback role/element を追加してから commit する。

全候補の保持先は debug-only side table ではない。committed recovery record が
`Arc<[SyntaxExpectation]>` を所有し、そこから作る public `SyntaxDiagnostic` も同じ `Arc` と selected index
を保持し、`expectations()` / `primary_expectation()` 相当の typed accessor で観測可能にする。release build、
LSP、fixture harness でも候補が失われない。複数候補は一つの diagnostic の structured context であり、
候補ごとに diagnostic や recovery event を増やさないため、1 recovery event = 1 primary diagnostic と
recovery node / diagnostic の 1 対 1 contract は維持される。

primary candidate は parser branch order ではなく、committed `GrammarRole` との関係で選ぶ。優先順位は
次の通りである。上の tier が常に下の tier より優先する。

| tier | candidate role | 根拠 |
| --- | --- | --- |
| 0 | committed site の `GrammarRole` と exact match | 実際に選んだ recovery path の causal slot であり、speculative alternative より authority が強い |
| 1 | 同じ owner/construct の declaration-specific required slot (`Import(Path)`、`OperatorHeader(Fixity)` など) | `expected path` のようにユーザーが直すべき宣言 field を直接示せる |
| 2 | 同じ owner の structural boundary (`ClosingDelimiter`、separator、`Layout`) | construct を閉じるための局所的で安全な修正を示す。site 自体が delimiter なら tier 0 になる |
| 3 | 同じ grammar family の form (`Statement`、`Expression`、`Pattern`、`Type`、`Embedded`) | declaration slot / boundary より広いが、generic token class より意味がある |
| 4 | lexical `Token` role | keyword/identifier/punctuation choice の branch noise が上位の grammar intent を隠さないようにする |
| 5 | owner または grammar family が committed site と異なる candidate | 最遠 speculative group の情報として保持するが、causal role がある限り主表示には選ばない |

同じ tier では次の key を順に適用する。

1. `CommittedRecoveryRule` bit を持つ candidate を `Speculative` bit だけの candidate より先にする。
2. owner と slot の両方を持つ狭い role を family-level role より先にする。
3. `ExpectedSyntax::stable_order_key()` を使う。kind rank は `Path` < `OperatorName` < `Fixity` <
   `BindingPower` < `Delimiter` < `Keyword` < `Punctuation` < `Identifier` < `Literal` < `Operator` <
   `Expression` < `Pattern` < `Type` < `Statement` < `EndOfInput` と固定する。同じ kind では delimiter を
   round / square / curly、literal を integer / float / character / string の順にし、keyword、punctuation、
   operator とその他 payload は canonical source spelling の byte order で並べる。この順序は enum declaration
   order や locale から導出せず、変更時は diagnostic presentation contract の変更として fixture review を行う。
4. expectation range の `(start, end)`、最後に typed role の stable key を使う。

localized message、English message、hash-map iteration order、`choice` / `or` の arm order、同じ candidate の
出現回数は tie-break に使わない。grammar refactor で branch order が変わっても primary message が変わらず、
role vocabulary または explicit stable key を変更した時だけ intentional な presentation change になる。

`SyntaxDiagnostic` の主メッセージは selected candidate 一件と optional な unexpected evidence から
presentation key を作る。たとえば `Declaration(Import(Path)) + ExpectedSyntax::Path` は
`expected import path`、`ClosingDelimiter { delimiter: Round, .. } + ExpectedSyntax::Delimiter(Round)` は
`expected ')'` を選ぶ。残りの候補は structured context として保持し、UI が secondary note の
`also expected ...` を表示するために使ってよいが、primary message に全候補を連結しない。移行期の
Yulang2 presentation adapter はこの presentation key の wording/range を変えてよいが、candidate union、
selected index、site key、`DiagnosticId` を変えてはならない。

full reparse で exact `RecoverySiteKey` が header record に一致した場合は、full phase の expectation group で
header diagnostic を作り直したり候補を追加したりしない。early-ready result と full-ready result で同じ ID の
主メッセージが変わることを避けるため、header が凍結した candidate union と selected index をそのまま再利用する。
full group は debug/parity assertion に使ってよいが、public record の authority にはしない。key が一致せず
full-origin record を新規発行する場合だけ、その full group から独立の union と主メッセージを作る。

## Complete `use` declaration grammar and projection

この章は、現行 `UseDeclaration { range, path }` を置き換える use grammar / AST と、そこから
`HeaderImport` を作る規則を定める。parser implementation 自体はこの revision の対象外である。

### Oracle token vocabulary and recognition order

`yulang2-oracle@a58eefc3` の `stmt/use_scan.rs` は、trivia を消費した後の一 token を次の順で
分類する。

1. `::`、`*`、`/`、`,`、`{`、`}`、`;`、`(`、`)`、`[`、`]` を punctuation として試す。
   `;` と bracket は use grammar では `Stop` になる。
2. `v` + ASCII digit で始まり、その後に ASCII alphanumeric、`.`、`-`、`+` が零個以上続く
   spelling を `Version` として試す。
3. Unicode XID identifier（先頭 `_` も可、末尾 `?` / `!` も可）を読み、`mod`、`as`、`with`、
   `without` だけを use 専用 tag にする。
4. use operator-name character run を `Op` として試し、それ以外の一文字を `Stop` にする。

`mod` は `UseTag::Mod` かつ CST 上も `SyntaxKind::Mod` になる use 専用 contextual keyword である。
`as` も専用 tag / kind である。`with` と `without` は専用 `UseTag` だが CST kind は一般
`Ident` のままである。`realm` と `band` はどちらも専用 tag ではなく、一般 `Ident` である。
`Realm` / `Band` という scanner tag は存在しない。したがって form marker の語彙は、scanner が
直接確定する `mod` と、projection が spelling + separator で確定する `realm` / `band` の三つで
網羅される。`as`、`with`、`without`、`Version` は suffix/control であり form marker ではない。

newline を含む trailing trivia は次 token の `leading_info` になる。通常の use spec はそこで停止する。
brace group の list machine だけは newline を implicit separator として受理し、次 item の先頭では
`Space` 相当に変換する。このため path 自体は physical newline をまたがず、group item は comma または
newline で区切れる。empty group と trailing comma は closing `}` を次 item の stop として受理する。

### Oracle state machine

`stmt/use_decl.rs` の recognition rule は次の state table と等価である。ここで
`operator-name` は `(`、`Ident | Op | Glob`、`)` の三 token、`sep` は `/ | ::` である。
declaration-level visibility は caller が先に解析して `parse_use_decl` へ渡すため、use 専用 token
vocabulary と state table には含まれない。

| state | accepted token and transition |
| --- | --- |
| spec start | `{` -> recursive group tail、`mod` -> ident-required state、`Ident` / `operator-name` -> segment tail |
| after `mod` | `Ident` だけを受理して segment tail |
| segment tail | `sep` -> separator target、`as Ident` -> group/alias tail、`Version` -> version tail、`with` -> anchor、または stop |
| separator target | `Ident` / `operator-name` -> segment tail、`{` -> recursive group tail、`*` -> glob tail |
| group/alias tail | `as Ident` を反復可、`Version` -> version tail、`with` -> anchor、または stop |
| glob tail | `as Ident`、`without` list、`Version`、`with`、または stop |
| `without` list | `Ident` / `*` / `operator-name`、または recursive brace group。simple item は comma で反復し、その後 `Version` / `with` も可 |
| version tail | `with` または stop |
| anchor | `Ident (sep Ident)*` の後で stop |

group item は同じ spec-start function を再帰的に呼ぶ。このため group は nested group、path、alias、
glob、item-local `mod` を構文上表せる。group の明示 separator は comma、暗黙 separator は indentation に
依存しない newline、terminator は `}` である。glob は必ず separator の後に現れ、`without` は glob
tail からだけ到達する。anchor は identifier path に限定され、group、glob、operator-name を含まない。

この table は oracle の認識範囲を記録するものであり、すべての認識可能な並びに有効な import 意味を
与えるという意味ではない。たとえば parser state は group / glob の後の alias と alias の反復を
認識できるが、一つの alias を複数 target に投影する規則は持たない。Yulang3 は後述の semantic
validation でこのような曖昧な tail を diagnostic にし、silent に最後の alias を採用しない。

### Form classification

form は path 全体を先に `Vec<WordSpan>` へ潰した後で推測せず、各 recursive use spec の先頭を
読んだ時点で次の順序により一度だけ確定する。

```text
classify_use_form(first, following_separator):
    if first.tag == Mod:
        consume `mod`
        require an Ident as the first stored path segment
        return (Mod, path_without_mod)

    require first to be Ident or parenthesized operator-name

    if first is Ident("realm") and following_separator == Slash:
        consume both as a marker
        return (Realm, path_after_marker)

    if first is Ident("band") and following_separator == ColonColon:
        consume both as a marker
        return (Band, path_after_marker)

    return (Plain, path_including_first_and_all_separators)
```

`mod` の判定を先に置くのは `use_scan.rs` が spelling `mod` を `Ident` より先に専用 tag にするためである。
したがって `use mod::x` を Plain path として読み直さず、`mod` 後の必須 `Ident` が欠けた invalid spec と
する。`realm` / `band` は spelling だけでは marker にならない。具体的には `realm::x`、`band/x`、
`other/x` はすべて Plain で、最初の segment も path に残る。`realm/x` と `band::x` だけが marker と
separator を path から除く。

各 group item でも同じ classifier を使う。親から既に non-empty prefix または non-Plain form を
継承した branch に、子が別の non-Plain marker を置くと absolute origin が二つになるため、その branch は
semantic error とし fact を commit しない。prefix のない Plain root group では、各 item が Plain / Mod /
Realm / Band を独立に選べる。Plain child は親の effective form を継承する。

4 fixture はこの rule の直接例になる。

| source | form | normalized path | declaration range |
| --- | --- | --- | --- |
| `use std::data` | Plain | `std`, `data` | `0..13` |
| `use mod math::value` | Mod | `math`, `value` | `0..19` |
| `use realm/tools::format` | Realm | `tools`, `format` | `0..23` |
| `use band::support::value` | Band | `support`, `value` | `0..24` |

これは fixture の `header.imports` と `full.header_projection.imports` の form / path / range に一致する。
oracle の source collector も `band` + `::`、`realm` + `/` の順に分類し、この二 form だけ先頭 segment を
除く。slash を含むそれ以外の path は別の slash-qualified route として全 segment を保持しており、
Realm marker へ一般化しない。

implementation は use 用の独立した global lexer を作らない。shared word / punctuation scanner の
range を使い、use grammar position で上記 tag を付ける。最初の atom と直後の separator を一度読み、
`PendingUseHead` のような小さい local value で分類してから committed CST / AST を一度だけ出力する。
`realm` と `band` のために source や CST を再走査しない。通常の start alternative は chasa の
`choice` / `or`、separator と suffix の遷移は token 一個の predictive dispatch で表し、manual
checkpoint / rollback を declaration 全体へ広げない。

### Structured Use AST

現行の `UseDeclaration { range, path: Vec<WordSpan> }` は次の概念 shape に置き換える。これは public
field layout の固定ではなく、実装が失ってはならない情報と責務の境界を示す。

```rust
struct UseDeclaration<'source> {
    range: Range<usize>,
    visibility: Visibility,
    tree: UseTree<'source>,
}

struct UseTree<'source> {
    range: Range<usize>,
    form: HeaderImportForm,
    prefix: UsePath<'source>,
    terminal: UseTerminal<'source>,
    aliases: Vec<WordSpan<'source>>,
    qualifiers: UseQualifiers<'source>,
}

enum UseTerminal<'source> {
    Single,
    Group {
        join: Option<UseSeparator>,
        items: Vec<UseTree<'source>>,
    },
    Glob {
        join: Option<UseSeparator>,
        without: Vec<UseExclusion<'source>>,
    },
}

struct UsePath<'source> {
    segments: Vec<UseSegment<'source>>,
    separators: Vec<UseSeparator>,
}

enum UseSegment<'source> {
    Word(WordSpan<'source>),
    Operator { range: Range<usize>, text: &'source str },
}

enum UseSeparator {
    ColonColon,
    Slash,
}

struct UseQualifiers<'source> {
    version: Option<UseVersion<'source>>,
    anchor: Option<UsePath<'source>>,
}

struct UseVersion<'source> {
    range: Range<usize>,
    text: &'source str,
}

enum UseExclusion<'source> {
    Segment(UseSegment<'source>),
    Glob { range: Range<usize> },
    Group {
        range: Range<usize>,
        items: Vec<UseTree<'source>>,
    },
}
```

`UsePath` は `separators.len() == segments.len().saturating_sub(1)` を保つ。group / glob の直前にある
separator は path 内の separator ではなく terminal の `join` に置く。先頭 group では `join = None`、
`std::io::{...}` では prefix が `std::io`、`join = Some(ColonColon)` になる。Realm / Band marker が
separator ごと除かれ、直後が group / glob だった場合も `join = None` になり、先頭に架空の空 segment を
作らない。

parenthesized operator-name は source range と内側の canonical spelling を一 segment として保持する。
glob の `*` と operator spelling `(*)` を同じ variant にしない。`UseExclusion` は name、operator、glob、
および brace 内の recursive exclusion tree を区別し、group と同じ prefix flattening を再利用する。
exclusion は import record を追加せず、glob selection から候補を引く pattern になる。

`aliases` が vector なのは oracle recognition が `as Ident` を反復でき、invalid source でも各 token の
range を CST 再走査なしで diagnostic に渡すためである。semantic import で許す explicit alias は
`Single` の零個または一個だけとする。複数 alias、group alias、glob alias は曖昧な binding shape として
diagnostic を生成し、その subtree の fact は commit しない。oracle recognition の反復可能性を、最後の
alias を silent に勝たせる互換性 contract にしないためである。

`without` は glob が選ぶ binding set を変えるため、この AST と意味論に含める。brace group 内の
exclusion は common prefix を展開し、source order の exclusion pattern にする。重複 exclusion の除去や
存在しない name の扱いは resolver policy であり parser は決めないが、構造を捨てたり単なる token text に
戻したりしない。

version suffix と `with` anchor は oracle scanner / parser が明確な構文を持ち、後から CST を再走査して
復元すべきではないため `UseQualifiers` に typed syntax として入れる。一方、その version の canonical
validation、manifest / lock との対応、anchor が source provider selection に与える意味、inner item と
group-wide qualifier が競合した場合の precedence は source-loader / resolution 設計に依存する。
これらの resolution semantics と `HeaderImport` への最終 qualifier projection は future scope とする。
実装は qualifier を無視した `HeaderImport` を commit して別 dependency と同一視してはならない。

### Group expansion to `HeaderImport`

header/full の shared declaration grammar は同じ `UseTree` を作り、次の一回の depth-first projection で
fact を得る。CST や source を projection のために再走査しない。

```text
expand(tree, inherited_form, inherited_path, pending_join):
    effective_form =
        inherited_form                    if tree.form == Plain
        tree.form                          if inherited_form == Plain
                                             and inherited_path is empty
        semantic error                     otherwise

    path = concatenate(inherited_path, pending_join, tree.prefix)

    match tree.terminal:
        Single:
            validate one target and zero-or-one alias
            emit one record(effective_form, path, alias)
        Glob { without }:
            validate no alias
            emit one glob record(effective_form, path, expanded without)
        Group { join, items }:
            validate no alias
            for item in source order:
                expand(item, effective_form, path, join)
```

empty group は record を作らない。nested group は同じ algorithm を再帰し、完成した leaf だけを
left-to-right source order で commit する。一 item の missing target、form conflict、曖昧な alias は
その branch だけを不完全にし、delimiter recovery で同期できた sibling の complete fact を捨てない。
一つの `UseTree` から出た fact は transaction buffer に staging し、各 leaf の mandatory field が一意に
確定してから commit する。この規則は既決の committed recovery record と diagnostic の一対一原則を
変更しない。fact の個数と recovery event の個数を対応させる必要もない。

各 projected `HeaderImport` field は次のように決める。

- `form`: 上の `effective_form`。marker text は normalized path に入れない。
- `path`: common prefix と leaf path を結合した segment spelling。operator segment は括弧を除いた
  canonical spelling とする。separator shape は Use AST に残し、resolution 前に必要な route 情報を
  捨てない。`HeaderImport` も最終的には structured path / route を所有し、既存 `path()` はその segment
  projection として維持する。Plain の `a/b::c` と `a::b::c` を同じ fact に潰してはならない。
- `alias`: `Single` leaf に source 上の `as name` が一つある場合だけその spelling。alias がない場合は
  last path segment から暗黙 alias を合成せず `None` のままにする。
- `visibility`: shared declaration prefix が正規化した declaration-level visibility を全 leaf に
  コピーする。group item は visibility を上書きしない。現在の4 fixtureでは無指定を `Private` とする。
- `range`: root が Single / Glob なら newline を除く `UseDeclaration.range`。group から展開した record
  は、その record を最終的に生んだ innermost leaf `UseTree.range` とする。common prefix と leaf は
  source 上で不連続になり得るため、一つの range へ無理に合成しない。declaration 全体の range は AST に
  別途残る。`UseDeclaration.range` は visibility があればその先頭から最後の use suffix までで、newline、
  semicolon など caller が所有する statement separator は含めない。
- `key`: production field ではなく fixture-local join label のままとする。parser は path 文字列から key を
  生成しない。fixture author / harness は source-order の record shape に key を対応づけ、header/full の
  同じ leaf に同じ key を使う。重複 path は ordinal を含む別 key で区別できる。

glob と `without` を losslessly public fact にするには、`HeaderImport` を
`selection: Single | Glob { without }` 相当で evolve させる必要がある。version / anchor を実装する時も
raw source qualifier を区別できる field が必要になり、non-marker slash path には structured separator /
route field が必要になる。Phase 2 fixture schema v0 の import record は
`form/path/visibility/alias/range` だけを固定しており、current four fixture はすべて qualifier-free
Single なので矛盾しない。v0 が表せない glob selection、exclusion、version、anchor の fixture を
closed-world contract に追加する前、および separator shape の異なる Plain path を同じ case family で
区別する前に、schema の additive revision または contract-version bump を行う。
それまでは path の末尾へ `*` を偽 segment として足したり、qualifier を落とした record を期待値に
書いたりしない。

### `use mod` sugar responsibility

oracle parser のコメントは `use mod path` を `mod path_head; use path` の sugar と説明する。しかし
`yu-syntax` は source file discovery、module declaration の合成、source-set mutation を所有しない。
したがって syntax 層の責務は次で閉じる。

- CST は source に存在する一つの use declaration を lossless に保持する。
- Use AST / `HeaderImport` は `form = Mod` と normalized path を保持する。
- parser は synthetic `ModDeclaration` を作らず、`HeaderInfo.imports` 以外の source-set fact をその場で
  追加しない。
- downstream source-loader / module-resolution は Mod record を見て、少なくとも path head の module
  load と通常 import の二効果を実現する責任を持つ。

この分担自体は確定とする。一方、§18 が未決定としている non-header `mod` / late `use` を含む
source-set expansion を iterative full parse で発見するか、operator-independent structural discovery
product で発見するかは、この章でも決めない。leading `use mod` の raw syntax fact を正確に作ることと、
source-loader が全 file の source set をどう固定点へ到達させるかは別 decision である。

### Still open

- version suffix の canonical validation、manifest / lock / source provider との対応。
- `with` anchor の resolution semantics と、item-local qualifier と group-wide qualifier が競合した時の
  precedence。AST 上の source scope は保持するが、ここでは勝者を決めない。
- glob selection、`without`、version、anchor、Plain slash route を fixture の closed-world projection で
  固定する schema revision の具体的 field shape。現 schema v0 と current four fixture は変更しない。
- §18 の non-header `mod` / late `use` を含む source-set expansion の discovery mechanism。

### Use-specific implementation gates

- four leading-use fixture の header/full form、normalized path、visibility、range が一致する。
- `realm::x`、`band/x`、arbitrary `a/b::c` が Realm / Band marker に誤分類されない。
- recursive group は source-order に独立 fact を作り、malformed item 後の complete sibling を commit する。
- simple alias、operator segment、glob、glob + `without` を Use AST が区別し、CST 再走査を要求しない。
- group/glob alias と repeated alias は silent overwrite せず committed recovery record を持つ。
- version / `with` は typed syntax に残り、意味未確定のまま qualifier を落とした HeaderImport を作らない。
- use grammar の header/full parity failure は既決通り compiler invariant violation とし、full value で
  header value を上書きしない。

## Direct Rowan full-parse session

この章は、前節までに確定した「shared declaration grammar」「sink を持たない speculative parser」
「parse-event buffer を置かない direct Rowan emission」を、現在の `grammar::declaration`、
`grammar::expression`、`grammar::header`、`RowanSink` へ接続できる API boundary まで具体化する。

採用する構成は **shared recognition core + commit-aware continuation** である。source 全体や declaration
全体を一度 AST にしてから CST を復元しない。逆に、全 parser へ常時 sink を渡して speculative arm から
書けるようにもしない。rollback が必要な最小の local decision だけを sink-free recognition とし、
accepted branch は commit 後の continuation が source order で一度だけ CST を書きながら完走する。

### Recognition と commit continuation の境界

shared recognition core に残す責務は次に限定する。

- character input と rollback-aware `ParseLocal` を読み、現在位置で成立し得る local grammar role を判定する。
- scanner が確定した source byte range、contextual tag、fixity role、delimiter / layout 情報を返す。
  operator header scanner は別途 parsed `BindingPower` を返すが、body expression recognition result は
  numeric binding power を持たない。
- `choice`、`maybe`、`lookahead`、`longest_match_then` の候補探索と、その候補内で生じた
  `LatestSink` expectation を所有する。
- candidate rejection では input、`ParseLocal`、expectation を checkpoint へ戻し、public fact、CST、
  committed recovery record を一切変更しない。

recognition result は一個の statement intro、use state transition、operator-header slot、NUD / LED
candidate、または一回の trivia run に必要な typed data だけを持つ。node start / finish の列や source
全体の token 列を持たない。accepted result は caller が直ちに commit continuation へ渡し、保持・replay
しない。

commit continuation は次を所有する。

- accepted branch の node / token を source order で direct sink へ書く。
- mandatory tail が欠けた場合、別 declaration arm へ戻らず shared recovery を commit する。
- syntax AST / fact projection に必要な semantic value を、scanner result から同時に組み立てる。
- recovery site ごとに `LatestSink` の最遠 typed candidate union を一度だけ committed record へ凍結する。
- completed use / operator declaration を header fact へ投影し、full mode では frozen `HeaderInfo` と照合する。

> **Status: 2026-08-22 partially superseded.**
> 次段落のoutput-generic Pratt control、boxed application AST、left-wrap checkpoint、shared precedence
> controlはhistorical implementation shapeである。current expression projectionはflat `OperatorChain`を作り、
> production CSTとtest用surface ASTが同じordered chain authorityを共有する。

ここで「同時に AST を組み立てる」は CST 復元用 token buffer を作るという意味ではない。`UseTree` と
`OperatorHeaderDeclaration` は header fact / parity の semantic input として必要なので、commit
continuation が引き続き返す。一方、full parse の expression は boxed `Expression` AST を最終 product に
必要としない。Pratt control を output-generic にし、unit test 用 `AstExpressionOutput` は現在の
`Expression` を作り、production の `CstExpressionOutput` は Rowan node と最小の `ParsedExpression`
metadata（range と left-wrap checkpoint）だけを作る。同じ NUD / LED recognition と precedence control を
使い、AST parser と CST parser の二つの grammar authority は作らない。

### Capability と API shape

現在の `Probe` / `CommittedCst` skeleton は、chasa `In<SourceInput, ..., &mut ParseLocal, ...>` を
実際に包む capability へ発展させる。以下の署名は lifetime spelling の固定ではなく、アクセス権と
data flow の binding contract を示す。

```rust
struct Probe<'parse, 'source, E> {
    input: GrammarInput<'parse, 'source, E>,
}

struct Committed<'parse, 'source, E, O> {
    probe: Probe<'parse, 'source, E>,
    output: O,
}

trait CommitOutput<'source> {
    type Checkpoint: Copy;

    fn checkpoint(&mut self) -> Self::Checkpoint;
    fn start_node(&mut self, kind: SyntaxKind);
    fn start_node_at(&mut self, checkpoint: Self::Checkpoint, kind: SyntaxKind);
    fn token(&mut self, kind: SyntaxKind, range: Range<usize>);
    fn finish_node(&mut self);
    fn commit_recovery(&mut self, record: CommittedRecoveryRecord);
}
```

`Probe` は source input、`ParseLocal`、`LatestSink` だけへ access できる。`RowanSink`、fact vector、
committed recovery log は持たない。`Committed::probe` は scoped closure として sink-free `Probe` を一時的に
再借用し、closure が返るまで `output` へ access できない形にする。raw `&mut RowanSink` を返す API や、
probe と sink を同時に借用できる field access は置かない。

`FullCstOutput` は `RowanSink` と committed recovery log を包んで `CommitOutput` を実装する。
`HeaderOutput` は Rowan sink を持たず、node / token operation が code generation 上 no-op になる
implementation と、fact transaction / committed recovery だけを持つ。generic continuation は両 output に
monomorphize されるため、production hot path に mode branch を一 token ごとに置かない。

`DirectCstSink` は空 marker のまま残さず、`RowanSink` が実装する sealed emission interface とする。
`CommittedCst` は raw sink を外へ渡さず、上記 `CommitOutput` operation を自身の method として公開する。
これにより、scanner callback が `DirectCstSink` trait bound を追加するだけで emission capability を得る
ことを防ぐ。

statement driver の概念 API は次とする。

```rust
enum StatementIntro<'source> {
    Use(UseIntro<'source>),
    Binding(BindingIntro<'source>),
    OperatorHeader(OperatorHeaderIntro<'source>),
}

fn probe_statement_intro(
    probe: Probe<'_, '_, ParseErrorSink>,
) -> Option<StatementIntro<'_>>;

fn continue_statement<O: CommitOutput<'_>>(
    intro: StatementIntro<'_>,
    committed: &mut Committed<'_, '_, ParseErrorSink, O>,
) -> StatementOutcome;
```

full mode は `StatementIntro` が一意に選ばれた後に chasa `cut` を行い、対応する continuation へ入る。
header mode は同じ intro recognizer を checkpoint 下で呼ぶ。`Use` / `OperatorHeader` なら transaction を
commit して同じ declaration continuation を使い、`Binding` / unknown starter なら checkpoint へ戻して
`FirstNonHeader` として正常停止する。

cut は「最初の word を読んだ」だけでは置かない。`my` は binding intro と private operator-header prefix
の両方になり得るため、必要な lookahead で declaration role が一意になった後に置く。`use` のように
starter 自体が role を一意にする場合は、その keyword と mandatory following slot を認識した時点を
commit boundary とする。cut 後の mandatory field failure は `None` で outer `choice` へ戻らず、既存の
typed recovery role で `Missing` / `Error` と committed record を作る。

### Declaration family ごとの分割

#### `use`

現在の `parse_use_tree` 全体を一個の speculative recognizer として残さない。次の local decision を
sink-free recognizer として抽出する。

- declaration starter と visibility prefix。
- spec start の contextual form (`mod`、`realm` + `/`、`band` + `::`、Plain)。
- separator 後の segment / operator-name / group / glob decision。
- group 内の close / comma / newline / next item decision。
- alias、`without`、version、`with` anchor の各 optional transition。

commit continuation は accepted transition ごとに source span をemitし、同時に現在の `UseTree`を
組み立てる。recursive group は同じ continuation を再帰し、complete child を source order で閉じる。
optional transition が存在しないことは normal probe failure であり、何も emit しない。transition の
introducer が確定した後の欠落は recovery であり、その branch の `Missing` / `Error` を commit する。

declaration node は `UseDeclaration`、recursive spec は `UseTree`、path は `UsePath` として構造化する。
group / exclusion item の branch-local recovery は既存の一対一 committed recovery rule を使い、complete
sibling の node と fact を捨てない。full mode が完成した `UseDeclaration` を投影した結果は、同じ source
revision の header projection と range / form / route / visibility / alias で exact に照合する。qualifier を
落とした `HeaderImport` は作らないという既存決定を維持する。

#### Operator header

operator header intro recognizer は `[visibility] [lazy] fixity` が一つの declaration role として確定する
ところまで読む。visibility / lazy / fixity の各 token と間の trivia は local recognition result に保持し、
commit 後すぐemitする。continuation は operator-name delimiter、operator spelling、fixity ごとの0〜2個の
`BindingPower`、`=`を順に読む。

binding-power recognizer は `digits+ ('.' digits+)*` の component range を返す。semantic valueは既存の
`BindingPower`へ一度だけ変換し、CSTは`BindingPower` node内へ`Integer` / `Dot` tokenを即時emitする。
operator spelling はdynamic expression scannerで再分類せず、operator-name slotが確定した範囲を
`Operator` tokenとしてemitする。

`=`をcommitした時点で`OperatorHeaderDeclaration`が完成し、header modeはfactをtransaction commitして
opaque body scanへ、full modeは同じfactを`HeaderInfo`と照合して通常のstatement/body grammarへ進む。
header opaque scanはCSTを作らず、full body parseとのauthorityを混同しない。

#### Binding statement

`my`だけではoperator visibilityとの区別が付かないため、shared statement-intro recognitionがbinding roleを
確定してから`BindingStatement`を開始する。nameと`=`をcommitした後はexpression recoveryを含むtotal
continuationとし、別declarationへ戻らない。header modeはbinding introをconsumeせず`FirstNonHeader`で
止まり、full modeだけがbinding continuationを実行する。

### Pratt NUD / LED の probe / commit

> **Status: 2026-08-22 superseded.**
> この節はlanded Pratt direct-CST sliceのhistorical control flowを記録する。minimum binding powerの
> probe、recursive RHS parse、`InfixExpression` / `SuffixExpression`へのleft wrapping、prefix operandの
> BP-driven ownershipは、末尾のprecedence-neutral chain追補が全てsupersedeする。sink-free operator
> candidate probe、oracle judge、accepted後のcut、triviaのlossless emissionだけを維持する。

current `parse_expression_bp`のprecedence controlとoracle judge tableは維持するが、現在の
`parse_infix_tail`のようにRHSをASTへ読み切ってからtailを返す形はdirect CST pathで使わない。

conceptual resultとAPIは次とする。

```rust
enum NudRecognition<'source> {
    Identifier(TokenSpan<'source>),
    Integer(IntegerSpan<'source>),
    Prefix(ScannedOperator<'source>),
    Nullfix(ScannedOperator<'source>),
}

enum LedRecognition<'source> {
    Infix {
        leading: TriviaRun,
        operator: ScannedOperator<'source>,
        left: BindingPower,
        right: BindingPower,
    },
    Suffix {
        leading: TriviaRun,
        operator: ScannedOperator<'source>,
        left: BindingPower,
    },
}

fn probe_nud(...) -> Option<NudRecognition<'_>>;

fn probe_led(
    minimum: &BindingPower,
    probe: Probe<'_, '_, ParseErrorSink>,
) -> Option<LedRecognition<'_>>;

fn commit_led<O: CommitOutput<'_>>(
    accepted: LedRecognition<'_>,
    left: ParsedExpression<O::Checkpoint>,
    committed: &mut Committed<'_, '_, ParseErrorSink, O>,
) -> ParsedExpression<O::Checkpoint>;
```

`probe_led`はleading trivia、`longest_match_then`、boundary、judge、value-start lookahead、fixity、minimum
binding powerの検査までをsink-freeで終える。candidateなし、site mismatch、BP不足ならLED probe開始前へ
rollbackし、leading triviaもemitしない。accepted resultが返った後にcallerがcutし、それからのみ
`commit_led`を呼ぶ。

full CST outputの順序は次で固定する。

```text
left_checkpoint = checkpoint immediately before committed left operand
emit left operand
accepted = probe_led(minimum)
if no accepted candidate: return left
cut
start_node_at(left_checkpoint, InfixExpression | SuffixExpression)
emit accepted leading trivia
emit operator token and its accepted trailing trivia
if infix: parse and emit RHS with right binding power
finish application node
continue LED loop
```

prefixはaccepted NUD fixityの後にcutし、`PrefixExpression`を開始してoperator / trailing triviaをemitして
からRHSを再帰parseする。nullfixは`NullfixExpression`を開始してoperatorをemitし、その場で閉じる。
suffixはRHSを読まず、leftを`start_node_at`で包む。operator candidate callback、`value_start`
lookahead、BP比較中にはsink call countが増えない。

expression先頭のleading triviaはcallerが所有し、expression checkpointより前にemitする。leftとLEDの間の
leading triviaはaccepted LEDが所有し、application node内でleftの後にemitする。operator scannerが
受理したtrailing triviaはoperatorとRHSの間に一度だけemitする。lower-precedence LEDをcallerへ返す場合は
そのtriviaをconsumeもemitもしない。

### Typed local trivia result

current `TriviaSpan { start, end }`だけでは、同じrange内のhorizontal whitespace、CRLF newline、line
comment、nested block commentを異なるCST tokenとしてemitできない。`scan_trivia`は次のlocal resultを返す
形へ発展させる。

```rust
struct TriviaRun {
    range: Range<usize>,
    parts: TriviaParts,
}

struct TriviaPart {
    kind: TriviaPartKind,
    range: Range<usize>,
}

enum TriviaPartKind {
    Whitespace,
    Newline,
    LineComment,
    BlockComment {
        termination: CommentTermination,
    },
}

enum CommentTermination {
    Closed,
    Unterminated { remaining_depth: usize },
}
```

`TriviaParts`は一回のmaximal trivia scanだけに生存するinline-first compact containerとし、source全体へ
蓄積しない。overflow storageの具体的な実装はobservable contractではない。partはtextを所有せず、元sourceの
UTF-8 byte rangeだけを持つ。次のinvariantをscanner unit testとsink debug checkで固定する。

- empty runでは`range.start == range.end`かつpartsは空。
- non-empty partはsource orderで重ならず、隣接し、全partsの連結がrun rangeと一致する。
- CRLFは一個の`Newline` partで、二byte rangeを持つ。
- line comment rangeは改行を含まず、直後の改行は独立`Newline` partになる。
- nested block commentは一個の`BlockComment` token rangeとして保持し、未閉鎖なら残depthを保持する。
- layout用`LineState`と`EmbeddedLexicalMode`のmutationはcurrent scanner同様`ParseLocal`に入り、candidate
  rejection時にはparts resultと一緒にrollbackする。

full outputはaccepted `TriviaRun`を受け取った直後、各partを`Whitespace`、`Newline`、`LineComment`、
`BlockComment` tokenへ写す。header outputはpartsをemitしないが、同じrunからleading / trailing triviaと
layout stateを得る。operator scannerの`ScannedOperator.trailing_trivia`は`TriviaSpan`から`TriviaRun`へ
変え、longest candidateがrejectされた場合はrunを公開しない。

これはparse-event bufferではない。保持単位は一回のscanner decisionだけで、accepted後に即時emitして
破棄する。`TriviaRun`からsourceを再scanせず、token textは`RowanSink::token_range`がsource rangeから
borrowする。

### Rowan sink completion contract

`RowanSink`には`token_range(kind, Range<usize>)`と`emit_trivia(&TriviaRun)`を追加し、callerがsource sliceを
手組みしない形にする。既存のsource ownership、contiguous order check、`checkpoint`、`start_node_at`は
維持する。

full sessionはroot nodeを一度だけ開始し、file-leading triviaを一回scan / emitしてからstatement loopへ
入る。parse終了時は`finish_complete`相当のoperationで次を検査してから`GreenNode`を返す。

- node start / finishがbalancedである。
- first token rangeが0から始まり、last token endが`source.len()`である。
- emitted token / trivia rangeがgap、overlap、重複なくsource全体を一度だけ覆う。
- `green.to_string() == source`である。

`Missing`はzero-width nodeなのでcoverageを進めない。`Error`はcommit済みrecoveryがconsumeした一byte以上の
rangeを子tokenとして持ち、coverageを進める。unknown / malformed sourceをlosslessにするためのrecoveryも
direct character consumptionと即時`Error` emissionを使い、旧`lex()`や全source token bufferへfallback
しない。

### Canonical `OperatorTable`

正本は`crates/yu-syntax/src/operator.rs`のfull-fixity trieを持つ`operator::OperatorTable`とする。
`parse.rs`にある空のpublic unit struct `parse::OperatorTable`は削除し、`lib.rs`はcanonical型を同じ
`OperatorTable`名でre-exportする。

`SyntaxEnvironment`はimport済みsyntax dependencyからcompile済みの`Arc<OperatorTable>`を保持する。
`SyntaxEnvironment::operators() -> &OperatorTable`というpublic accessorの型名は変えない。placeholder unit
constructorを直接使う互換性は維持せず、`Default` / `OperatorTable::empty()`を正規のempty constructorと
する。opaque table nameと`parse_file` signatureは維持される。

full session開始前に、imported tableと`HeaderInfo.operators`を次のようなsingle builderで一度だけmergeする。

```rust
fn compile_full_parse_operators(
    imported: &OperatorTable,
    local: &[HeaderOperator],
) -> Result<OperatorTable, OperatorTableBuildError>;
```

builderはimported entryの全fixity / binding power / provenanceをcopy-on-buildし、その後local declarationを
source orderでmergeする。同じspellingの異なるfixityは一entryへ集約し、同fixityの再宣言は既決通り
`ConflictingFixity`とする。errorはspelling、fixity、old origin / range、new origin / rangeを保持するため、
canonical entryはfixityごとのorigin metadataを失わない形へevolveする。

buildに成功したtableは`FullParseSession` / `ParseEnv`が所有または`Arc`で固定し、operator-role scannerと
後段のassociation queryは同じrevisionに属するreferenceだけを見る。full parse中のinsert、overlay、
lazy rebuild、HeaderInfo / CST再走査は置かない。
`SyntaxEnvironment`内のimported tableも、個々のexpression entrypointで再compileしない。

cross-source conflictをどのsyntax-planning diagnosticへ写し、table build failure後に`parse_file`がどの
recovery CSTを返すかは下のStill openに残す。これはcanonical型とparse中immutableというdecisionを
変更しない。

### `SyntaxKind` vocabulary

最初のdirect full-parse vertical sliceで、現在のvariantに加えて次を導入する。nodeとtokenを同じenumに
置くcurrent Rowan language shapeは維持する。

| family | node variants | token variants |
| --- | --- | --- |
| recovery | `Missing`, `Error` | `Unknown`（既存、commit済みerror childに限定） |
| use | `UseTree`, `UsePath`, `UseGroup`, `UseGlob`, `UseAlias`, `UseQualifiers`, `UseVersion`, `UseAnchor`, `UseExclusion`, `UseExclusionGroup` | `ModKw`, `RealmKw`, `BandKw`, `AsKw`, `WithoutKw`, `WithKw`, `Version` |
| operator header | `OperatorName`, `BindingPower` | `PubKw`, `OurKw`, `LazyKw`, `PrefixKw`, `SuffixKw`, `NullfixKw`（`MyKw` / `InfixKw`は既存） |
| expression | `IdentifierExpression`, `PrefixExpression`, `InfixExpression`, `SuffixExpression`, `NullfixExpression` | 既存`Identifier` / `Integer` / `Operator`を使用 |
| punctuation | — | `Slash`, `Colon`, `Comma`, `Star`, `LBrace`, `RBrace`, `LBracket`, `RBracket`, `Semicolon`, `Apostrophe`, `Backslash`（`Dot` / `ColonColon` / `LParen` / `RParen` / `Equals`は既存） |
| trivia | — | `LineComment`, `BlockComment`（`Whitespace` / `Newline`は既存） |

`UseKw`、`UseDeclaration`、`OperatorHeader`、`BindingStatement`、`IntegerLiteral`など既存variantは維持する。
contextual keywordはscanner-wide keyword tableで先に固定せず、accepted grammar slotが上表のkindへ分類する。
たとえば一般path segmentの`realm`は`Identifier`、markerとしてacceptedされた`realm/`の先頭だけが
`RealmKw`になる。operator-name内の`*`は`Operator`、separator後globとしてacceptedされた`*`だけが
`Star`になる。

`SuffixExpression`はcurrent `Expression` enumにまだないが、canonical tableがsuffix capabilityを既に
持ち、最初からfull-fixityを保つという決定に合わせてvocabularyへ含める。実装がsuffix LEDを後回しにする
場合も`Unknown`や`InfixExpression`へ潰さない。

> **Status: 2026-08-22 superseded for the expression row.**
> `PrefixExpression` / `InfixExpression` / `SuffixExpression` / `NullfixExpression`をsemantic application
> nodeとして使うvocabularyと上の説明はhistoricalである。replacementの`OperatorChain`とrole-specific
> operator-use nodeは末尾の追補で固定する。header / use / punctuation / trivia rowは変更しない。

### Header / full parity と diagnostics

headerとfullは同じstatement intro、use transition、operator-header slot recognizerを使う。違うのはcommit
outputとoperator bodyのcontinuationだけである。headerはcomplete mandatory fieldsだけをfact transactionへ
commitし、fullは同じsemantic declarationを作ってfrozen factとexact比較する。

recovery recognitionもshared coreに置く。probe failureの`LatestSink` candidateはまだdiagnosticではない。
commit continuationがrecovery siteを選んだ時だけ、既決の`GrammarRole + ByteRange` key、全candidate union、
selected primaryを一件のcommitted recovery recordへ写す。header/fullの同じsiteは同じIDを再利用し、
node emissionの有無でidentityを変えない。full outputはその同じrecordに対応する`Missing` / `Error` nodeを
direct emitする。

fixture schema v0のheader/full range、form、route、operator shapeは変更しない。新しいstructured use node、
comment token、expression application nodeはproduction CSTの精度を上げるが、glob / exclusion / version /
anchorのheader projection fieldをschema v0へ暗黙に追加しない。

### Implementation slices and gates

この章の実装は少なくとも次の順序へ分ける。

1. `SyntaxKind`、typed `TriviaRun`、`RowanSink::token_range` / whole-source completion check。
2. actual chasa inputを包む`Probe` / `Committed` capabilityとoutput-generic commit continuation skeleton。
3. shared statement introとuse / operator-header continuation。header fact parityとdirect declaration CST。
4. canonical `OperatorTable`のpublic type一本化とfull session開始前merge。
5. NUD / LED role probeとprecedence-neutral `OperatorChain` continuation。prefix / infix / suffix / nullfixの
   role-specific use nodeをsource orderでdirect emitし、application treeは作らない。
6. binding statementを含むroot statement loop、committed recovery、whole-file lossless invariant。

各sliceは次を満たす。

- speculative scanner / `choice` / `maybe` / `longest_match_then`中のsink call countは0のまま。
- accepted local resultは一度だけemitされ、token/eventのsource-wide bufferとreplayがない。
- header/fullのshared declaration projectionとrecovery ID parityが維持される。
- triviaを含む全token rangeがsource orderで連続し、slice対象fixtureで`green.to_string() == source`になる。
- `+!a` / `a+!b`はcanonical full-fixity tableとoracle judge semanticsを使い、candidate fallback中にCSTが
  増えない。
- production pathは旧`HeaderCursor` / `lex` / `FullCstBuilder`へfallbackしない。置換完了までは内部
  candidateとして隔離し、public entrypointを二系統にしない。

### Still open

- imported operatorとlocal header operatorの`ConflictingFixity`を、どのsyntax-planning recovery site / IDへ
  対応させるか。typed build errorと両originは保持するが、`parse_file`がtable build failure後に返すCSTと
  diagnostic orderingは、full-session diagnostics wiring時に既存の一対一原則へ沿って決める。
- `TriviaParts`のinline capacityとoverflow storageの具体型。range / part invariantと非蓄積性は確定だが、
  capacityはrepresentative corpusの計測後に決める。

## Fate of the committed code

### Reuse assessment

| current element | decision | reason / destination |
| --- | --- | --- |
| `HeaderInfo`, `HeaderImport`, `HeaderOperator` | keep/evolve | diagnostics/hash と `BpVec` 相当の full fixity を最初の slice で追加する |
| `SyntaxDiagnostic`, `DiagnosticId` | define/evolve | committed record の typed site key、全 expectation union、selected primary を保持する public product にする |
| `ParsedFile` and `parse_file` API shape | keep | `green: GreenNode`、diagnostics ownership、syntax key は正本と一致する |
| `SyntaxEnvironment` boundary | keep and implement | imported operator と committed local header fact から immutable full-parse table を作る入力になる |
| trivia/content distinction | keep as a concept | lossless CST と indentation grammar に必要。chasa scanner output へ移す |
| delimiter stack | keep as a concept | lexical-region stack と分離した outer boundary / recovery safe point に必要。rollback-aware `ParseLocal` へ移す |
| indentation / line-start tracking | keep/evolve | physical/current-line indentation、block/introducer baseline、continuation mode を rollback-aware `ParseLocal` へ移す |
| `newline_len`, indentation predicates | port selectively | shared scanner の char/byte helper へ移す |
| `GreenNodeBuilder` start/token/finish bridge | keep | commit 後だけ使える dedicated direct sink へ移す |
| `HeaderCursor` as token-producing cursor | replace | operator boundary を grammar 前に確定するため foundation にはできない |
| `HeaderCursor::next` / `scan_token` | replace | source char input と context-specific scanner に分解する |
| `scan_symbol_end` / `starts_distinct_item` | delete | context-free maximal munch が confirmed root problem |
| `TokenKind::Symbol` as preclassified run | delete | spelling/fixity/site を operator scanner が同時に決める |
| `lex() -> Vec<LexedToken>` | delete | architecture correction の中心 |
| `LexedToken`, `token_index` | delete | streaming char parse + direct range emission に不要 |
| `FullCstBuilder` orchestration | replace | grammar session と direct Rowan sink に責務分割する |
| `HeaderNode` / header ranges で CST を包む処理 | delete | shared declaration grammar と parity projection へ置き換える |
| `syntax_kind(TokenKind, text)` | replace | shared lexical authority と grammar-site classification に統合する |

### Rewrite strategy

既存 `lib.rs` と `parse.rs` の中で巨大な replacement を続けず、新しい named module に
character input、session、direct sink、shared declaration grammar の vertical slice を作る。
最小 slice が leading `use`、一つの operator header、`my <ident> = <expr>`、二つの `+!` case を
end-to-end に通した時点で、old `HeaderCursor` / `lex` / `FullCstBuilder` path を同じ change で削除する。

old/new parser を feature flag や fallback として長期間並存させない。二つの lexical authority と
header grammar が残り、parity failure を隠すためである。移行中も public entrypoint は
`scan_header` / `parse_file` の一つだけに保つ。

この rewrite strategy は元 proposal から変更しない。`HeaderCursor` / `lex` / `FullCstBuilder` は
新 vertical slice が成立する同じ change で削除し、long-lived feature-flagged fallback を残さない。

## Required implementation tests

> **Status: 2026-08-22 partially superseded.**
> 下記1の`+!a` / `a+!b` tree-shape assertionはassociation-phase testへ移す。yu-syntax testは同じ
> oracle judge resultとrole-specific flat item列をassertする。2以降のscanner rollback、full-fixity table、
> header/full parity、lossless / recovery contractは維持する。

最初の implementation slice で少なくとも次を固定する。

1. canonical fixture の同じ table に infix `+!`、prefix `+`、prefix / nullfix `!` とそれぞれの
   binding power を明記し、`+!a` が `+ (! a)`、`a+!b` が `a +! b` になる。judge table は
   oracle の `contains(PREFIX | NULLFIX)` semantics のまま使う。
2. longer trie candidate が current site で無効なとき、shorter candidate の末尾へ input、
   `line_indent` を含む scanner/layout local state、expectation error がすべて rollback する。trailing
   trivia の newline を消費した後に failure する probe でも、次 branch の indentation decision が
   fresh parse と一致する。candidate exploration 中は
   direct CST sink の call count が変わらず、accepted result の commit 後にだけ増える。
3. prefix / infix / suffix / nullfix の全 capability と binding power を `HeaderInfo` から immutable
   `OperatorTable` まで保持し、同じ spelling に複数 fixity がある case を parse できる。infix-only
   temporary representation を許さない。
4. accepted candidate の後では unrelated grammar branch へ戻らない cut placement と、通常の
   alternation が手書き rollback ではなく `choice` / `or` を使うことを確認する。
5. ASCII と multi-byte operator / identifier の diagnostic と header range が UTF-8 byte offset になる。
6. leading `use` と operator header の header/full projection が一致し、full parse 中に
   `OperatorTable` が更新されない。
7. valid operator header + malformed body で header fact は残り、body diagnostic だけが増える。
8. malformed header 後の valid header を recovery が発見し、fact transaction が partial field を
   commit しない。
9. operator body に heredoc、`%{...}` interpolation、`~"..."` rule literal、quoted / block Yumark を
   それぞれ含め、各 region 内に top-level boundary に見える newline / brace を置いた後へ valid header を
   続ける case family で、その header を早期分割も飲み込みもせず発見する。normal string、nested block
   comment、raw / Yulang fence body も同じ boundary contract で覆う。
10. all current fixtures で `green.to_string() == source`、direct builder の node balance、range
   conservation が成立する。
11. every byte prefix fuzz test が panic / hang せず、`Missing` / `Error` contract を守る。
12. current narrow `scan_header` compatibility fixtures の range / fact output を意図せず変えない。
13. header/full が同じ declaration recovery を `GrammarRole + ByteRange` の exact key で照合し、同じ
    `DiagnosticId`、candidate union、主メッセージを再利用する。message が同じでも role または
    parser-native range が異なる record は新しい full-origin ID になり、presentation range 補正では
    identity が変わらない。同じ key の header record 重複と、exact key 一致後の recovery shape 不一致は
    invariant violation になる。
14. 同じ最遠 expectation group に declaration slot、closing delimiter、expression、token candidate を
    混在させても全 distinct candidate が `SyntaxDiagnostic` に残り、committed site と role が一致する
    一件だけが主表示になる。`choice` arm の順序と hash insertion order を逆にしても selected candidate と
    message が変わらず、exact tie は explicit stable key で決着する。
15. source を編集して新しい `SourceRevision` にした case は旧 header record を照合せず、同じ role と
    shifted range に見えても新しい revision の ID を発行する。

oracle differential test は operator declaration を省略・簡略化しない。特に `+!a` の
value-start lookahead が調べる spelling の prefix / nullfix capability を canonical fixture と一致させる。
一時調査の prefix-only fixture で得た失敗を oracle predicate bug の期待値として固定せず、oracle の
judge table と user-confirmed language semantics を authority にする。

## Performance constraints

- source 全体の token vector と token text copy を作らない。
- operator lookup は prebuilt trie を一 character ずつ進み、run 全体の再走査を避ける。
- full parse の `OperatorTable` は `HeaderInfo` と imported syntax から一度だけ構築し、parse 中に
  overlay update や再構築を行わない。
- `longest_match_then` の rollback は同じ operator run 内の candidate boundary に限定する。
- speculative parser は CST を emit せず、local checkpoint は collection 全体の clone ではなく
  length/depth と scalar value の snapshot にし、scanner/layout-affecting state を漏れなく戻す。
- parse-event buffer と final Rowan replay を作らず、commit 後の token / node を direct sink へ
  一度だけ書く。
- expectation union と canonical sort は recovery commit ごとに最遠 active group 一件へだけ行い、
  speculative step ごとや表示ごとに再計算しない。header/full exact match では header の `Arc` を再利用する。
- header discovery は body を full expression parse せず、operator-independent lexical region を
  delimiter / indentation とともに追跡する opaque scan を行い、syntax planning のための軽量 phase
  という性質を維持する。
- full parse 中に HeaderInfo ranges を使った source 再走査や CST 再走査を追加しない。
- token text は source range から borrow する。

benchmark では少なくとも parse elapsed、operator trie probe count / rollback count、direct sink
emission count、token bytes、peak parser-local capacity を測り、current fixture と Yulang2
representative corpus の regression を見る。

## Resolved decisions

元の question 番号を残して decision の由来を追跡できるようにする。

### Resolved

1. `chasa` は crates.io の normal dependency として `=0.5.0` に exact pin する。ユーザーの直接確認
   （2026-08-20）により、source を Yulang repository に vendor / copy せず、workspace member や path
   dependency にもしない。exact pin により experimental API の通常の `cargo update` による暗黙の更新を
   防ぐ。
2. dynamic operator trie は `HeaderInfo` の committed local fact と imported syntax から full parse
   前に一度だけ compile し、immutable に使う。`qp-trie` か専用 trie かは observable architecture
   decision ではなく、`TrieState` contract と benchmark を満たす範囲の implementation detail とする。
3. canonical representation は最初の vertical slice から Yulang2 の `BpVec` と同等の prefix /
   infix / suffix / nullfix 全 fixity と binding power を持つ。
4. oracle の whitespace/fixity judge table は、`contains(PREFIX | NULLFIX)` を含めてそのまま採用する。
   full-fixity combination は canonical declaration を明記した fixture で固定する。
5. event buffer + final Rowan replay は採用しない。speculative parser が CST を emit できないことを
   型/API で強制し、commit 後だけ direct `GreenNodeBuilder` sink を使う。
6. operator declaration は header-scoped である。header discovery 完了後に table を構築するため、
   full parse 中の table update と rollback-aware overlay は置かない。
7. chasa expectation bridge は、`LatestSink` の最遠 active group にある distinct typed candidate と
   committed recovery rule の candidate を union し、committed record と public `SyntaxDiagnostic` の
   両方に全件保持する。主メッセージは committed site との grammar-role affinity と明示 stable key で
   一件選び、branch order や message text では決めない。
8. header/full reparse の `DiagnosticId` reconciliation は、同じ `SourceRevision` 内の typed
   `GrammarRole + parser-native ByteRange` exact key を使う。一致時は header record をそのまま再利用し、
   role/range 不一致時は fuzzy deduplicate せず full-origin の新しい ID を発行する。
9. full fixity API extension は architecture replacement の最初の vertical slice に含める。
   infix-only compatibility representation を中間段階として残さない。
10. direct full parse は shared recognition core + commit-aware continuation とする。rollback が必要な
    local decision だけを sink-free `Probe` で行い、accepted branch は `cut` 後の total continuation が
    AST / fact と direct CST output を同時に作る。declaration / expression 全体の token event buffer と
    replay は置かない。
11. trivia scanner は text を所有しない local `TriviaRun` を返し、whitespace、CRLF newline、line
    comment、nested block comment の contiguous source range を typed part として保持する。accepted run は
    commit 後すぐ emit して破棄し、CST emission のために source を再走査しない。
12. canonical operator table は `operator::OperatorTable` とする。空の placeholder
    `parse::OperatorTable` は削除し、public `OperatorTable` 名は canonical 型の re-export として維持する。
    imported syntax と local header fact は full session 前に一度だけ merge し、parse 中は immutable に使う。
13. direct CST の lexical / structural vocabulary は `SyntaxKind` に明示し、contextual keyword と operator
    glyph は accepted grammar slot で分類する。probe 中は kind を決めても emit せず、committed token だけが
    source range を一度だけ覆う。

## Implementation gates

architecture-level gate と question 7 / 8 の diagnostic detail は上の resolved decision で閉じた。
最初の vertical slice の完了条件は次とする。

- `chasa` が crates.io の normal dependency として `=0.5.0` に exact pin され、source の vendor / copy
  や workspace member / path dependency を使わない。
- `chasa` input から shared declaration grammar と最小precedence-neutral operator-chain grammarが直接sourceを読む。
- 通常の alternation は `choice` / `or` を使い、明示的 rollback は構造的に必要な operator-candidate
  区間へ限定される。
- `lex() -> Vec<LexedToken>` と `scan_symbol_end` を production path から除去する。
- `HeaderInfo` と immutable `OperatorTable` が `BpVec` 相当の prefix / infix / suffix / nullfix を
  最初から持ち、full parse 中に table mutation がない。
- canonical full-fixity fixture の `+!a` / `a+!b` がoracle judge tableのまま確定したoperator roleと
  source-order flat chain shapeを持つ。precedence-shaped treeはassociation-phase fixtureが固定する。
- `scan_header` と full parse が同じ declaration grammar を使い、fixture で parity が成立する。
- speculative branch は direct sink を呼べず、commit 後だけ Rowan node / token を書く。parse-event
  buffer と final replay layer がない。
- committed recovery record が最遠 expectation group の全 distinct typed candidate を保持し、
  grammar-role priority と stable tie-break で主表示を一件選ぶ。
- header/full の shared recovery site が typed role + parser-native byte range で同じ header-origin ID を
  再利用し、不一致 record を message/range で deduplicate しない。
- `ParsedFile.green` が lossless Rowan root で、structured diagnostic product と同じ revision に属する。
- old path への fallback がない。

## Sources inspected

- local Cargo registry `chasa-0.5.0`: `README.md`、`src/lib.rs`、`src/back.rs`、
  `src/input/*`、`src/error.rs`、`src/error/std.rs`、`src/parser.rs`、`src/parser/choice.rs`、
  `src/parser/prim.rs`、`src/parser/token.rs`、`src/parser/str.rs`、
  `src/parser/trie.rs`、`src/parser/memo.rs`。
- `yulang2-oracle@a58eefc3`: `crates/parser/src/context.rs`、`lib.rs`、`lex.rs`、
  `sink.rs`、`op.rs`、`scan/mod.rs`、`scan/trivia.rs`、`expr/core.rs`、
  `expr/tail.rs`、`expr/scan.rs`、`expr/scan/op/{scan,judge,boundary}.rs`、
  `typ/parse.rs`、`mark/scan.rs`、`string/{scan,parse}.rs`、`stmt/{op_def,common}.rs`、
  `stmt/{mod,use_scan,use_decl}.rs`、`parse/mod.rs`、`tests/{expr_grammar,stmt_grammar}.rs`、
  `crates/sources/src/lib.rs`、Cargo manifest / lock。
- Yulang3 current tree: `docs/yulang3-architecture.md` §4.2.1-4.2.2 / §18、
  `crates/yu-syntax/src/{lib,parse,input,session,sink,syntax_kind,operator}.rs`、
  `crates/yu-syntax/src/grammar/{mod,declaration,expression,header}.rs`、
  `crates/yu-syntax/src/scan/operator.rs`、
  `notes/design/2026-08-20-phase2-parser-fixture-schema.md`、phase 2 parser fixtures、
  commit `e1737368`、`7022ed27`、`669e678e`。
- local Cargo registry `rowan-0.15.17`: `src/green/builder.rs` と `examples/math.rs` の
  `GreenNodeBuilder::checkpoint` / `start_node_at`。

## Verification performed during investigation

- `chasa 0.5.0`: 12 unit tests と 124 doctests が offline で成功した。
- `yulang2-oracle` temporary copy: prefix-only declaration を使った `+!` test により tagged behavior の
  差異を再現した。この結果は fixture の fixity 集合に依存し、oracle の bug 判定には使わない。
- 同 temporary copy: `op_value_start_inner` の prefix/nullfix condition だけを OR にした実験で、
  `+!a` と `a+!b` の両方が expected tree になることを確認した。ただしこれは experimental variant
  の観測であり、採用する semantics ではない。
- `docs/yulang3-architecture.md` §4.2.2 / §18 を再照合し、operator の header 外 declaration point が
  記載されていないことを確認した。
- Phase 2 fixture schema と `header-full-diagnostic-identity` / `malformed-header-followed-by-valid-header`
  fixture を再照合した。production key の role/range は `full.recovery` の観測へ、cause authority と
  event sequence は `id.origin` / `id.event` へ対応し、header-origin の実 ID を full list で値比較する
  contract と矛盾しないことを確認した。fixture schema 自体は変更していない。
- broader grammar survey の指摘箇所を tagged source で再確認した。`scan_trivia` の `line_indent`
  mutation と expression/type/Yumark scanner の layout/mode dependency から、scanner/layout state の
  rollback ownership を binding rule とした。
- tagged `skip_op_def_body` と `scan_stmt_lex`、string/trivia/Yumark scanner を再照合し、header-mode
  opaque scan が delimiter / indentation に加えて operator-independent lexical region を追跡する必要を
  確認した。
- tagged `stmt/use_scan.rs` と `stmt/use_decl.rs` を通読し、use 専用 tag の全 vocabulary、version を
  identifier より先に試す scan 順序、各 predictive state、recursive group、glob 後だけの `without`、
  comma / newline group separator を確認した。`crates/sources/src/lib.rs` の route classifier と collector
  も照合し、`realm` + `/` と `band` + `::` だけが marker になり、group suffix が複数 import に作用する
  current behavior を確認した。
- four leading-use fixture の source と header/full record を再照合し、新しい form classifier が
  Plain / Mod / Realm / Band の form、marker を除いた path、declaration range、Private visibility を
  そのまま再現することを確認した。fixture schema v0 は recursive group の independent committed item
  projection と整合する一方、glob / exclusion / version / anchor の field をまだ持たないことを明記した。
- current `RowanSink`、`Probe` / `CommittedCst` skeleton、grammar declaration / expression / header、
  operator scanner と二つの `OperatorTable` 定義を再照合した。local probe が sink-free、accepted
  continuation が direct emit、full session が canonical immutable table を一度だけ構築する境界を、
  current API から実装可能な shape として固定した。
- この revision は本 design document だけを変更し、source、manifest、fixture、正本 architecture
  document は変更していない。

著者: Codex gpt-5.6-sol xhigh（2026-08-21）

## 追補案: `use` 宣言と operator header の direct-CST node shape

この節は、`Direct Rowan full-parse session` の実装 slice 3 で使う宣言 CST を具体化する。
既決の Use AST、header fact、recognition / commit continuation 境界は変更しない。ここで決めるのは、
accepted continuation がどの node をいつ開き、各 source token と trivia をどの親の直下へ書くかである。

本節の CST は semantic AST と同時に source order で構築する。CST から Use AST や
`OperatorHeaderDeclaration` を復元するための再走査は行わず、逆に AST を完成させてから CST token を
replay することもない。以下の child list は recovery のない valid source に対する canonical shape とする。
mandatory slot の recovery では、その slot と同じ位置へ既決の `Missing` または `Error` node を置き、
前後の valid child の順序を変えない。

### 表記と trivia 所有規則

以下の表記を使う。

| 表記 | 意味 |
| --- | --- |
| `I+` | `scan_trivia` が返す non-empty run で、source range 内に CR / LF を含まないもの。各 part を typed trivia token として順に emit する |
| `I*` | 上と同じ inline trivia run だが empty でもよい。empty のとき child は増えない |
| `G*` | group / list position の maximal `TriviaRun`。newline と comment を含めてよく、empty のとき child は増えない |
| `X?` | source に存在するときだけ一個の `X` |
| `X*` | source order の零個以上の `X` |
| `A \| B` | grammar が accepted slot で一意に選んだどちらか一方 |

`TriviaRun` は node ではない。`Whitespace`、`Newline`、`LineComment`、`BlockComment` の各 token を、
child list 中の `I+` / `I*` / `G*` の位置へ直接 emit する。CRLF は既決通り一個の `Newline` token である。

trivia の concrete parent は次で固定する。

1. file 先頭、statement 間、および declaration の semantic end より後ろにある trivia は `Root` の直下に
   置く。したがって statement 終端の newline、caller が所有する semicolon、`use` の最後の suffix または
   operator header の `=` より後ろの空白は declaration node に含めない。
2. declaration 内で次の required / optional slot を導入する trivia は、accepted transition と一緒に一度だけ
   emit する。CST 上ではその transition を包む最小の構造 node の直下で、次の child の直前に置く。
   たとえば alias 前の `I+` は `UseTree` または `UseGlob` の直下、`as` 後の `I+` は
   `UseAlias` の直下に置く。
3. optional transition の probe が不成立なら、その probe が読んだ trivia も input / `ParseLocal` と一緒に
   rollback し、emit しない。outer statement loop または別の accepted transition が同じ source range を
   一度だけ所有する。
4. group の brace / parenthesis 内にある `G*` は group node の直下に置く。comma と newline は item node に
   押し込まず sibling にする。これにより explicit comma、implicit newline separator、comment、empty group、
   trailing comma が source に現れた順のまま観測できる。
5. path separator の前後には trivia を許さない。これは現在の use grammar と oracle state machine の
   contract であり、`UsePath` は segment / separator のみを持つ。

これは「次の accepted slot と一緒に trivia を commit する」という leading-trivia convention である。
ただし trivia token 自体を次の leaf node の中へ常に入れるわけではない。構造上の parent を安定させるため、
inter-child trivia は最小の共通 parent の直下に置く。旧 `FullCstBuilder` のように trivia を declaration range
内へ lossless に残しつつ、どの subtree が separator / suffix trivia を所有するかも一意になる。

この convention は declaration continuation に限定する。expression operator scanner が返す
`ScannedOperator.trailing_trivia` は trailing result のままだが、flat `OperatorChain`ではoperator-use nodeを
閉じた後にchain直下のinter-item triviaとしてemitする。role nodeが後続operandを所有する形にはしない。
Rowan 上ではどちらも source-order の sibling token であり、旧 `FullCstBuilder` と同じく token text の
順序や coverage に差はない。

`RowanSink` には必要な primitive がすでにある。`token_range` と `emit_trivia`、node の
`start_node` / `finish_node` だけで本節の shape を表現でき、declaration では `start_node_at` を使わない。
ただし現在の capability wrapper では `RowanSink::emit_trivia` が `Committed` まで proxy されていない。
slice 3 では `CommitOutput::emit_trivia(&TriviaRun)` と `Committed::emit_trivia` を追加し、
`FullCstOutput` は `RowanSink::emit_trivia` へ委譲、`HeaderOutput` は no-op とする。continuation が
`TriviaPartKind -> SyntaxKind` の対応を各所で複製する形にはしない。これは新しい sink primitive ではなく、
sub-slice 1 と 2 の既存 primitive を capability boundary へ通す wiring である。

### `UseDeclaration`

一個の source declaration は `SyntaxKind::UseDeclaration` で包む。ordered children は次である。

```text
UseDeclaration :=
    (VisibilityKw I+)?
    UseKw I+
    UseTree

VisibilityKw := PubKw | MyKw | OurKw
```

visibility spelling がないとき token や zero-width visibility node は作らない。semantic
`Visibility::Private` は prefix の absence から得る。明示 `my` は `MyKw`、`pub` は `PubKw`、`our` は
`OurKw` とする。現在の `parse_use_declaration` は visibility を常に Private にしているが、Use AST の
`visibility` field と oracle の caller-owned declaration prefix は明示 visibility を保持するため、shared
statement intro が prefix を確定し、この node の先頭へ emit する。

`UseDeclaration.range` は最初の visibility token、なければ `UseKw` の先頭から、`UseTree` の最後の
non-trivia token までである。`UseDeclaration` node も同じ source extent を持つ。`use` と spec の間の
`I+` は node 直下であり、`UseTree` の中には入れない。

### `UseTree`、form marker、`UsePath`

各 recursive spec は `SyntaxKind::UseTree` で包む。最初に form head、次に normalized prefix path、
terminal、alias、qualifier の順で書く。

```text
FormHead :=
      ModKw I+
    | RealmKw Slash
    | BandKw ColonColon

PathSegment :=
      Identifier
    | OperatorName

OperatorName := LParen Operator RParen

UsePath :=
    PathSegment ((ColonColon | Slash) PathSegment)*
```

`UsePath` は `SyntaxKind::UsePath`、parenthesized operator segment は
`SyntaxKind::OperatorName` で包む。word segment は追加 wrapper を置かず `Identifier` token を直接
`UsePath` の child にする。operator segment の `Operator` token は括弧を含まず、`OperatorName` node と
`UseSegment::Operator.range` は両括弧を含む。`UseSegment::Operator.text` は内側 token の source text である。

`UsePath` node は AST の `UsePath.segments` が non-empty のときだけ作る。root group や marker 直後の
group / glob に対応する empty `UsePath` は source byte を持たないため、valid CST に zero-width node を
作らず、`UsePath` child の absence で表す。zero-width node は recovery の `Missing` に限定する。

form head は専用 wrapper node を作らず、`UseTree` の direct children とする。

- `mod` は `ModKw` と直後の `I+` を emit し、その後の `UsePath` は必ず `Identifier` から始まる。
  `mod` 自体は normalized path に入らない。
- accepted `realm/` marker は `RealmKw`, `Slash`、accepted `band::` marker は `BandKw`,
  `ColonColon` とする。marker separator は `UsePath` にも terminal join にも入らない。
- Plain の `realm::x`、`band/x`、`other/x` では marker kind を使わない。先頭 spelling は
  `UsePath` 内の `Identifier`、separator は同じ `UsePath` 内の token になる。
- marker 直後に group / glob が来る場合、marker separator は form head にすでに現れているので
  AST の terminal `join` は `None` のままである。

現在の AST-producing parser は normal path の parenthesized operator segment をまだ全 transition で
recognize していない。しかし `UseSegment::Operator` と設計済み state table は spec start と separator
target の両方でこれを要求する。direct continuation は exclusion 専用 branch へ限定せず、Plain の
`PathSegment` として両位置で `OperatorName` を受理する。

`UseTree` の terminal 別 child list は次である。

```text
Single tree :=
    FormHead? UsePath
    (I+ UseAlias)*
    UseQualifiers?

Group tree :=
    FormHead? UsePath?
    TerminalJoin?
    UseGroup
    (I+ UseAlias)*
    UseQualifiers?

Glob tree :=
    FormHead? UsePath?
    TerminalJoin?
    UseGlob
    UseQualifiers?

TerminalJoin := ColonColon | Slash
```

`TerminalJoin` は wrapper を作らず `UseTree` の direct token とし、直後の `UseGroup` / `UseGlob` と
`UsePath` の sibling にする。これは AST の `UseTerminal::{Group, Glob}.join` に一対一で対応する。
separator を `UsePath` に入れると末尾に target segment のない path になり、terminal node に入れると
brace / star 自体の source extent が join まで広がるため、どちらも採らない。

`UseTerminal::Single` は source 上の terminal token を持たないため node を作らない。`UseGroup` /
`UseGlob` child がないことと、non-empty `UsePath` が完了したことから derived する。marker なしの
Plain glob は path と join を必須とし、`use *` は引き続き不受理である。Realm / Band marker が terminal
origin をすでに与えた場合は empty path、`join = None` の glob を許す。

### `UseGroup`

group terminal は `SyntaxKind::UseGroup` で包み、join token を含めず opening brace から closing brace
までを所有する。

```text
UseGroup :=
    LBrace G*
    (UseTree G* (Comma G*)?)*
    RBrace

# direct child sequence
LBrace
G*
(UseTree G* (Comma G*)?)*
RBrace
```

ただし隣り合う二個の `UseTree` の間は、comma があるか、間の `G*` の source range が CR / LF を含む
場合だけ valid である。block comment token の内側に physical newline がある場合も、現在の
`consume_group_trivia` と同じく newline separator として数える。synthetic comma、implicit-separator
token、separator node は作らない。

この sequence により、`{}`、`{ /*c*/ }`、`{a,b}`、`{a\n b}`、`{a,}`、`{a,\n}` を同じ node shape で
表せる。comma は group の punctuation であって前後どちらかの `UseTree` の一部ではないため、group 直下の
sibling にする。nested group の item は同じ `UseTree` continuation を再帰的に呼ぶ。

group terminal の後ろに認識された alias は `UseGroup` の外、親 `UseTree` の `(I+ UseAlias)*` に置く。
したがって `UseGroup` node の extent は常に `{` から対応する `}` までであり、semantic validation が
group alias を拒否しても group 内の complete child CST は変わらない。

### `UseAlias`

一回の `as name` は `SyntaxKind::UseAlias` で包む。

```text
UseAlias := AsKw I+ Identifier
```

alias を導入した `I+` は `UseAlias` の直前にある親 node の child、`as` と name の間の `I+` は
`UseAlias` の child である。これにより `UseAlias` node 自体は `as` から name の末尾までになり、
`WordSpan` は最後の `Identifier` token と一致する。反復 alias は source order の別 node として全部残す。
最後の一個へ上書きせず、既決の semantic validation が repeated / group / glob alias を判定する。

Single / Group tree の alias は `UseTree` 直下に置く。Glob tree だけは次節の source-order constraint により
`UseGlob` の child に置くが、commit continuation はどちらの場合も同じ `UseTree.aliases` vector へ同時に
追加する。

### `UseGlob` と `without`

glob terminal は `SyntaxKind::UseGlob` で包む。node は `Star` から始まり、glob tail に属する alias と
optional `without` clause までを source order で所有する。

```text
UseGlob :=
    Star
    (I+ UseAlias)*
    (
        I+ WithoutKw I+
        UseExclusion
        (Comma G* UseExclusion)*
    )?
```

top-level `without` list では first exclusion の前に inline trivia が必須である。二個目以降は comma が
必須で、comma の直前には trivia を挟まない。comma 後は `scan_trivia` の maximal runをそのまま `G*` として
emit するため、改行を含められる。newline だけを top-level exclusion separator としては使わない。

`UseTree.aliases` が AST 上は terminal と sibling の field である一方、source grammar では glob alias が
`Star` と `without` の間に現れる。`UseGlob` が optional `without` を一つの contiguous node として包み、
新しい `UseWithout` wrapper を増やさないため、glob alias の `UseAlias` node は `UseGlob` 内へ置く。
semantic AST と CST の parent を無理に一対一にせず、source-contiguous construct を優先する決定である。
alias vector は continuation が同時に作るため、この nesting 差を CST 再走査で埋めない。

`without` がない場合も `UseGlob` は `Star` と accepted alias の末尾で閉じる。version / `with` は glob
selection ではなく tree qualifier なので `UseGlob` を閉じた後の `UseQualifiers` に置く。

### `UseQualifiers`、`UseVersion`、`UseAnchor`

version または anchor が一つでも存在するときだけ `SyntaxKind::UseQualifiers` を作る。ordered children は
次である。

```text
UseQualifiers :=
      I+ UseVersion (I+ UseAnchor)?
    | I+ UseAnchor

UseVersion := Version

UseAnchor :=
    WithKw I+ UsePath
```

`UseVersion` は `SyntaxKind::UseVersion` で包み、その唯一の child は source spelling 全体を持つ
`Version` token である。`v1-alpha+build.2` も一 token のままで、内側の dot / hyphen / plus を別 token に
分割しない。`UseVersion.range` / `text` はこの token から同時に得る。

`UseAnchor` は `SyntaxKind::UseAnchor` で包む。anchor の `UsePath` は word segment のみを許し、group、glob、
parenthesized operator segment を許さない。separator token の shape は通常の `UsePath` と同じである。

qualifier 全体を `SyntaxKind::UseQualifiers` で包むのは、version だけ、anchor だけ、version + anchor の三形を
一箇所から typed に取得し、group item / glob tail のどちらに付いた suffix も同じ subtree として扱うためで
ある。qualifier がない valid tree に empty `UseQualifiers` node は作らない。

### `UseExclusion` と `UseExclusionGroup`

`without` list の一 item は必ず `SyntaxKind::UseExclusion` で包む。payload は次のいずれか一個である。

```text
UseExclusion :=
      Identifier
    | OperatorName
    | Star
    | UseExclusionGroup

UseExclusionGroup :=
      LParen G* (UseTree G* (Comma G*)?)* RParen
    | LBrace  G* (UseTree G* (Comma G*)?)* RBrace
```

`UseExclusionGroup` の item separation、empty / trailing comma、implicit newline rule は `UseGroup` と同じ
machine を使う。delimiter spelling は source のまま `LParen` / `RParen` または `LBrace` / `RBrace` に
する。group の child は AST の `UseExclusion::Group.items` と同じく recursive `UseTree` であり、
`UseExclusion` の flat listへ変換しない。

exclusion position では parenthesized operator recognizer を group recognizer より先に probe する。
したがって `(*)` は次の shape になり、glob exclusion や parenthesized groupに潰れない。

```text
UseExclusion
  OperatorName
    LParen
    Operator "*"
    RParen
```

bare `*` は `UseExclusion > Star`、`(a, b)` は
`UseExclusion > UseExclusionGroup(LParen ... RParen)` になる。group probe と operator probe のいずれも
accepted 前には emit しない。

### Use AST field と visible CST の対応

lossless invariant は「semantic field ごとに専用 node が必要」という意味ではなく、source byte が一度だけ
typed token として存在し、semantic valueを commit 時に同じ recognition result から作れることを要求する。
専用の source child を持たない field は次の通りである。

| AST field / value | CST での表現と理由 |
| --- | --- |
| `UseDeclaration.range`, `UseTree.range`,各 segment / version / exclusion の range | node / token の source extent から commit 時に同時に得る metadata。range 自体は source text ではない |
| implicit `Visibility::Private` | visibility keyword の absence。明示 private は `MyKw` で区別できる |
| `HeaderImportForm::Plain` | form-marker token の absence。Mod / Realm / Band は専用 keyword token と marker separator で可視 |
| empty `UsePath` | `UsePath` child の absence。source byte がない valid valueへ zero-width node を作らない |
| `UseTerminal::Single` | `UseGroup` / `UseGlob` child がない完了 path。source 上の terminal marker がない |
| `UseTerminal::{Group, Glob}.join` | terminal 直前の direct `ColonColon` / `Slash` token。`None` は token の absence |
| `UsePath.separators` / `UseSeparator` | `UsePath` 内の literal separator token。marker separator、terminal joinとは親と位置で区別する |
| `UseTree.aliases` | source order の `UseAlias` node。Glob では contiguous `UseGlob` 内、他 terminal では `UseTree` 直下にあるが、vector は parse 時に同じ continuation が作る |
| `UseQualifiers.version` / `anchor` の `Option` | `UseVersion` / `UseAnchor` child の presence / absence |
| `UseVersion.text` |一個の `Version` token の raw spelling。canonical version value はまだ計算しない |
| `UseSegment::Word` | `Identifier` token。segment ごとの冗長 wrapper は置かない |
| `UseSegment::Operator.text` | `OperatorName` 内の `Operator` token。segment range は括弧を含む node extent |
| `UseExclusion::Glob.range` | `UseExclusion` 内の bare `Star` token extent |
| normalized form / projected header route | CST に synthetic token を足さない。semantic AST / fact は同じ accepted ranges から同時に作る |

### `use` の canonical tree 例

`use std::io::{read, write}` は次の shape になる。indent は Rowan parent / child を表す。

```text
UseDeclaration
  UseKw "use"
  Whitespace " "
  UseTree
    UsePath
      Identifier "std"
      ColonColon "::"
      Identifier "io"
    ColonColon "::"          # terminal join
    UseGroup
      LBrace "{"
      UseTree
        UsePath
          Identifier "read"
      Comma ","
      Whitespace " "
      UseTree
        UsePath
          Identifier "write"
      RBrace "}"
```

`use std::* as all without {foo, (*)} v1 with program::ui` の terminal tail は次になる。

```text
UseTree
  UsePath
    Identifier "std"
  ColonColon "::"            # terminal join
  UseGlob
    Star "*"
    Whitespace " "
    UseAlias
      AsKw "as"
      Whitespace " "
      Identifier "all"
    Whitespace " "
    WithoutKw "without"
    Whitespace " "
    UseExclusion
      UseExclusionGroup
        LBrace "{"
        UseTree
          UsePath
            Identifier "foo"
        Comma ","
        Whitespace " "
        UseTree
          UsePath
            OperatorName
              LParen "("
              Operator "*"
              RParen ")"
        RBrace "}"
  UseQualifiers
    Whitespace " "
    UseVersion
      Version "v1"
    Whitespace " "
    UseAnchor
      WithKw "with"
      Whitespace " "
      UsePath
        Identifier "program"
        ColonColon "::"
        Identifier "ui"
```

### `OperatorHeaderDeclaration`

operator header 全体は `SyntaxKind::OperatorHeader` で包む。ordered children は次である。

```text
OperatorHeader :=
    (VisibilityKw I+)?
    (LazyKw I+)?
    FixityKw I*
    OperatorName
    BindingPowerSlots
    I* Equals

VisibilityKw := PubKw | MyKw | OurKw
FixityKw := PrefixKw | InfixKw | SuffixKw | NullfixKw

OperatorName :=
    LParen Operator RParen

BindingPowerSlots :=
      /* nullfix: empty */
    | I+ BindingPower                         # prefix: right
    | I+ BindingPower                         # suffix: left
    | I+ BindingPower I+ BindingPower         # infix: left, right

BindingPower :=
    Integer (Dot Integer)*
```

`VisibilityKw` と `LazyKw` の後ろは non-empty inline trivia を必須とする。fixity と `(` の間、最後の
binding power と `=` の間は empty でもよい inline trivia で、physical newline は許さない。
`OperatorName` 内にも trivia を許さない。operator spelling 全体を一個の `Operator` token にし、dynamic
expression scanner の NUD / LED classificationは呼ばない。`*` が name なら `Star` ではなく
`Operator` である。

`BindingPower` は一 vector ごとに `SyntaxKind::BindingPower` で包み、digit component ごとに
`Integer` token、component 間に literal `Dot` token を置く。`5.0.1` を一個の number token にせず、
`Integer("5"), Dot("."), Integer("0"), Dot("."), Integer("1")` とする。raw spellingを保持したまま、
semantic `BindingPower` は各 component を一度だけ `i8` へ変換して同時に作る。

left / right 専用 node kind は作らない。fixity と `BindingPower` child の個数 / source order から role が
一意に決まる。

| fixity | `BindingPower` children | semantic mapping |
| --- | --- | --- |
| `NullfixKw` | 0 | left = `None`, right = `None` |
| `PrefixKw` | 1 | first = right |
| `SuffixKw` | 1 | first = left |
| `InfixKw` | 2 | first = left, second = right |

header node は trailing `Equals` を含み、その byte の直後で閉じる。`=` の後の trivia と body は
`OperatorHeader` に含めない。これにより node extent と `OperatorHeaderDeclaration.range`、
`HeaderOperator.range` が同じになり、header mode は同じ位置から opaque body scan、full mode は通常の
body grammar へ進める。

`OperatorHeaderDeclaration` の source-visible でない field は次の通りである。

| field | CST での表現と理由 |
| --- | --- |
| `range` | `OperatorHeader` node extent。metadata 自体は token ではない |
| default private visibility | `VisibilityKw` の absence。明示 `my` と区別できる |
| `lazy: bool` | `LazyKw` の presence / absence |
| `fixity` |一個の `FixityKw` kind |
| `name: &str` | `OperatorName` 内の `Operator` token text。括弧は別 tokenとして lossless に残る |
| left / right binding power `Option` | fixity と positional `BindingPower` child から同時に決まる |
| `BindingPower.components` の数値 |各 `Integer` token text の semantic conversion。raw digit spellingは CST に残る |

たとえば `pub lazy infix (<+>) 5.0 5.1 =` は次の shape になる。

```text
OperatorHeader
  PubKw "pub"
  Whitespace " "
  LazyKw "lazy"
  Whitespace " "
  InfixKw "infix"
  Whitespace " "
  OperatorName
    LParen "("
    Operator "<+>"
    RParen ")"
  Whitespace " "
  BindingPower
    Integer "5"
    Dot "."
    Integer "0"
  Whitespace " "
  BindingPower
    Integer "5"
    Dot "."
    Integer "1"
  Whitespace " "
  Equals "="
```

### 非自明な nesting choice の根拠

- path 内 separator、terminal join、form-marker separator は同じ spelling でも semantic slot が違う。
  wrapper kind を増やさず、parent と sibling position で一意に区別する。
- comma / newline / comment は list の構造情報であり、前後の item の意味内容ではない。group 直下の
  sibling にすると implicit newline separator と trailing comma を synthetic node なしで保持できる。
- valid empty path と Single terminal に zero-width node を作らない。source にない構造 marker を追加すると
  `Missing` recovery nodeとの区別が弱くなるためである。
- `UseGlob` は star から `without` の最後まで contiguous にする。そのため source 上で間に挟まる glob alias
  も同 node に入る。AST field ownershipより、編集・range queryで一続きの syntax constructになることを
  優先する。
- `OperatorName` は use segment / exclusion / operator header で共有する。三者とも「parenthesis で
  operator spelling を identifier-like slotへ入れる」という同じ concrete syntax であり、token kind は
  enclosing grammar slotが区別する。
- binding power の left / right wrapper を増やさない。fixityごとの arity と source orderがすでに role を
  完全に決め、raw vector structureは共通 `BindingPower` nodeで十分に観測できる。

### 必要な `SyntaxKind` 追加

**追加はない。** sub-slice 1 で追加済みの次の vocabulary だけで本節の canonical shapeを表現できる。

- use node: `UseDeclaration`, `UseTree`, `UsePath`, `UseGroup`, `UseGlob`, `UseAlias`,
  `UseQualifiers`, `UseVersion`, `UseAnchor`, `UseExclusion`, `UseExclusionGroup`
- operator-header node: `OperatorHeader`, `OperatorName`, `BindingPower`
- contextual / header token: `UseKw`, `ModKw`, `RealmKw`, `BandKw`, `AsKw`, `WithoutKw`,
  `WithKw`, `PubKw`, `MyKw`, `OurKw`, `LazyKw`, `PrefixKw`, `InfixKw`, `SuffixKw`, `NullfixKw`,
  `Version`
- shared token: `Identifier`, `Integer`, `Operator`, `Dot`, `ColonColon`, `Slash`, `Comma`, `Star`,
  `LParen`, `RParen`, `LBrace`, `RBrace`, `Equals` と typed trivia kinds

`UseWithout`、`UseSegment`、`UseSeparator`、`Visibility`、`LeftBindingPower`、
`RightBindingPower` の node variant は追加しない。それぞれ `UseGlob` の contiguous child list、token / node
position、または semantic value だけで一意に表せるためである。

### Open questions

この追補の direct-CST node shape について、既存 code / design から解けずに残る question は **ない**。

既存章の Still open である version validation、`with` resolution、fixture schema の qualifier / glob field、
late `use` / `mod` discovery、operator-table build conflict diagnostic、`TriviaParts` inline capacity は、この
追補では変更しない。いずれも raw syntax を上記 CST へ lossless に置くことを妨げず、slice 3 の
node nestingを追加判断なしで実装できる。

### Ready for implementation checklist

Terra-tier implementation session は次を順に機械的に確認する。

- [ ] `SyntaxKind` は増やさず、上の既存 variant と contextual classification をそのまま使う。
- [ ] `CommitOutput` / `Committed` へ `emit_trivia(&TriviaRun)` を通し、full は既存
      `RowanSink::emit_trivia`、header は no-op にする。
- [ ] shared statement intro が visibility + `use`、または visibility + lazy + fixity を一意に確定するまで
      sink call を行わず、accepted 後だけ declaration node を開始する。
- [ ] `UseDeclaration`、recursive `UseTree`、`UsePath` を上の ordered child list 通りに同時 emitし、
      marker separator / path separator / terminal joinを別 slotとして保持する。
- [ ] normal use path の spec start と separator target の両方で parenthesized `OperatorName` を受理する。
- [ ] `UseGroup` / `UseExclusionGroup` は comma と `G*` を direct child とし、newline implicit separator、
      empty group、trailing commaを synthetic tokenなしで扱う。
- [ ] `UseGlob` は alias、`without` keyword、flat exclusion listを source orderで包み、各 itemを
      `UseExclusion`、nested delimiter formを `UseExclusionGroup` で包む。
- [ ] alias、version、anchorをそれぞれ `UseAlias`、`UseVersion`、`UseAnchor` にし、qualifierがある場合だけ
      `UseQualifiers` を作る。repeated alias tokenを捨てない。
- [ ] `OperatorHeader` は modifier / fixity、`OperatorName`、fixity arity通りの `BindingPower`、`Equals` を
      emitし、`=` 直後で閉じる。
- [ ] Header output と Full output が同じ continuation から同じ Use AST / operator declarationを返し、
      node emissionの有無だけが異なることを unit test で固定する。
- [ ] canonical tree test に少なくとも root / nested / empty / newline-separated group、operator segment、
      glob + repeated alias + `without`、version + anchor、4 fixity、visibility + lazy、vector BP を入れる。
- [ ] optional transition failure中の sink call countが0で、accepted trivia/token rangeだけが一度 emitされる
      ことを RecordingOutput で検査する。
- [ ] slice 対象 source で node balance、contiguous token coverage、`green.to_string() == source`、
      header/full fact parityをすべて通す。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確認（2026-08-21、direct-CST node-shape 追補案）。
査読はCodex gpt-5.6-terra（high）による事実クロスチェックに基づく: SyntaxKind vocabulary(既存variant過不足なし)、
`CommitOutput`/`Committed`/`FullCstOutput`/`HeaderOutput`いずれにも`emit_trivia`が未露出であること、
`parse_use_declaration`が常に`Visibility::Private`を返すこと、parenthesized operator segment認識が
現状`parse_use_exclusion`経由のみであること、`UseTerminal`/`UseSegment`/`UseQualifiers`/`UseExclusion`/
`OperatorHeaderDeclaration`/`BindingPower`のfield・variant shape、以上すべてを現行コードと突き合わせ、
不一致なし。

## 追補案: cross-module operator provenance と canonical `SyntaxEnvironment` construction boundary

この節は、`Direct Rowan full-parse session` の実装 sub-slice 4 で行う canonical
`OperatorTable` merge を、cross-module origin と constructor boundary まで具体化する。既決の
「imported table を先にコピーし、local header operator を source order で merge する」規則、
同 spelling / 異 fixity の集約、同 fixity 再宣言の `ConflictingFixity`、full parse 中の immutable table
という decision は変更しない。

ここで追加するのは、現在の実装が build 中だけ持って完成 table から捨てている declaration range を
fixity ごとに残す表現、range がどの source に属するかを示す origin、imported table と provenance を
一つの valid な `SyntaxEnvironment` にする入口である。module graph、`ModuleId` allocation、syntax
reexport resolution 自体は `yu-syntax` に移さない。

### Decision summary

- operator declaration origin は、現在 full parse している file を表す `Local` と、file-specific
  `SyntaxEnvironment` の provenance slot を指す `Imported(SyntaxDependencySlot)` の二形にする。
- 完成した `OperatorTable` は、既存 `entries: Vec<OperatorEntry>` と index を共有する cold side table
  `sites: Vec<OperatorFixitySites>` を持つ。prefix / infix / suffix / nullfix の各 capability は、それを
  導入した origin と declaration range を一件ずつ保持する。
- `SyntaxDependencyProvenance` は、resolver / syntax planner が与える diagnostic 用 module label と、
  imported declaration range が属する `SourceRevision` を持つ。slice 内の ordinal である
  `SyntaxDependencySlot` が operator site と provenance record の join key になる。
- non-empty environment の canonical constructor は、caller が確定済みの
  `SyntaxEnvironmentKey`、pre-merged imported `Arc<OperatorTable>`、canonical order の provenance slice を
  一度に渡す `SyntaxEnvironment::from_imported` とする。constructor は origin/slot の referential
  integrity を検査し、受け取った `Arc` をコピーしない。
- full-parse table は imported table の各 fixity と site を一度コピーした後、local
  `HeaderInfo.operators` を source order で merge し、最後に trie を一度だけ構築する。imported table の
  mutation、overlay、parse 中の rebuild は行わない。

### 現行 shape と blocker

現行 `operator.rs` の `AccumulatedOperator` は `prefix_range` / `infix_range` / `suffix_range` /
`nullfix_range` を持つ。しかし `OperatorTable::from_declarations` が完成した `OperatorEntry` へ移すのは
`spelling` と `fixities` だけで、range は全て失われる。したがって imported table を次の builder へ
渡しても、各 fixity をどの declaration が導入したかを復元できない。

`OperatorTableBuildError::ConflictingFixity` も `first_range` / `second_range` だけを持つ。この二 range が
別 source に属する cross-module conflict では、数値だけを見てもどちらの module を指すか分からない。
range を current file の offset へ写し替えると元 declaration location を失うため、range 自体は元 source
relative のまま保持し、source owner を origin で別に運ぶ必要がある。

現行 `SyntaxEnvironment` は `operators: Arc<parse::OperatorTable>` と
`provenance: Arc<[SyntaxDependencyProvenance]>` を持つが、前者は空 unit struct、後者は
`_private: ()` だけである。`empty()` 以外の constructor もない。上位 architecture が future type として
挙げる `FileId` / `ModuleId` はこの branch にまだ実装されておらず、`HeaderImportRoute` は resolution 前の
source route である。したがって raw import route を resolved module identity として固定してはならない。

### Operator origin と per-fixity declaration site

conceptual production shape は次とする。visibility は canonical `OperatorTable` の public re-export と
syntax-planning API の実装位置に合わせて調整してよいが、field の意味と一対一関係は固定する。

```rust
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OperatorOrigin {
    Local,
    Imported(SyntaxDependencySlot),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct OperatorDeclarationSite {
    origin: OperatorOrigin,
    range: Range<usize>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct OperatorFixitySites {
    prefix: Option<OperatorDeclarationSite>,
    infix: Option<OperatorDeclarationSite>,
    suffix: Option<OperatorDeclarationSite>,
    nullfix: Option<OperatorDeclarationSite>,
}

pub struct OperatorTable {
    entries: Vec<OperatorEntry>,
    sites: Vec<OperatorFixitySites>,
    trie: OperatorTrie,
}
```

`entries.len() == sites.len()` を table construction invariant とし、同じ index の `OperatorEntry` と
`OperatorFixitySites` が一つの logical spelling entry を構成する。
`OperatorEntry` 自体の `spelling` / `fixities` layout と、`OperatorTrieState::Value = &OperatorEntry` は変えない。

各 `sites[index]` は `entries[index].fixities` と同じ presence invariant を持つ。

- `fixities.prefix.is_some() == sites.prefix.is_some()`
- `fixities.infix.is_some() == sites.infix.is_some()`
- `fixities.suffix.is_some() == sites.suffix.is_some()`
- `fixities.is_nullfix() == sites.nullfix.is_some()`

`OperatorFixities` の `PrefixFixity` / `InfixFixity` / `SuffixFixity` を origin wrapper で包み直さない。
NUD / LED role scannerと後段associatorが読むhot `OperatorEntry`は現在のshapeのままにし、build errorと
diagnostic だけが読む metadata を `OperatorTable` の parallel side table に置くためである。既存
`AccumulatedOperator` の四つの `*_range` は `OperatorFixitySites` へ置き換え、build 完了時に
`entries` と同じ order の `sites` vector へ移す。

一個の source-level `HeaderOperator` は一 fixity だけを宣言するため、現在の `OperatorDeclaration` は
次の最小拡張で足りる。

```rust
pub(crate) struct OperatorDeclaration {
    spelling: Box<str>,
    fixities: OperatorFixities,
    origin: OperatorOrigin,
    range: Range<usize>,
}
```

`OperatorDeclaration::from_header_operator` と existing test convenience constructor は
`origin = OperatorOrigin::Local` を使う。imported `OperatorEntry` をコピーするときは、entry 全体を一個の
declaration に戻さない。一 spelling の prefix と infix が別 module 由来であり得るため、各 present fixity
を一 capability ずつ、その fixity に対応する `OperatorDeclarationSite` とともに builder へ seed する。

`OperatorTableBuildError` は現在の first/second naming を維持し、origin field を対称に追加する。

```rust
pub enum OperatorTableBuildError {
    EmptySpelling {
        range: Range<usize>,
    },
    ConflictingFixity {
        spelling: Box<str>,
        fixity: OperatorFixity,
        first_origin: OperatorOrigin,
        first_range: Range<usize>,
        second_origin: OperatorOrigin,
        second_range: Range<usize>,
    },
}
```

`first_*` は accumulator に先に採用済みの declaration、`second_*` は現在 merge しようとした
declaration である。full-parse builder では imported site が常に local より先に入るため、imported/local
conflict は first=imported、second=local になる。local/local conflict は両方 `Local` で、二 range が
source order の declaration を指す。binding power が同じでも、同 fixity の二回目は現行 decision 通り
conflict であり、deduplicate しない。

range の座標系は origin ごとに決まる。

- `Local` の range は現在 `parse_file` に渡された source revision 内の UTF-8 byte range。
- `Imported(slot)` の range は `provenance[slot]` が示す dependency source revision 内の UTF-8 byte
  range。

異なる origin の range 数値を大小比較したり、一つの current-file range へ合成したりしない。error の
deterministic な「最初」は global range sort ではなく、下記 merge order で定義する。

### `SyntaxDependencyProvenance` の concrete content

`SyntaxDependencySlot` は一つの `SyntaxEnvironment` 内でだけ有効な typed ordinal とする。
global module identity、persistent cache key、syntax-interface hash には使わない。

```rust
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SyntaxDependencySlot(u32);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxDependencyProvenance {
    module_label: Arc<str>,
    revision: SourceRevision,
}

impl SyntaxDependencyProvenance {
    pub fn new(module_label: Arc<str>, revision: SourceRevision) -> Self;
    pub fn module_label(&self) -> &str;
    pub fn revision(&self) -> SourceRevision;
}

impl SyntaxDependencySlot {
    pub fn from_index(index: usize) -> Option<Self>;
    pub fn index(self) -> usize;
}
```

`module_label` は syntax planner が resolution 後に選ぶ non-empty、人間可読かつ同 environment 内で
unambiguous な label である。これは diagnostic の「operator was declared in ...」へ使う presentation
data であり、equality join や module resolution の authority ではない。operator site は label 文字列を
複製せず slot だけを持ち、`SyntaxEnvironment` が slot から record を引く。

`revision` は imported declaration の range が属する immutable source snapshot を示す。current code では
`SourceRevision::UNTRACKED` しか割り当てていないが、上位 architecture の `HeaderInfo.revision` と
compiler query revision が接続された後も field shape を変えずに range owner を特定できる。

provenance slice は caller が canonical order で凍結する。slot の value はその slice index であり、
`u32` に収まらない dependency count は environment construction failure とする。順序を変える場合は
operator table 内の全 imported slot も同時に rebase し、`SyntaxEnvironmentKey` も変えなければならない。

この record に `HeaderImportRoute`、current file の `use` range、alias、direct/reexport chain は入れない。
`HeaderImportRoute` は unresolved source-level route であり、group expansion 後の一 record が必ず一つの
resolved source module identityになるとはまだ決まっていない。また transitive reexport の operator range は
original declaring module に属し、consumer の direct `use` range と同じ provenance axis ではない。
今回必要なのは declaration range の source owner までであり、import chain note は syntax-planning
diagnostic の別 data とする。

### Canonical `SyntaxEnvironment` constructor boundary

non-empty environment は次の一入口から作る。

```rust
impl SyntaxEnvironment {
    pub fn from_imported(
        key: SyntaxEnvironmentKey,
        operators: Arc<OperatorTable>,
        provenance: Arc<[SyntaxDependencyProvenance]>,
    ) -> Result<Self, SyntaxEnvironmentBuildError>;

    pub fn dependency(
        &self,
        slot: SyntaxDependencySlot,
    ) -> Option<&SyntaxDependencyProvenance>;
}

pub enum SyntaxEnvironmentBuildError {
    ImportedTableContainsLocalOrigin {
        spelling: Box<str>,
        fixity: OperatorFixity,
        range: Range<usize>,
    },
    MissingDependencyProvenance {
        spelling: Box<str>,
        fixity: OperatorFixity,
        dependency: SyntaxDependencySlot,
        range: Range<usize>,
    },
}
```

constructor は `operators` の全 present fixity site を一度走査し、次を検査する。

1. 全 site が `OperatorOrigin::Imported(slot)` である。
2. 全 slot が `provenance` slice の有効 index である。
3. `OperatorFixities` と `OperatorFixitySites` の presence invariant が一致する。

presence mismatch は public source error ではなく `OperatorTable` 自身の construction invariant violation
であるため、safe constructor / debug assertion で table 作成時に防ぐ。上の public environment error は、
caller が consumer-relative origin を誤って渡した場合と provenance を欠かした場合だけを表す。

provenance record は operator を一件も供給しない selected syntax dependency を含んでよい。したがって
constructor は「全 record が table から参照されること」を要求せず、「table が参照する全 slot に record が
あること」だけを要求する。

`SyntaxEnvironment::empty()` / `Default` は既存の `SyntaxEnvironmentKey::EMPTY`、
`Arc::new(OperatorTable::empty())`、空 provenance slice を使う。non-empty constructor は受け取った二つの
`Arc` を clone-on-write せずそのまま environment に格納し、`operators() -> &OperatorTable` と
`provenance() -> &[SyntaxDependencyProvenance]` の accessor shape は維持する。

`SyntaxEnvironment` が持つ table は **consumer file 用に pre-merged / rebased 済みの imported-only
table** である。他 file の full-parse table は、その file の local declaration site を
`OperatorOrigin::Local` のまま持つため、その `Arc` を別 file の `SyntaxEnvironment` へ直接渡してはならない。
syntax planner は syntax interface から consumer 用 table を作る際、各 exported fixity site を実際の
originating module に対応する `Imported(slot)` へ rebase する。constructor の
`ImportedTableContainsLocalOrigin` がこの relative-origin 取り違えを入口で止める。

`SyntaxEnvironmentKey` は constructor が table から再計算しない。syntax planning query が、operator
semantic content、canonical provenance-slot mapping、dependency revision/hash を含む既決の environment
identity を一度計算して渡す。hash algorithm と public key allocator は `yu-syntax` の parser session
boundary では決めないが、同じ key で異なる slot mapping を渡すことは caller invariant violation である。

### Single-builder merge algorithm

既存章の conceptual signature は維持する。

```rust
fn compile_full_parse_operators(
    imported: &OperatorTable,
    local: &[HeaderOperator],
) -> Result<OperatorTable, OperatorTableBuildError>;
```

この function は `SyntaxEnvironment::from_imported` を通過した table に対してだけ呼ぶ。caller は同じ
`SyntaxEnvironment` を保持しているため、返った `OperatorOrigin::Imported(slot)` を environment の
provenance record へ解決できる。

algorithm は次で固定する。

```text
builder = empty OperatorTableBuilder

for imported entry in canonical spelling order:
    for fixity in [Prefix, Infix, Suffix, Nullfix]:
        if entry has the fixity:
            copy exactly that fixity's binding power/capability
            copy exactly that fixity's OperatorDeclarationSite
            seed builder with the one-fixity value and site

for header operator in HeaderInfo.operators source order:
    convert the one HeaderOperator fixity and binding power once
    site = { origin: Local, range: header.range }
    merge spelling + one fixity + site into builder
    on occupied same-fixity slot, return ConflictingFixity immediately

freeze the spelling map in canonical spelling order
build one OperatorEntry { spelling, fixities } and one matching OperatorFixitySites per spelling
insert every spelling into one new trie
return the immutable OperatorTable
```

imported table はすでに conflict-free なので seed 中に origin を上書きしたり conflict winner を選んだり
しない。同じ spelling に複数 imported fixity があれば一 accumulator entry に集約するが、各 site は
元 fixity のものを保つ。`HeaderInfo.operators` は shared header grammar が declaration source order で
commit した slice をそのまま渡し、range sort や spelling sort を挟まない。

local merge の結果は次の通りである。

| existing imported/local capability | incoming local capability | result |
| --- | --- | --- |
| spelling なし | 任意 fixity | new spelling entry |
| 同 spelling、異 fixity | fixity と BP を追加 | one full-fixity entry、両 site を保持 |
| 同 spelling、同 fixity | BP が同じでも異なっても | first conflict で `ConflictingFixity` |

`OperatorTableBuilder` はこの一 merge の mutable accumulator に限る。完成 table に public mutation API を
追加せず、`SyntaxEnvironment.operators` の trie を cloneして後からpatchする経路も作らない。
`OperatorTable::from_header_operators` は empty imported table + local declarations という同じ builder path
へ委譲し、別の conflict rule を持たない。

build成功後、full parse sessionが完成tableを所有するか`Arc`で固定し、`ParseEnv::full`とoperator-role
scannerはその一referenceだけを見る。後段associatorも`ParsedFile`と同じsyntax-environment revisionのtableを
参照する。header declaration continuationはfull parse中にtable insertを行わない。

### Non-obvious choices の根拠

- `Local` に current module label / revision を埋めない。current source、`HeaderInfo`、revision は
  `parse_file` / full session がすでに一つに固定しており、全 local fixity site に同じ owner を複製する
  必要がない。imported range だけが別 owner を必要とする。
- provenance pointer に `Arc<SyntaxDependencyProvenance>` や module label を直接入れず slot にする。
  同 module の複数 operator / fixity で cold metadata を複製せず、environment の side table を authority に
  できる。scanner hot path は label や revisionへ触れない。
- per-fixity site を `OperatorEntry` inline field にしない。operator trie traversal が返す hot value の
  size/layoutを維持し、diagnostic/buildだけがentry indexでparallel `sites` vectorを読む。logical entryと
  siteの対応はsingle builderが同時にfreezeするため、二つのauthorityにはならない。
- slot を `ModuleId` と呼ばない。上位 architecture は `ModuleId` を module-resolution 側の stable
  structural key としているが、現 branch に型も allocator もない。environment-local ordinal はその decision
  を先取りせず、future planner が本物の `ModuleId` から slot table を作れる。
- `HeaderImport` を origin にしない。一つの import source route と一つの declaration source は同じ概念で
  なく、reexport を通ると一致しない。operator conflict が必要とするのは、まず actual declaration module と
  range である。
- first/second field を old/new へ rename しない。現在の `OperatorTableBuildError` と test shape を最小に
  evolve しつつ、first=accepted、second=incoming という insertion-order semantics を明文化すれば曖昧さは
  ない。

### Open questions

この追補で sub-slice 4 の type storage、constructor invariant、merge order は確定する。次は別 layer の
未決定事項として残し、今回の implementation で推測しない。

1. compiler / module-resolution 側の stable `FileId` / `ModuleId` concrete type、
   `SyntaxEnvironmentKey` の hash/allocator API、およびそれらから canonical provenance order と
   `module_label` を作る規則。上位 architecture は ownership と stable-key requirement を決めているが、
   current branch に concrete type はない。sub-slice 4 は environment-local slot と caller-supplied key/label
   までを boundary とする。
2. imported declaration module から consumer の direct `use` site までの reexport chain を diagnostic note に
   どう載せるか。今回の provenance は actual declaration module + revision + range を失わないが、import
   edge chain は保持しない。
3. `OperatorTableBuildError::ConflictingFixity` をどの syntax-planning recovery site / `DiagnosticId` へ写し、
   `parse_file` が table build failure 後にどの lossless CST と diagnostic ordering を返すか。これは既存章の
   `Still open` を維持し、recovery/diagnostic wiring slice で決める。
4. syntax planner が複数 `SyntaxInterface` から imported-only `OperatorTable` を materialize / rebase する
   public builder API。`yu-syntax` 側の受け入れ shape と validation は本節で決めるが、syntax graph / cycle /
   reexport visibility を所有する producer API は sub-slice 4 に含めない。

1 と 4 は external syntax-planning integration の open question であり、current `yu-syntax` 内の
per-fixity site storage、validated constructor、empty/imported tableを使う merge unit testを妨げない。
3 は public `parse_file` へのfailure wiringを妨げるため、sub-slice 4ではtyped build errorを握りつぶさず、
internal full-session construction boundaryの`Result`として保持する。

### Ready for implementation checklist

Terra-tier implementation session は次を順に機械的に確認する。

- [ ] `parse.rs` の unit `OperatorTable` placeholder を削除し、`operator::OperatorTable` を public canonical
      name として `lib.rs` から re-export する。`OperatorTable::empty()` / `Default` を empty table の
      authority にする。
- [ ] `OperatorOrigin::{Local, Imported(SyntaxDependencySlot)}`、`OperatorDeclarationSite`、
      `OperatorFixitySites` を追加し、`OperatorTable` の parallel `sites` vector が全 present fixity の site を
      build 後も保持する。`entries` / `sites` の length/order invariantをsingle builderで固定する。
- [ ] `OperatorFixities` 自体と NUD / LED 用 accessor は現 shape を維持し、origin lookup を scanner hot path
      に追加しない。
- [ ] `OperatorDeclaration` に origin を追加し、local `HeaderOperator` conversion と既存 unit-test helper は
      `Local` を使う。
- [ ] `ConflictingFixity` に `first_origin` / `second_origin` を追加し、既存 `first_range` /
      `second_range` と同じ accepted/incoming declaration から四 fieldを作る。
- [ ] imported entry copy は entry 全体を一 declaration に潰さず、Prefix / Infix / Suffix / Nullfix の
      stable order で一 capability + corresponding siteずつ seedする。
- [ ] `SyntaxDependencyProvenance` に module label / source revision を実装し、slot lookup accessorを置く。
- [ ] `SyntaxEnvironment::from_imported` が imported-only origin とslot boundsを一度検査し、受け取った
      `Arc<OperatorTable>` / provenance sliceをそのまま保持する。operatorを持たない provenance recordは
      受理する。
- [ ] another fileの`Local` siteを含むfull tableをimported environmentとして渡したcaseと、out-of-range
      slotのcaseを`SyntaxEnvironmentBuildError`にする。
- [ ] `compile_full_parse_operators` が importedを先にcopyし、local `HeaderInfo.operators`をslice orderのまま
      mergeし、一つのnew trieだけをfinish時に作る。
- [ ] imported prefix + local infixの同 spellingが一 entryへ集約され、各binding powerとorigin/rangeが
      保持されるtestを置く。
- [ ] imported prefix + local prefixが、spelling/fixity、first=Imported(slot)+dependency range、
      second=Local+current rangeを持つ最初の`ConflictingFixity`になるtestを置く。
- [ ] local/local same-fixity conflictと、同 spellingの4 distinct fixity集約に既存 semanticsの回帰がない
      ことを確認する。
- [ ] merge前後で`SyntaxEnvironment.operators`のentry/siteが変わらず、full session中のtable mutation /
      lazy rebuildがないことをtestまたはAPI shapeで固定する。
- [ ] public `parse_file`でbuild errorをpanic、empty table fallback、silent overwriteへ変換しない。
      diagnostic wiring未決定の間はinternal session constructorのtyped `Result`として残す。
- [ ] このsub-sliceでmodule path文字列から`ModuleId`を合成せず、`HeaderImportRoute`をresolved identityや
      operator declaration originに流用しない。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確認（2026-08-21、cross-module operator
provenance / environment boundary追補案）。
査読はCodex gpt-5.6-terra（high）による事実クロスチェックに基づく: `AccumulatedOperator`の`*_range`が
`from_declarations`完成時に失われること、`OperatorTableBuildError::ConflictingFixity`の現行フィールドが
`spelling`/`fixity`/`first_range`/`second_range`のみでorigin情報がないこと、`SyntaxEnvironment`が
`operators: Arc<parse::OperatorTable>`（空unit struct、`operator::OperatorTable`とは別型）と
`provenance: Arc<[SyntaxDependencyProvenance]>`（`_private: ()`のみ）を持ち`empty()`以外の
constructorがないこと、`HeaderOperator`が単一fixityしか持たないこと、`compile_full_parse_operators`が
本追補より前の節に既存のconceptual signatureとして存在すること、以上すべてを現行コードと突き合わせ、
不一致なし。

## 追補案: root statement loop、committed recovery、binding continuation、operator merge failure

この節は、`Direct Rowan full-parse session` の第6かつ最後のsub-sliceを、実装時に追加判断が不要な
boundaryまで具体化する。対象はfull modeのroot statement loop、mandatory slot recovery、
`my <name> = <expression>`のdirect-CST continuation、およびfull-parse operator tableの
`ConflictingFixity`をpublic `parse_file`がどう扱うかである。

既決のdirect-CST node shape、`Probe` / `Committed` capability、header/full recovery identity、
canonical immutable `OperatorTable`は変更しない。特に`OperatorHeader` nodeは`=`の直後で閉じ、
`Missing`はzero-width、`Error`は一byte以上を所有するというcontractを維持する。この追補はpublic
entrypointを新pipelineへ切り替える決定ではない。切り替え可能と判断するためのgateを定義するだけである。

### Decision summary

- full rootは`Root`を一度だけ開き、root-owned trivia / semicolonをemitしながら、sink-free
  `StatementIntro` probe、committed continuation、root recoveryをEOFまで繰り返す。
- accepted statement familyは`UseDeclaration`、`OperatorDefinition`、`BindingDeclaration`の三つである。
  operator definitionは既決の`OperatorHeader` nodeと、その後ろのdirect precedence-neutral expression bodyを一つの
  statement control episodeとして扱うが、新しいwrapper nodeは追加しない。
- introがcommitした後のcontinuationはtotalである。mandatory slot failureを`Option::None`でouter
  statement choiceへ返さず、`Complete(T)`または`Incomplete`を返しながら`Missing` / `Error`と
  `CommittedRecoveryRecord`を一対一で作る。
- root `Error`は、現在位置から、delimiter / embedded lexical regionの外側にある最初のsemicolon、
  次のcolumn-zero root lineの直前、またはEOFまでを一episodeとしてconsumeする。keyword spellingだけを
  見てline途中へ同期しない。
- binding valueとoperator definition bodyは、sessionのcanonical `OperatorTable`を渡した
  `parse_direct_expression_with_operators`で読む。旧`FullCstBuilder`のinteger-only special caseへ
  scopeを縮めない。
- `compile_full_parse_operators`相当のmergeで`ConflictingFixity`が生じても、public `parse_file`は
  `ParsedFile`を返す。先に採用済みのfixityを残し、incoming duplicateだけをrejectし、typed construction
  diagnosticを追加して、同じsingle builder passを続行する。
- operator conflictはsource byteのparse recoveryではないため、架空の`Missing` / `Error` nodeを作らない。
  `SyntaxDiagnostic`はcommitted recoveryとoperator-table construction conflictをtyped causeで区別する。

### 現行実装で確認したblocker

現行`FullCstBuilder`が一般statementとして構造化するのは、`emit_header`が`HeaderInfo`のrangeから作る
`UseDeclaration` / `OperatorHeader`を除くと、token kindが正確に
`MyKw Whitespace Identifier Whitespace Equals Whitespace Integer`となり、直後がnewlineまたはEOFである
一形だけである。それ以外のnon-binding部分は`lex() -> Vec<LexedToken>`のtokenを`Root`直下へそのまま流す。
したがってこのold pathの限定性を、新direct grammarの言語scopeとして固定してはならない。

一方、`BindingDeclaration`のfieldは`range`、`name: WordSpan`、`value: Expression`であり、
`Expression` enum自体はidentifier / integerに加えてprefix / nullfix / suffix / infix applicationを表せる。
現行`parse_binding_declaration`が呼ぶ`parse_expression`はidentifier / integerだけの最小helperだが、
`parse_expression_with_operators`とsub-slice 5のdirect continuationは同じ`Expression` domainのdynamic
operator formをすでに実装している。第6sub-sliceのtargetは後者である。

残る五つのblockerは現行codeでも次の通り確認できる。

1. root statement loopとroot synchronization ruleが存在しない。
2. `StatementRole`、`RecoveryKind`、root-level unexpected evidenceのconcrete shapeがなく、
   `CommittedRecoveryRecord`は`_private: ()`だけである。
3. `commit_use_declaration` / `commit_operator_header`以下のmandatory helperは、nodeを開いた後でも
   `Option::None`を返し、recovery nodeもrecordも作らない。
4. bindingはAST-producing `parse_binding_declaration`だけで、direct continuationがない。
5. `SyntaxDiagnostic`も`_private: ()`だけであり、strict operator merge errorを`parse_file`へ写すcontractが
   ない。

`SyntaxKind`には`Missing`、`Error`、`BindingStatement`、全direct expression kindがすでにある。
本追補の最小実装で`SyntaxKind`追加は不要である。

### Statement vocabularyとintro classification

rootとbinding recoveryに必要なclosed vocabularyは次とする。「既存の`GrammarRole` family」とは、本note
冒頭近く（`enum GrammarRole { Declaration(DeclarationRole), ..., Statement(StatementRole), ... }`、
上記の`GrammarRole`/`DeclarationRole`/`ImportRole`/`OperatorHeaderRole`定義を参照）で先に決めた
design上のfamilyを指し、現行`.rs`実装にはまだ存在しない。本追補は、そこで既に導入済みの
`GrammarRole::Statement(StatementRole)` variantの中身を、次のvocabularyまで初めて具体化する。
表示文字列やraw `SyntaxKind`をidentityとして使わない。

```rust
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum StatementKind {
    UseDeclaration,
    OperatorDefinition,
    BindingDeclaration,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum StatementRole {
    Starter,
    Separator,
    TrailingInput { owner: StatementKind },
    OperatorDefinitionBody,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum BindingRole {
    Name,
    DefinitionIntroducer,
    Value,
}

enum DeclarationRole {
    Import(ImportRole),
    OperatorHeader(OperatorHeaderRole),
    Binding(BindingRole),
}
```

`StatementRole::Starter`はrootでknown introが一つも成立しなかったsite、`Separator`はstatement間の
explicit semicolon、`TrailingInput`はcompleteまたはincomplete statementのsemantic end後に同じlogical
lineへ残ったsource、`OperatorDefinitionBody`は`OperatorHeader`の`=`より後ろのfull-only bodyを表す。
bindingの三fieldはdeclaration-specific roleに置き、root starterと同じroleへ潰さない。

shared introは次へ発展させる。

```rust
enum StatementIntro<'source> {
    Use(UseStatementIntro<'source>),
    Binding(BindingStatementIntro<'source>),
    OperatorHeader(OperatorStatementIntro<'source>),
}
```

intro recognitionは次のpriorityではなく、次の構造判定で一意にする。

1. 先頭`use`はuse、先頭fixity wordはoperator、先頭`lazy`の後ろがfixityまたはmandatory fixity recovery
   positionならoperatorとする。
2. `pub` / `our`はvisibilityとしてだけ使い、その後ろが`use`、`lazy`、fixityのいずれかなら対応familyを
   選ぶ。そこまで到達しないprefixはfamilyを推測せずroot starter recoveryへ返す。
3. `my`の後ろにinline trivia、word、inline trivia、`=`がlookaheadできた場合は、word spellingが
   `use` / `lazy` / fixityと同じでもbindingを選ぶ。これは現行`parse_declaration`が
   `my <word> =`をbindingとして受理する範囲を維持する。
4. 3が不成立で、`my`後ろのwordが`use`ならexplicit-private use、`lazy`またはfixityなら
   explicit-private operatorを選ぶ。それ以外、または`my`の直後がnewline / EOF / punctuationならbindingを
   選び、name以降をmandatory recoveryへ渡す。inlineでないvisibility prefixは成立しないため、`my`単独を
   operator/useへ推測しない。
5. recognitionがlookaheadで読んだrangeと`TriviaRun`はtyped introに保持し、commit後に一度だけemitする。
   同じprefixをCST emissionのために再scanしない。

`use` keywordやoperator fixityまでfamilyが確定したら、直後のrequired triviaやpath / nameはintro成功の
条件に含めない。たとえば`use\nuse std::data`の最初の`use`はuse continuationへcommitし、byte 3に
missing pathを作れる。現行`UseStatementIntro.after_use`のようにmandatory tailまでintroへ含めるshapeは
この目的に合わないため、intro fieldは「すでに認識できたprefix」と「continuationが回復すべき最初のslot」を
区別する。

header modeは同じclassifierをcheckpoint下で呼び、Use / OperatorHeaderだけをcommitする。Bindingは
checkpointへ戻して既決通り`FirstNonHeader`で正常停止する。full modeだけが三familyすべてをcommitする。

### Root statement loop

full driverのcontrol flowは次で固定する。

```text
compile one immutable full-parse OperatorTable (with conflict recovery described below)
initialize SourceInput / ParseLocal at file start
start Root

loop:
    scan and emit one maximal root-owned TriviaRun
    if EOF: break

    if current byte is a top-level semicolon:
        emit Semicolon directly under Root
        continue

    if current position is not a root statement start:
        commit one root Error and continue

    checkpoint input + ParseLocal + expectation sink
    intro = probe_statement_intro()
    if intro exists:
        cut; transfer to Committed
        run the selected total continuation
        continue

    rollback to the checkpoint
    commit one root Error and continue

finish Root
finish_complete()
```

root statement startは、file byte 0、top-level semicolon直後、またはroot-owned triviaが少なくとも一個の
physical newlineを含み、そのrunの末尾で`line_indent == 0`となる位置である。水平spaceだけを挟んだ
statement tailを新statementにしない。column-zeroの判定はUTF-8 byte offsetではなく、既存`LineState`が
数えるphysical indentation columnを使う。tabの将来のdisplay width規則をこの判定へ先取りせず、現行scanner
と同じ一code unit一indent stepを維持する。

Use continuationがcomplete `UseDeclaration`を返した場合だけheader fact projection / parity checkへ渡す。
OperatorHeader continuationがcomplete headerを返した場合は、header fact parityを確認した後、full modeだけが
`=`後ろのinline triviaをemitして`parse_direct_expression_with_operators`でbodyを読む。body expression nodeは
`OperatorHeader`のsiblingとして`Root`直下に現れるが、root driver上は同じ
`StatementKind::OperatorDefinition`の完了条件である。header modeは従来通り同じ位置からopaque body scanへ
進む。

binding continuationは一個の`BindingStatement`を完成させる。各statementのsemantic end後、newline / EOF /
semicolon以外が残れば、次のloopで`TrailingInput { owner }`のroot recoveryを行う。continuationが残余byteを
握りつぶしたり、次statementのintroを自身のchildに入れたりしない。

### Root recoveryのsafe point

root recoveryはcurrent non-trivia byte `start`から始め、必ず`end > start`になるまでsource characterを
consumeする。次のうち最も早い位置を`end`とし、boundary自体はconsumeしない。

1. active embedded lexical regionがなく、recovery開始後に開いた`()` / `[]` / `{}`がすべて閉じた状態で
   現れるsemicolonの先頭。
2. 同じouter stateで現れるphysical newlineの先頭で、そのnewlineから始まるmaximal ordinary triviaを
   sink-freeにlookaheadした結果がEOF、または次のnon-trivia byteの`line_indent == 0`となる位置。
3. EOF。

newline後の次lineがindentされている場合、そのnewline、indent、次lineのsourceは同じ`Error` episodeへ
含める。次にcolumn-zeroのlineまたはEOFへ到達した時に止まる。blank line、line comment、block commentを
挟む場合は、最初のboundary newlineより後ろのmaximal trivia全体をroot loopが所有するため、`Error`は
そのnewlineの直前で止まる。

string、heredoc、interpolation、rule literal、quoted / block Yumark、raw / Yulang fence、line comment、
nested block commentの中ではsemicolon / newlineをboundaryにしない。region recognitionとouter delimiter
trackingは`scan::opaque_body`と同じoperator-independent lexical authorityを使う。root recovery専用の簡易
quote counterを別に作らない。ただしreturn valueはopaque bodyのheader coverageではなく、non-empty
`Range<usize>`一個であり、source-wide token列を作らない。

`garbage use std`のline途中に`use`が現れても同期しない。keyword listをraw sourceから検索するとstring /
comment内を誤認し、word spellingを変えただけでrecovery boundaryが変わるためである。semicolonまたは
column-zero lineというstructural boundaryを通った後だけ、root loopがあらためてintro probeを行う。

この規則はprogress guaranteeも兼ねる。boundaryがcurrent positionと一致するsemicolonはroot loop自身が
先にconsumeするため、root recoveryへ渡らない。その他のcaseでは少なくとも一Unicode scalarをconsumeして
からboundaryを探索し、zero-width `Error`や同じpositionでのretry loopを作らない。

### Recovery recordとunexpected evidenceのconcrete shape

recovery kindはnode shapeそのものだけを表し、expected elementを重複してpayloadへ入れない。

```rust
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum RecoveryKind {
    Missing,
    Error,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum UnexpectedSyntax {
    EndOfInput { at: usize },
    Token {
        range: ByteRange,
        category: UnexpectedCategory,
    },
    Root(RootUnexpected),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum UnexpectedCategory {
    Word,
    DecimalInteger,
    OperatorLike,
    Punctuation(PunctuationEvidence),
    OtherCharacter,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum PunctuationEvidence {
    Open(DelimiterKind),
    Close(DelimiterKind),
    Comma,
    Semicolon,
    Dot,
    Slash,
    Colon,
    ColonColon,
    Equals,
    Star,
    Apostrophe,
    Backslash,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RootUnexpected {
    UnrecognizedStarter {
        range: ByteRange,
        head: RootUnexpectedHead,
    },
    TrailingInput {
        owner: StatementKind,
        range: ByteRange,
        head: RootUnexpectedHead,
    },
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum RootUnexpectedHead {
    Word,
    DecimalInteger,
    OperatorLike,
    Punctuation(PunctuationEvidence),
    OtherCharacter,
}
```

`PunctuationEvidence`はdelimiter、comma、semicolon、colon類などdiagnosticに必要なclosed token categoryで
あり、scanner内部の`PunctuationKind`のpublic exposureやlocalized labelではない。root evidenceの`range`は
`Error` node全体のrange、`head`はそのrangeの先頭non-trivia lexical categoryである。source textはrangeから
取得できるためcopyしない。local slot recoveryは`Token`または`EndOfInput`を使い、root statement episodeと
混ぜない。

既存conceptual recordを次の実fieldへ発展させる。

```rust
#[derive(Clone, Debug, Eq, PartialEq)]
struct CommittedRecoveryRecord {
    id: DiagnosticId,
    site: RecoverySiteKey,
    kind: RecoveryKind,
    unexpected: Arc<[UnexpectedSyntax]>,
    expectations: Arc<[SyntaxExpectation]>,
    primary_expectation: usize,
}
```

constructorは次を検査する。

- `Missing`なら`site.range.start == site.range.end`である。
- `Error`なら`site.range.start < site.range.end`であり、少なくとも一件のnon-EOF unexpected evidenceを持つ。
- expectation unionは空でなく、`primary_expectation < expectations.len()`である。
- `Error`のroot range、local consumed range、CST `Error` node rangeが同一である。

full CST emissionは`Missing`なら`start_node(Missing); finish_node()`だけを行う。`Error`なら
`start_node(Error); token(Unknown, range); finish_node()`とし、raw source rangeを一個のchild tokenとして
一度だけemitする。recovery pathのcommit時に`LatestSink`を一度takeし、既決のcandidate union / primary
selectionを行ってから、nodeとrecordを一回ずつcommitする。

### Mandatory slot recoveryの共通規則

commit後のhelper returnは概念上次のshapeにする。

```rust
enum Recovered<T> {
    Complete(T),
    Incomplete,
}
```

`Incomplete`は「CSTとrecovery recordはcommit済みだが、semantic factを作るmandatory valueがない」ことを
表す。commit後に`None`を返してopen nodeをcallerへ残す意味ではない。各continuationは自身が開いたnodeを
必ず閉じ、statement outcomeまで返す。nested use itemの`Incomplete`はそのbranchのfactだけを抑止し、owner
safe pointへ同期できたsiblingを続行する。

mandatory slotは次の共通ruleで扱う。

| slot class | current positionの状態 | recoveryとcontinuation |
| --- | --- | --- |
| required inline separation | newlineを含まず、次slotがcurrent positionで認識できる | current positionへ`Missing(Layout(...))`を置き、sourceをconsumeせず次slotを読む |
| required inline separation | newline / root boundary / EOFで、次slot自体も存在しない | separator単独のrecordを作らず、次のsemantic slotの`Missing`一件へ集約する。boundaryはconsumeしない |
| atomic value | matching valueがある | normal commit |
| atomic value | owner safe pointまたはEOF | current positionへ`Missing(expected)`を置き、inputを止める |
| atomic value | invalid sourceがslotを占有する | 次のlocal candidateまたはowner safe pointまで一byte以上を一個の`Error`にし、candidateがあればslotをretryする |
| fixed punctuation / keyword | following slotがcurrent positionで認識できる、またはowner safe point | punctuationを挿入したものとして`Missing`を置き、following slot / owner closeへ進む |
| fixed punctuation / keyword | invalid sourceが間にある | invalid runを一個の`Error`にし、punctuationまたはfollowing slotでretryする |
| shape discriminator | absent at safe point | `Missing`後にconstructを`Incomplete`としてowner boundaryへ同期する。arityやbranchを推測しない |
| closing delimiter | matching closeがある | normal commit |
| closing delimiter | mismatched closeがある | mismatched delimiter一個を`Error`にしてmatching close探索を続ける |
| closing delimiter | outer/root safe pointまたはEOF | boundaryをconsumeせずmatching closeの`Missing`を置き、owner nodeを閉じる |

local candidateはslot grammar自身をsink-free probeして判定する。たとえばbinding valueならNUD candidate、
path separator後ならword / parenthesized operator / group / glob、`=`ならbody/value NUDがcandidateになる。
raw keyword searchやCST再走査は行わない。

required inline separationは、後続contentが存在するのに区切りだけがない時だけ独立したrecovery siteになる。
`use\nuse std::data`の最初のdeclarationではbyte 3に`Missing(Import(Path))`一件を置き、同じbyteへ
layout `Missing`を重ねない。これは一つのcausal absenceからseparatorとcontentのdiagnosticを連鎖生成しない
規則であり、phase-2のmalformed-header fixtureが固定する一recovery / 一diagnosticと一致する。

continuation familyごとのmandatory slotとowner safe pointは次で固定する。

| continuation | mandatory slots | local / owner safe pointとfact rule |
| --- | --- | --- |
| Use declaration head | `use`後inline separation、最初の`UseTree` target | physical newline、semicolon、root boundary、EOF。target欠落ならdeclaration factは作らない |
| `mod` / path | `mod`後inline separationとfirst identifier、separator後のword / `OperatorName` / group / glob | current groupのcomma / matching close、use suffix introducer、root boundary。separator後target欠落のbranchだけ`Incomplete` |
| parenthesized use operator | non-empty operator spelling、`)` | path separator、comma、matching owner close、inline suffix、root boundary。`(`をacceptした後は別group armへ戻らない |
| alias / `without` / `with` | accepted introducer後のinline separationとalias name / first exclusion / first anchor identifier、separator後のanchor identifier | comma、matching group close、次のvalid suffix、root boundary。introducer keywordを認識した後はoptional transition absenceへrollbackしない |
| use group / exclusion group | comma後のitem、matching `}` / `)` | matching close、comma、newline separator、outer/root boundary、EOF。incomplete item後も次のcomplete siblingを続ける |
| operator modifiers / fixity | modifier後inline separation、fixity discriminator | root boundary / EOF。fixityがなければBP arityを推測せずheader factを作らない |
| operator name | `(`、non-empty spelling、`)` | first BP candidate、`=`、root boundary。nameまたはcloseだけを欠くcaseは`Missing`で後続slotを保つ |
| operator BP / `=` | fixity arity通りのBP、definition introducer`=` | next BP、body NUD、root boundary。i8変換不能なdigit vectorはsourceを保持する`Error`で、zeroやclampへ変換しない |
| binding | `my`後inline separation、name、`=`、value | `=`、value NUD、semicolon、root boundary、EOF。name/valueのないbinding semantic valueは作らない |
| operator definition body | `=`後のbody expression | semicolon、root boundary、EOF。header factはすでにcompleteなら保持し、body recoveryだけをfull-originにする |

groupのnewline separatorはvalid syntaxであり`Missing(Comma)`を作らない。同じlogical lineでcomplete itemの
直後に次item starterが来た場合だけcommaの`Missing`を置く。empty groupとtrailing commaも既決通りvalidで
ある。matching closeがないままcolumn-zeroのknown statement introへ到達した場合は、outer/root safe pointを
優先してcloseの`Missing`を置き、次statementをgroup itemとして飲み込まない。

Use AST / operator header ASTはmandatory fieldがすべて一意に得られたconstructだけを作る。recovery CSTを
後から再走査してpartial factを補完しない。header/full shared rangeで同じrecovery siteが生じた場合は、
既決通りheader-origin recordのID、expectation union、primaryをそのまま再利用する。

### Binding declaration direct-CST continuation

binding nodeは既存`SyntaxKind::BindingStatement`を使い、valid sourceのordered child shapeを次とする。

```text
BindingStatement :=
    MyKw I+
    Identifier I+
    Equals I+
    DirectExpression
```

ここで`I+`は既存のinline `TriviaRun`であり、physical newlineを含まない。現行AST-producing
`parse_binding_declaration`の三箇所の`inline_trivia` requirementを維持する。missing separationは前節の
layout recoveryで表し、synthetic whitespace tokenは作らない。statement前後のtriviaとsemicolonは
`Root`が所有する。

conceptual continuationは次である。

```rust
fn commit_binding_declaration<O: CommitOutput<'_>>(
    intro: BindingStatementIntro<'_>,
    operators: &OperatorTable,
    committed: &mut Committed<'_, '_, ParseErrorSink, O>,
) -> BindingStatementOutcome<O::Checkpoint>;

enum BindingStatementOutcome<'source, C> {
    Complete(ParsedBindingDeclaration<'source, C>),
    Incomplete { range: Range<usize> },
}

struct ParsedBindingDeclaration<'source, C> {
    range: Range<usize>,
    name: WordSpan<'source>,
    value: ParsedExpression<C>,
}
```

continuationは`BindingStatement`を開き、introが保持した`MyKw` rangeをemitし、name / `=`までを
mandatory recovery込みで進める。`=`後ろのaccepted triviaをemitした上で、そのpresenceを
`LeadingTrivia::{None, Present}`へ写し、canonical tableとともに
`parse_direct_expression_with_operators`へ渡す。expression continuationが返す
`ParsedExpression<Checkpoint>`はrangeとleft-wrap checkpointだけを保持し、boxed `Expression` ASTを
production CSTのために作らない。

`Complete`の三fieldはAST `BindingDeclaration`の三fieldと一対一である。`Incomplete.range`は実際に閉じた
recovered `BindingStatement` extentであり、semantic binding factとして公開しない。generic
`BindingDeclaration<V>`へ既存AST型を即座にrefactorするか、上のdirect metadataを別typeにするかはobservable
contractではないが、二つのgrammar authorityやCST再走査を作らないことはcontractである。

source-visible fieldとの対応は次の通りである。

| `BindingDeclaration` field | direct CST / metadata |
| --- | --- |
| `range` | `MyKw`のstartからcomplete expressionのend。recovered incomplete statementは別outcomeであり、架空のcomplete rangeを作らない |
| `name` | `BindingStatement`直下の`Identifier` tokenと、そのscanから同時に得た`WordSpan` |
| `value` | operator-aware direct expression subtreeと`ParsedExpression.range`。CSTからASTを復元しない |

target expressionはidentifier / integerだけでなく、session tableが許すprefix / nullfix / suffix / infixを
含む。`my value = +!a`と`my value = a+!b`はsub-slice 5と同じcandidate fallback / judge semanticsでroleを
確定し、flat item列としてparseする。numeric BP semanticsは後段associationが所有する。
旧`FullCstBuilder`の`my <ident> = <integer>` token patternはcompatibility observationにすぎず、direct
continuationのscope authorityにはしない。

expression startがnewline / semicolon / EOFならvalue roleの`Missing`を置いてnodeを閉じる。invalid byte後に
同じstatement内のNUD candidateがある場合はinvalid runを`Error`にしてcandidateからretryする。candidateが
なければroot boundaryで止まり、次statementをvalueとしてconsumeしない。

### Operator definition bodyのfull-only continuation

既決の`OperatorHeader` shapeは変更しない。complete headerの`Equals`後、full root driverはrequired inline
triviaと一個のdirect expression bodyをmandatory slotとして読む。valid fixture
`infix (<+>) 50 51 = left`では`OperatorHeader("... =")`と`IdentifierExpression("left")`がsource orderの
siblingになり、diagnosticは生じない。

bodyが欠落またはmalformedでも、name / fixity / BP / `=`までcompleteな`HeaderOperator` factは捨てない。
body recoveryは`GrammarRole::Statement(StatementRole::OperatorDefinitionBody)`を持つfull-only eventであり、
header fact parityのIDへ混ぜない。今回のvertical sliceが構造化するbody grammarはsub-slice 5のdirect
precedence-neutral operator-chain domainまでである。将来block、pattern、type、Yumark statement familyを追加する際は`StatementIntro`と
body grammarをclosed enumで拡張し、root raw fallbackを常設しない。

### `SyntaxDiagnostic`とoperator-table conflict

public `parse_file`のsignatureは維持する。

```rust
pub fn parse_file(
    source: Arc<SourceText>,
    header: Arc<HeaderInfo>,
    syntax: Arc<SyntaxEnvironment>,
) -> ParsedFile;
```

`ConflictingFixity`はsourceまたはselected syntax environmentに対するdiagnosable conflictであり、
`Result<ParsedFile, _>`としてCST全体を失うfatal construction errorにはしない。public contractは次である。

1. imported entryをcanonical order、local header operatorをsource orderで一回だけbuilderへ渡す。
2. vacant fixityは従来通り採用する。同spelling / same fixityがoccupiedなら、accepted `first`をtableに残し、
   incoming `second`一capabilityだけをrejectする。binding powerが同じでもdiagnosticにする。
3. conflictをtyped recordへ追加した後も後続declarationを処理し、異なるspelling / fixityを失わない。
4. finish時に、accepted capabilityだけからimmutable entry/site vectorsとtrieを一度作る。
5. degradedだがdeterministicなtableでfull CST parseを最後まで行い、conflict diagnosticをfinal ordered listへ
   入れた`ParsedFile`を返す。

strict unit / constructor boundaryの`compile_full_parse_operators(...) -> Result<OperatorTable,
OperatorTableBuildError>`は、最初のconflictをcallerへ返すfail-fast APIとして維持してよい。production
session preparationは同じ`OperatorTableBuilder::merge` primitiveを使うrecovering wrapperを一回だけ走らせる。
strict functionが一度失敗した後にempty tableでparseしたり、source / HeaderInfoを再走査して二回目のtableを
作ったりしない。

recovering construction boundaryのconceptual shapeは次である。

```rust
struct FullParseOperatorCompilation {
    table: OperatorTable,
    rejected_conflicts: Vec<RejectedOperatorFixity>,
}

struct RejectedOperatorFixity {
    spelling: Box<str>,
    fixity: OperatorFixity,
    first_origin: OperatorOrigin,
    first_range: Range<usize>,
    second_origin: OperatorOrigin,
    second_range: Range<usize>,
}

enum FullParseOperatorConstructionError {
    EmptySpelling {
        origin: OperatorOrigin,
        range: Range<usize>,
    },
}

fn compile_full_parse_operators_recovering(
    imported: &OperatorTable,
    local: &[HeaderOperator],
) -> Result<FullParseOperatorCompilation, FullParseOperatorConstructionError>;
```

`rejected_conflicts`はmerge encounter orderを保ち、全entryがsame-fixity duplicateであることを型で示す。
`OperatorTableBuildError`全体をvectorへ入れて実装者が`EmptySpelling`までrecoverableと解釈するshapeにはしない。
`FullParseSession` constructorはこの`Result`を受け、`Ok`のtableとconflict recordsを同じsessionへ移す。
`Err(EmptySpelling)`は下記の通りsource recoveryではなくconstruction invariant violationである。

`SyntaxDiagnostic`は少なくとも次のtyped causeを保持する形へ発展させる。

```rust
pub struct SyntaxDiagnostic {
    id: DiagnosticId,
    primary: ByteRange,
    cause: SyntaxDiagnosticCause,
}

pub enum SyntaxDiagnosticCause {
    Recovery {
        site: RecoverySiteKey,
        kind: RecoveryKind,
        unexpected: Arc<[UnexpectedSyntax]>,
        expectations: Arc<[SyntaxExpectation]>,
        primary_expectation: usize,
    },
    ConflictingOperatorFixity(OperatorConflictDiagnostic),
}

pub struct OperatorConflictDiagnostic {
    spelling: Box<str>,
    fixity: OperatorFixity,
    first_origin: OperatorOrigin,
    first_range: ByteRange,
    second_origin: OperatorOrigin,
    second_range: ByteRange,
}
```

public field visibilityはaccessor中心に調整してよいが、cause distinctionと両siteの情報は落とさない。
imported originのmodule label / revisionは`SyntaxEnvironment.dependency(slot)`からpresentation時に解決する。
primary rangeは常にincoming local declarationの`second_range`である。imported/local conflictではfirst siteを
dependency revisionのsecondary location、local/local conflictでは両rangeをcurrent revisionのlocationとする。

operator conflictの`DiagnosticId`はfull-construction originのeventとして、header-origin eventの続きから
merge encounter orderで割り当てる。identity keyはtyped
`OperatorConflictKey { spelling, fixity, first_origin/range, second_origin/range }`であり、
`RecoverySiteKey`やmessage stringへ偽装しない。final diagnosticsは既決のprimary range、event、codeのstable
orderで一度sortするため、constructionがparseより先に起きることを表示順へそのまま使わない。

既存のrecovery-only conceptual `DiagnosticIdentity`は、cause authorityを失わない次のsumへ発展させる。

```rust
enum DiagnosticIdentity {
    Recovery {
        revision: SourceRevision,
        origin: RecoveryDiagnosticOrigin,
        event: DiagnosticEventSequence,
        site: RecoverySiteKey,
    },
    OperatorTableConflict {
        revision: SourceRevision,
        event: DiagnosticEventSequence,
        key: OperatorConflictKey,
    },
}

struct DiagnosticEventSequence(u32);

enum RecoveryDiagnosticOrigin {
    Header,
    Full,
}
```

`OperatorTableConflict`はcurrent full parse constructionだけが発行するため、もう一段のoptional originを持たない。
既存conceptual `RecoveryEventSequence`はdiagnostic全causeで共有する`DiagnosticEventSequence`へrenameし、
allocatorはheader recovery、full construction、full recoveryで重複しない一つのrevision-local sequenceを使う。
既存fixtureの`id.origin = "header" | "full"` projectionはrecovery variantだけを投影し、construction variantを
文字列`full` recoveryへ偽装しない。

operator conflictはsource characterをskip / insertしたrecoveryではない。したがってlocal
`OperatorHeader`を`Error`で包んだり、`Missing`をsecond rangeへ置いたりしない。既決の
「1 committed recovery node = 1 recovery diagnostic」は維持するが、逆向きの「全diagnosticがrecovery nodeを
持つ」はconstruction diagnosticには要求しない。phase-2 fixture schemaでoperator conflictをclosed-worldに
assertする前に、`full.construction_diagnostics`相当のadditive projectionを設け、recovery bijectionの対象を
`SyntaxDiagnosticCause::Recovery`へ限定する。これはpresentation wordingや`DiagnosticCode` allocationを
決めなくてもtyped boundaryを実装できる。

`EmptySpelling`はcomplete operator header factがnon-empty nameを要求し、validated imported tableも
non-empty spellingを要求するため、normal `parse_file` inputからは到達しないconstruction invariantである。
malformed sourceのempty nameはheader continuationの`Missing`になりfactをcommitしない。
`ConflictingFixity`とこのinvariant failureを同じdegraded recoveryへ混ぜない。

### Non-obvious choicesの根拠

- root boundaryをknown keywordそのものにしない。line途中のword、string/comment内のspelling、use pathの
  contextual wordをstatementへ誤分割せず、renameでrecovery rangeが変わらない。
- next column-zero lineで、starterがknownかどうかにかかわらず一度止まる。unknown statementが複数line続く
  sourceを一個の巨大な`Error`へ潰さず、一line単位のroot episodeとしてprogressできる。delimiter / lexical
  region内のnewlineだけは同episodeへ残す。
- committed continuationを`Option`のままにしない。direct sinkはrollbackできないため、node start後の
  `None`は構造balanceとdiagnostic ownershipの両方を曖昧にする。`Recovered<T>`はcomplete factの有無と
  CST完走を分ける。
- bindingをold builderのinteger-only shapeへ合わせない。すでに一つのcanonical operator tableとdirect
  expression authorityがあり、scopeを縮めるとsurface AST / full CSTで別grammarになる。
- operator header bodyをroot unknown recoveryへ落とさない。`OperatorHeader`の既決rangeを広げずに、bodyを
  同statement episodeのdirect expression siblingとすることでvalid fixtureをdiagnosticなしで構造化できる。
- conflict時にempty tableへfallbackしない。一つのduplicate fixityのために無関係なimported/local operatorを
  全て失うと、その後のtoken boundaryとdiagnosticが連鎖的に変わる。first-accepted一capabilityだけを残す方が
  merge order、provenance、既存error fieldと一致する。
- conflictをCST recovery nodeにしない。syntaxはlosslessにparseできており、問題は二つのsemantic capabilityを
  一つのsession tableへ入れられないことにある。source consumptionを表す`Error`へ偽装するとrecovery nodeの
  意味が壊れる。

### Sub-slice 6 gate

このsub-sliceを「実装完了」と判定し、old `HeaderCursor` / `lex` / `FullCstBuilder` pathを削除候補にできるのは、
少なくとも次を全て満たした時である。

- internal direct root candidateがUse、4 fixityのoperator definition、operator-aware bindingをsource orderで
  EOFまでparseし、valid fixtureにunexpected root `Error`を作らない。
- bindingとoperator bodyでidentifier / integer、prefix / nullfix / suffix / infix、`+!a` / `a+!b`を
  canonical tableからdirect emitできる。
- use / operator headerの全mandatory slotがcommit後に`Option::None`でabortせず、node balanceを保った
  `Complete` / `Incomplete` outcomeになる。
- root recoveryがsemicolon、column-zero line、EOFの規則通りに同期し、delimiter / string / comment /
  interpolation / rule / Yumark / fence内部で早期分割しない。
- every-byte-prefixとrepresentative malformed corpusでpanic / hang / zero-progressがなく、全`Missing`が
  zero-width、全`Error`がnon-emptyである。
- committed recovery nodeと`SyntaxDiagnosticCause::Recovery`が一対一で、header/full exact siteは同じIDと
  frozen expectation unionを再利用する。
- `ConflictingFixity` caseがfirst-accepted fixityでparseを継続し、両origin/rangeを持つ一construction
  diagnosticを返す。empty-table fallback、silent overwrite、CST dropがない。
- all current phase-2 parser fixturesでheader fact / range parity、diagnostic identity、CST node balance、
  contiguous token coverage、`green.to_string() == source`が成立する。
- old pathとnew internal candidateのvalid fixture projectionを比較し、old pathが構造化していた
  `BindingStatement` / `IntegerLiteral`をnew pathが少なくとも同等以上のtyped shapeで保持する。
- production candidateにsource-wide token/event buffer、CST replay、old lexer fallback、parse中のoperator
  table mutation / rebuildがない。

このgateを満たしても、本追補だけを根拠にpublic `parse_file`を切り替えない。code landing後のtest結果とdiffを
Claude / userが確認した上で、entrypoint cutoverとold path削除を同じimplementation changeで行うか決める。
long-lived feature flag、runtime fallback、二つのpublic parser authorityは作らないという既決方針は維持する。

### Open questions

この追補のsub-slice 6 implementationをblockするopen questionは**ない**。root safe point、mandatory slot
recovery、binding scope、operator bodyの最小full continuation、`ConflictingFixity`後のpublic return contractは
上記で確定する。

別layerの既存open questionであるversion / `with` resolution、late `use` / non-header `mod`のsource-set
discovery、stable `ModuleId` / syntax-environment key allocator、reexport chain presentation、
`TriviaParts` inline capacityは変更しない。operator conflict用fixture schemaのadditive field名とlocalized
message / diagnostic codeもpresentation / contract-versioning作業として後続できるが、typed cause、両site、
first-accepted degraded tableという実装判断はopenに戻さない。

### Ready for implementation checklist

Terra-tier implementation sessionは次を順に機械的に確認する。

- [ ] `StatementKind`、`StatementRole`、`BindingRole`、`RecoveryKind`、`UnexpectedSyntax`、
      `RootUnexpected`をclosed enumとして追加し、raw message / `SyntaxKind` / free-form stringをidentityにしない。
- [ ] `CommittedRecoveryRecord`へID、typed site、kind、unexpected evidence、expectation union、primary indexを
      実fieldとして入れ、Missing/Error range invariantをconstructorで検査する。
- [ ] `CommitOutput` / `Committed`に一対一の`emit_missing` / `emit_error` recovery pathを置き、full outputは
      zero-width `Missing`または`Error > Unknown(non-empty range)`、header outputは同じrecordだけをcommitする。
- [ ] statement introをUse / Binding / OperatorHeaderへ拡張し、`my <word> =` lookaheadをvisibility付きheader
      prefixより先に構造判定する。probe中のsink call countは0に保つ。
- [ ] `use` keyword / operator family確定後のmandatory tailをintro success条件から外し、malformed
      declarationをcommitted continuation内でrecoverできるようにする。
- [ ] commit後のuse / operator helperを`Option::None` abortから`Recovered<T>` / total outcomeへ変え、全open
      nodeをowner continuationが閉じる。
- [ ] mandatory slot table通りにlocal candidate / owner safe pointを実装し、optional `as` / `without` / `with`
      keywordをacceptした後はmissing tailをoptional absenceへrollbackしない。
- [ ] group / exclusion groupのmatching close、mismatched close、comma、newline sibling、outer/root boundary、EOFを
      testし、incomplete child後のcomplete sibling factを保持する。
- [ ] root recovery scannerをopaque lexical-region authorityと共有し、non-empty consume、top-level semicolon、
      next column-zero line、EOFの最早boundaryを返す。mid-line keywordへ同期しない。
- [ ] `commit_binding_declaration`を`BindingStatement` shape通りに実装し、canonical tableを渡した
      `parse_direct_expression_with_operators`でvalueをemitする。新しいbinding node kindは追加しない。
- [ ] complete operator header後、full modeだけがrequired trivia + direct expression bodyを読み、header modeは
      opaque scanを維持する。body failureでcomplete header factを捨てない。
- [ ] full rootがleading / inter-statement / trailing triviaとsemicolonを`Root`直下へ一度だけemitし、EOFで
      `finish_complete`する。
- [ ] recovering operator compilationがsingle builder passで全incoming conflictをcollectし、first capabilityを
      保持、secondだけをrejectして、後続の異fixity / spellingを採用する。
- [ ] `SyntaxDiagnostic`へRecovery / ConflictingOperatorFixityのtyped causeを追加し、conflictに架空のCST
      recovery nodeを作らない。imported originはenvironment provenanceからmodule/revisionへ解決できる。
- [ ] valid use/operator/binding fixtures、`use\nuse ...`、missing delimiter / BP / equals / value、unknown root line、
      indented continuation、semicolon recovery、string/comment/Yumark/fence内fake boundaryをtestする。
- [ ] local/localとimported/local conflictで`parse_file`が`ParsedFile`を返し、lossless CST、degraded tableに基づく
      stable parse、両site diagnosticを保持することをtestする。
- [ ] every-byte-prefix fuzz、node / token coverage、`green.to_string() == source`、header/full recovery ID parity、
      speculative sink call count 0をgateとして通す。
- [ ] gate確認前にpublic `parse_file`をnew pipelineへ切り替えず、切り替えるchangeではold
      `HeaderCursor` / `lex` / `FullCstBuilder`をfallbackなしで一括削除する。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確認（2026-08-21、direct-parse cutover
sub-slice 6追補案）。
査読はCodex gpt-5.6-terra（high）による事実クロスチェックに基づく: `BindingDeclaration`のfield shape、
`SyntaxKind`の`Missing`/`Error`/`BindingStatement`/各direct expression kindの存在、
`CommittedRecoveryRecord`/`SyntaxDiagnostic`が現状`_private: ()`のみであること、
`commit_use_declaration`/`commit_operator_header`が現状mandatory helperの失敗を`Option::None`で
伝播しrecovery nodeを作らないこと、`scan::opaque_body`がoperator-independentなlexical-region権限を
持つこと、以上を現行コードと突き合わせ不一致なし。2点だけ訂正した:
「`FullCstBuilder`がheader構造化分を除く全部を生tokenで流す」という精度の粗さと、
「`GrammarRole` familyは既存」という記述——現行`.rs`実装には存在せず、design note冒頭近くの
先行section（`enum GrammarRole { ..., Statement(StatementRole), ... }`）で導入済みの
design上の概念であることを明記した。

## 追補案: parenthesized grouped expression `(<expression>)`

> **Status: 2026-08-22 superseded.**
> この節はcommit `8551f356`で設計し、commit `0e3459e9`で実装した
> Phase 2.2.2のsingle-expression sliceを記録するhistorical sectionである。
> `Expression::Grouped`、`SyntaxKind::GroupedExpression`、inner一個を必須とするgrammar、
> および`()`をmissing innerとして扱う決定は、直後の
> 「parenthesized expression-listのsurface CSTと推論境界」追補がsupersedeする。
> opening `(`後のcut、binding-power reset、direct sink、total continuation、trivia所有、
> closing-delimiter recoveryについては、後続追補で明示的に変更する箇所以外を引き継ぐ。

この節は、`grammar::expression`のNUDにparenthesized grouped expressionを追加する
designを固定する。対象はAST / direct CSTの形、shared sink-free NUD recognition、
Pratt binding power、group内trivia所有、inner expressionとclosing `)`のmandatory recoveryである。

既決のshared recognition core + commit-aware continuation、`Recovered<T>`によるtotal continuation、
mandatory slotの共通rule、one committed recovery node = one recovery diagnosticは変更しない。
特に、groupのinner expressionには上の表の`atomic value`行、closing `)`には
`closing delimiter`行をそのまま適用する。expression専用の別recovery mechanismは作らない。

### Decision summary

- semantic ASTに`Expression::Grouped { inner, range }`を追加する。`range`はopening `(`から
  matching `)`までを含み、両delimiterの個別rangeはlossless CSTが所有する。
- CSTに`SyntaxKind::GroupedExpression`を一つ追加する。valid sourceのordered childrenは
  `LParen`, inner-leading trivia, inner expression subtree, inner-trailing trivia, `RParen`である。
- `NudRecognition`はopening punctuationのrangeだけを持つ`Group` caseを追加する。
  recognition中にinner expressionをparseせず、CSTもrecovery recordも書かない。
- `(`がaccepted NUDになった後にcutし、inner expressionは
  `BindingPower::scalar(i8::MIN)`で再帰parseする。groupを閉じた後のLED loopはcallerが
  渡したoriginal `minimum`で続行する。
- inner expressionのabsence / invalid bytesは既決の`atomic value`行、closing `)`の
  matching / mismatched / safe-point / EOFは既決の`closing delimiter`行に従う。
- `(`をacceptedしたgroup continuationはtotalである。recovery後もgroup nodeを必ず閉じ、
  direct Pratt controlへ`ParsedExpression`を返す。outer operator body / binding valueが同じsource位置に
  別の`Missing(expression)`を追加しない。

### 現行grammarのgapと既存authority

現行`Expression` enumはidentifier、integer、prefix / nullfix / suffix / infix applicationを持つが、
grouped expressionを持たない。`recognize_nud` も次の三armだけである。

1. `scan_operator(OperatorSite::Nud, ...)`からprefix / nullfix。
2. `parse_identifier`。
3. `parse_integer_literal`。

そのため`(`はvalid expression starterであるにもかかわらず、
`direct_expression_nud_candidate`にもAST-producing `parse_expression_bp`にも
direct-CST `parse_direct_expression_bp`にも見えない。これはdirect-parse cutoverで導入された
regressionではなく、両pathが共有するNUD vocabularyにある長期的なgapである。

一方、必要なbuilding blockはすでに存在する。

- `scan::punctuation::scan_punctuation`は`(` / `)`を
  `PunctuationKind::{Open, Close}(Delimiter::Parenthesis)`とUTF-8 byte rangeで返す。
- `SyntaxKind::LParen` / `RParen`は`OperatorName`で使用済みである。
- `ConstructRole::ExpressionGroup`、`ExpressionRole::Nud`、`Delimiter::Parenthesis`、
  `ExpectedSyntax::Expression`はtyped recovery vocabularyに存在する。
- `parse_expression_with_operators` / `parse_direct_expression_with_operators`はともに
  `BindingPower::scalar(i8::MIN)`をtop-level minimumとして使う。
- `commit_use_group` / `commit_use_exclusion_group`はmatching close、mismatched closeの
  non-empty `Error`、EOFのzero-width `Missing`を実装している。
- `commit_operator_name`はopening `(`をacceptした後にowner nodeを閉じるtotal continuationと、
  absent `)`のclosing-delimiter `Missing`の形を持つ。

したがって新規syntaxに必要なのは、group自身のAST / CST kindとNUD branch、および
これら既存primitiveをexpression continuationへwiringする局所helperだけである。

### Semantic AST shape

`Expression`に次を追加する。field名とrange contractは固定する。

```rust
pub(crate) enum Expression<'source> {
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Grouped {
        inner: Box<Expression<'source>>,
        range: Range<usize>,
    },
    PrefixApplication { /* existing fields */ },
    NullfixApplication { /* existing fields */ },
    SuffixApplication { /* existing fields */ },
    InfixApplication { /* existing fields */ },
}
```

valid groupの`range` は`open.start..close.end`である。`Expression::range()`はこのfieldを
cloneして返す。`open_range` / `close_range`をsemantic ASTに重複保持しない。両punctuationの
kind、raw text、個別range、間のtriviaはCSTからlosslessに観測でき、AST consumerが
group全体のsource extentとinner semantic expressionを持てば足りるためである。

AST-producing pathはvalid groupでのみ`Expression::Grouped`を作る。innerがrecoveryで
`Incomplete`になるmalformed groupは、direct CST / committed recoveryがsource shapeを保持し、
存在しないinner semantic valueを架空のASTで合成しない。

### Direct CST shapeとtrivia所有

`SyntaxKind`に新しいnode variant `GroupedExpression`を追加する。現行のexpression nodeが
`IdentifierExpression` / `PrefixExpression` / `InfixExpression` / `SuffixExpression` /
`NullfixExpression`という「form + `Expression`」順の名前なので、`ExpressionGroup`ではなく
`GroupedExpression`とする。typed recovery ownerの`ConstructRole::ExpressionGroup`は「delimiterを
所有するconstruct」の名であり、Rowan node namingと語順を同じにする必要はない。

valid sourceのcanonical child listは次である。

```text
GroupedExpression :=
    LParen G*
    DirectExpression
    G* RParen
```

ここの`G*`はgroup内の一回のmaximal `TriviaRun`で、emptyでもよく、
`Whitespace` / `Newline` / `LineComment` / `BlockComment`を含められる。各partは
`GroupedExpression`の直下にsource orderでemitし、trivia用wrapper nodeは作らない。
parenthesis内ではouter root newline stopをsuspendし、matching `)`またはowner safe pointを
group continuationが所有する。

opening `(`後の`G*`は「次のaccepted slotと一緒にtriviaをcommitする」という
先行追補のleading-trivia conventionに従う。direct pathはこのrunをemitした後、
empty / non-emptyを`LeadingTrivia::{None, Present}`へ写してinner NUD judgeへ渡す。
inner expression後の`G*`は、failed LED probeがinput / `ParseLocal`とともにrollbackした
runをgroup continuationが一度だけscan / emitする。これによりoperator scannerの
trailing triviaとgroup-owned triviaの二重emitを作らない。

recovery sourceではmandatory slotの位置に既決の`Missing`または`Error > Unknown`を置き、
正常childの順序を変えない。`Missing`はzero-widthでcoverageを進めず、`Error`は
実際にconsumeしたnon-empty source rangeを一度だけ所有する。

### Shared NUD recognitionへの統合

`NudRecognition`に次のcaseを追加する。

```rust
enum NudRecognition<'source> {
    Group {
        open: Range<usize>,
    },
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Prefix(ScannedOperator<'source>),
    Nullfix(ScannedOperator<'source>),
}
```

group armは`scan_punctuation`を呼び、kindが
`PunctuationKind::Open(Delimiter::Parenthesis)`のときだけ`open` rangeを返す小さな
sink-free recognizerとする。raw `item('(')`をexpression内に別authorityとして増やさない。

conceptual dispatchは次の形である。

```rust
i.choice((
    recognize_group_open.map(|open| NudRecognition::Group { open }),
    recognize_nud_operator(table, leading),
    parse_identifier.map(NudRecognition::Identifier),
    parse_integer_literal.map(NudRecognition::Integer),
))
```

`(`はfixed punctuation、operator armはsession tableでacceptedされたprefix / nullfix spelling、
identifier / integerはそれぞれword / ASCII digit startであり、first characterで互いに交わらない。
そのためgroup armの順序はsemanticsを変えない。fixed construct starterを先頭に置くのは
NUD vocabularyを読みやすくするためであり、prefix / nullfixのlongest-candidate fallbackや
identifier / integer recognitionをshadowしない。

`direct_expression_nud_candidate`は引き続き`recognize_nud`を唯一のauthorityとする。
そのためこの一armを追加すれば、declaration recoveryのNUD lookaheadも`(`をvalid candidateと
判定し、別のstarter listを更新する必要はない。

### Commit continuationとbinding power

groupはopening `(`がacceptedされた時点で他NUD formに戻れない。
AST pathの`parse_expression_bp`とdirect pathの`parse_direct_expression_bp`はともにこの時点で
cutする。現行direct pathの「`Prefix`だけcut」という条件は、
`Prefix | Group`をacceptedした場合のcutへ拡張する。

inner expressionのminimumは常に次である。

```rust
let inner_minimum = BindingPower::scalar(i8::MIN);
```

AST pathは`parse_expression_bp(table, &inner_minimum, ...)`、direct pathは
`parse_direct_expression_bp(table, &inner_minimum, inner_leading, ...)`を呼ぶ。prefix operandがoperatorの
right binding powerをminimumにするのと対称的に、groupは内側でprecedenceを完全に
resetするconstructなのでtop-levelと同じminimumを使う。これにより`(a + b)`の
inner LEDはouter callerのmore restrictive minimumに打ち切られない。

groupを閉じた後は、callerの`parse_expression_bp` /
`parse_direct_expression_bp`に既にあるLED loopへ、一つのcompleted left expressionとして戻る。
LED probeが比較するのはinner minimumではなくcallerが受け取ったoriginal `minimum`である。
したがって`(a + b) * c`ではparenthesis内が先に完了した後、`*`はgroup全体を
left operandとする普通のLEDとして解析される。special-case LEDは追加しない。

direct CST continuationのcontrol flowは次で固定する。

```text
accept Group { open }; cut
start GroupedExpression at the NUD checkpoint
emit LParen(open)
push ExpressionGroup delimiter / RightParenthesis stop scope
scan and emit inner-leading TriviaRun
parse or recover the inner expression at scalar(i8::MIN)
scan and emit inner-trailing TriviaRun
commit or recover the closing RParen
pop the group scope on every Complete / Incomplete path
finish GroupedExpression
return one ParsedExpression to the caller's original LED loop
```

`ParsedExpression.range` はmatching closeがあれば`open.start..close.end`、closeが`Missing`なら
`open.start..current_position`である。後者のcurrent positionはboundaryをconsumeしていないため、
trailing group triviaまでは含むが次statement / outer delimiterは含まない。

malformed groupでinner semantic valueが得られなくても、accepted `(`が表すouter NUDは
成立している。direct pathはrecovery済み`GroupedExpression`のrange / checkpointを返し、
outer mandatory value helperが同じsiteにbody/value `Missing`を連鎖させない。AST valueの
complete / incompleteとPratt control上の「NUDをconsumeした」は別の事実である。

### Mandatory inner expression recovery

inner slotのrecovery siteは次のtyped roleを使う。

```rust
GrammarRole::Expression(ExpressionRole::Nud)
ExpectedSyntax::Expression
```

既決の`atomic value`行の適用は次である。

| current position | recoveryとcontinuation |
| --- | --- |
| `recognize_nud` / `direct_expression_nud_candidate`がcandidateを返す | normal commit。inner minimumで再帰parseする |
| matching `)`、outer/root safe point、またはEOFでinner candidateがない | sourceをconsumeせず`Missing(ExpectedSyntax::Expression)`をそのpositionに置き、innerを`Incomplete`とする |
| invalid sourceがslotを占有し、後ろにNUD candidateがある | そのcandidateの直前までのnon-empty rangeを一の`Error` `Unknown`としてconsume / emitし、同じinner slotをretryする |
| invalid sourceからowner safe pointまでcandidateがない | invalid rangeを一のnon-empty `Error`にし、safe pointでinnerを`Incomplete`としてclosing continuationへ移る |

candidate探索はshared `recognize_nud`だけをsink-freeで呼び、identifier spellingやoperator-like
characterをraw searchしない。group内のinvalid byteをouter operator-body recoveryへ返さず、
`ExpressionRole::Nud`のowner-local episodeとしてcommitする。

matching `)`がcurrent positionにあるempty group `()`は、inner `Missing(expression)`を一件作った後、
`)`をnormal commitしてgroup nodeを閉じる。matching closeはinner recoveryがconsumeしないため、
closing slotが同じtokenを一度だけ所有できる。

### Mandatory closing `)` recovery

closing slotのrecovery siteは既存vocabularyだけで表す。

```rust
GrammarRole::ClosingDelimiter {
    owner: ConstructRole::ExpressionGroup,
    delimiter: Delimiter::Parenthesis,
}
ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
    Delimiter::Parenthesis,
))
```

既決の`closing delimiter`行の適用は次である。

| current position | recoveryとcontinuation |
| --- | --- |
| matching `)` | `RParen`をnormal commitし、group scope / nodeを閉じる |
| mismatched `]` / `}` | delimiter一tokenのnon-empty rangeを一の`Error`にし、matching `)`の探索を続ける |
| outer/root safe pointまたはEOF | boundaryをconsumeせずzero-width `Missing(')')`を置き、group scope / nodeを閉じる |

mismatched closeのunexpected evidenceはactual delimiterを持ち、recovery site / expectationはexpected
parenthesisを持つ。このrecord shapeは`emit_import_group_mismatched_close`と同じである。
arbitrary invalid runがinner completion後とmatching closeの間にある場合は、既決の
fixed-punctuation invalid-source行に従ってnon-empty `Error`にし、`)`またはsafe pointでretryする。

matching / missingのどのpathでもdelimiter / stop scopeは一度だけpopし、
`GroupedExpression`は必ずfinishする。close helperが`Option::None`をouter NUD choiceへ返すpathは
作らない。

### 同一owner boundaryでinnerとcloseがともに欠ける場合

`(`の後のtriviaを読んだ位置がEOFまたはouter/root safe pointで、inner expressionも
matching `)`もない場合、二つのmandatory slotは同じzero-width owner boundaryで同時に
stopする。この場合は`Missing(expression)`と`Missing(')')`を連続して二件作らず、
一のcausal absenceを一のcommitted recovery episodeへ集約する。

これは新しいslot recovery ruleではない。先行追補がrequired separationと後続contentの
同一absenceをsemantic slotの一recordへ集約するのと同じ「一つのcausal absenceから
diagnosticを連鎖生成しない」適用である。innerの`atomic value`とcloseの
`closing delimiter`のexpectationはどちらも失わず、一つのrecordのstructured unionに入れる。

recordは次のshapeにする。

```text
site:
  ClosingDelimiter {
    owner: ExpressionGroup,
    delimiter: Parenthesis,
  } @ p..p
kind:
  Missing
expectations:
  - ClosingDelimiter(ExpressionGroup, Parenthesis) -> expected `)`
  - Expression(Nud) -> expected expression
primary:
  expected `)`
```

siteとexact matchするclosing-delimiter candidateが既決のprimary selection tier 0になり、
inner expression candidateはstructured secondary contextとして残る。CSTにはclosing slotの
zero-width `Missing`を一nodeだけ置く。groupのinner semantic valueは`Incomplete`だが、
accepted group NUDのdirect `ParsedExpression`は返す。

matching `)`が存在する`()`はこの集約caseではない。innerのみが欠け、
closeはsource tokenとしてnormal commitできるため、前節のinner `Missing(expression)`一件になる。
innerが存在しcloseだけが欠ける`(value` も集約caseではなく、closing
`Missing(')')`一件になる。

### `header-full-diagnostic-identity` acceptance target

fixture sourceは26 bytesである。関連rangeは次の通りである。

```text
0..3    `use`
3..3    missing import path
4..23   `infix (<+>) 50 51 =` operator header
23..24  body-leading whitespace
24..25  `(`
25..26  newline owned by GroupedExpression
26..26  EOF insertion point for missing `)`
```

grouped-expression support後のfull continuationは次の順序で進む。

1. header phaseの`missing import path @ 3..3`をfull phaseがexact siteで再利用する。
   これが`id = { origin = "header", event = 0 }`である。
2. operator headerは`Equals` byteの直後で23で完了し、23..24のrequired body triviaを
   root / body continuationがemitする。
3. `recognize_nud`は24..25の`(`を`NudRecognition::Group`としてacceptする。
   したがってこのbyteはinvalid body byteの`Error`にならない。
4. `GroupedExpression`は`LParen` と25..26の`Newline`を所有し、EOF 26へ到達する。
5. innerとcloseの同一boundary absenceを一のclosing-delimiter `Missing @ 26..26`へ集約し、
   group nodeを閉じて`ParsedExpression`をbody continuationへ返す。これが
   `id = { origin = "full", event = 1 }`で、primary messageは`expected ')'`である。
6. operator bodyはaccepted group NUDを得ているため、
   `StatementRole::OperatorDefinitionBody`の別`Missing(expression)`を作らない。

したがってfile全体のcommitted recovery / diagnosticは次の **2件だけ** になる。

| order | kind / range | role | diagnostic |
| --- | --- | --- | --- |
| 0 | `Missing @ 3..3` | `Declaration(Import(Path))` | header-origin `expected import path` |
| 1 | `Missing @ 26..26` | `ClosingDelimiter { owner: ExpressionGroup, delimiter: Parenthesis }` | full-origin `expected ')'` |

現状の`(`をinvalid byteとするspurious `Error @ 24..25`は消える。その`Error`の後に
body NUDを再試行して生じていたspurious
`Missing(StatementRole::OperatorDefinitionBody)`も、group continuationが`ParsedExpression`を返すため消える。
代わりに期待値どおりexpression-group ownerのclosing `Missing`が一件だけ残る。

### Non-obvious choicesの根拠

- ASTにparenthesis token rangeを個別保持しないのは、ASTはinner semantic valueとgroup全体の
  extentを必要とし、punctuation / triviaのlossless authorityはCSTだからである。
- `GroupedExpression`を新nodeにするのは、parenthesisがprecedenceを変えるsource-visible
  expression formであり、`IdentifierExpression`やinner applicationの単なるtrivia parentへ潰せないためである。
- inner minimumを`i8::MIN`にするのは、groupがouter precedenceの制限を内側へ持ち込まない
  ことが役割そのものだからである。prefix RHSのbinding powerを流用しない。
- group内triviaをgroup nodeの直下に置くのは、`(` / inner / `)`の間にあるsourceであり、
  failed NUD / LED probeに所有させるとrollback後のemit authorityが消えるからである。
- accepted `(`後のcontinuationをtotalにするのは、direct sinkがrollbackできず、
  open nodeのまま`None`をouter choiceへ返せないという既決の`Recovered<T>` contractによる。
- EOFでinner / closeの二`Missing`を作らないのは、同じowner boundaryの一absenceから
  diagnosticを連鎖させず、既決のexpectation unionで両方の文脈を保持できるからである。
- `(`をoperator-body専用starterに追加しない。shared `recognize_nud`に入れることでAST / direct CST /
  declaration recoveryの全consumerが同じgrammar authorityを使い、fixture path名やstatement ownerによる
  special caseを避けられる。

### Open questions

この節を書いた時点では、single-expression slice内部のgrouped-expression AST / CST shape、
binding-power integration、trivia ownership、mandatory recovery、fixtureの2-recovery acceptance
targetについて、既存code / design / fixtureから解けずに残るquestionはないと判断した。
これはparenthesis全体のcurrent designを閉じる判断ではない。tuple / unitを含むsurface shapeは
後続のsuperseding追補で固定する。

既存のversion / `with` resolution、late `use` / non-header `mod`、syntax-environment key、
reexport presentation、`TriviaParts` inline capacityはこの追補で変更しない。

### Ready for implementation checklist

Terra-tier implementation sessionは次を順に機械的に確認する。

- [ ] `Expression::Grouped { inner, range }`を追加し、valid AST testでinner treeと
      parenthesisを含むrangeを固定する。
- [ ] `SyntaxKind::GroupedExpression`と`YulangLanguage::kind_from_raw`の対応armを追加する。
      `LParen` / `RParen`は既存token kindを使う。
- [ ] `NudRecognition::Group { open }`と`scan_punctuation`を使うsink-free group-open recognizerを
      `recognize_nud`の`choice`へ追加する。operator / identifier / integer armを別dispatchへ複製しない。
- [ ] AST pathとdirect pathの両方でaccepted `Group`後にcutし、continuation failureを
      他NUD armへrollbackさせない。
- [ ] opening `(`後にexpression-group delimiter / right-parenthesis stop scopeをpushし、
      matching / missing / incompleteの全pathで一度だけpopする。
- [ ] inner-leading `TriviaRun`を`GroupedExpression`直下へemitし、presenceを
      `LeadingTrivia`へ写し、inner parseを`BindingPower::scalar(i8::MIN)`で呼ぶ。
- [ ] inner後のfailed LED probeがtriviaをrollbackした後、group continuationが
      trailing `TriviaRun`を一度だけemitする。
- [ ] direct continuationは`GroupedExpression` nodeを必ずfinishし、innerが`Incomplete`でも
      Pratt control用`ParsedExpression`を返す。AST pathは存在しないinner valueを合成しない。
- [ ] inner mandatory slotは`ExpressionRole::Nud` + `ExpectedSyntax::Expression`を使い、
      safe point / EOFの`Missing`、invalid non-empty `Error`、later shared NUD candidateへのretryを
      mandatory-slot表どおり実装する。
- [ ] close mandatory slotは`ConstructRole::ExpressionGroup` + `Delimiter::Parenthesis`を使い、
      matching `)`、mismatched `]` / `}` Error、outer/root safe point / EOFのzero-width Missingを
      `commit_use_group` / `commit_operator_name`と同じshapeで実装する。
- [ ] `()`はinner Missing一件 + normal `RParen`、`(value`はclose Missing一件、
      `(…]` はmismatched-close Error後にclose探索継続というgeneralized recovery testを置く。
- [ ] innerとcloseが同じEOF / outer boundaryで欠けるcaseは一のclose-owned Missingに集約し、
      expectations unionにcloseとexpressionを保持、closeをprimaryにする。
- [ ] direct AST / CST Pratt testに`(a)`、nested `((a))`、trivia / comment / newlineを含むgroup、
      `(a + b) * c`相当のbinding-power reset、group後のouter suffix / infix LEDを追加する。
- [ ] accepted groupのprobe中はsink call countが0、commit後は各source rangeが一度だけemitされ、
      node balance / contiguous coverage / `green.to_string() == source`が成立することを固定する。
- [ ] `header-full-diagnostic-identity` fixtureでcommitted recovery / diagnosticがexactly 2件になることを
      acceptance gateにする。内訳はheader-origin `Missing import path @ 3..3`と
      full-origin `Missing ')' @ 26..26`だけで、`Error @ 24..25`やoperator-body
      `Missing(expression)`を許さない。
- [ ] implementationで`.rs`の変更を行う際は、この追補と無関係なexpression form /
      recovery refactorを同じdiffへ広げない。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確認（2026-08-21、parenthesized
grouped-expression grammar追補案）。
査読はCodex gpt-5.6-terra（high）による事実クロスチェックに基づく: 現行`recognize_nud`が
prefix/nullfix・identifier・integerの3 armのみで`(`を扱わないこと、`scan_punctuation`が
`(`/`)`を`PunctuationKind::{Open, Close}(Delimiter::Parenthesis)`とbyte rangeで返すこと、
`SyntaxKind::LParen`/`RParen`が`OperatorName`で既に使われていること、
`ConstructRole::ExpressionGroup`/`ExpressionRole::Nud`/`Delimiter::Parenthesis`/
`ExpectedSyntax::Expression`が既存のtyped recovery vocabularyに存在すること、top-level
minimumが両path(`parse_expression_with_operators`/`parse_direct_expression_with_operators`)で
`BindingPower::scalar(i8::MIN)`であること、`commit_use_group`/`commit_use_exclusion_group`/
`commit_operator_name`が主張通りのmatching/mismatched/EOF close recovery shapeを持つこと、
fixture`header-full-diagnostic-identity`(26 bytes)の実byte内容とmetadataが追補の
2-recovery acceptance target(`Missing @ 3..3`、`Missing @ 26..26`)と一致すること、
以上すべてを現行コードと突き合わせ不一致なし。

## 追補案: parenthesized expression-listのsurface CSTと推論境界

> **Status: 2026-08-22 amended in place.**
> **Separator-scope status: superseded.** この追補のcomma-only grammar / recovery / gateだけは、末尾の
> 「layout-aware comma-or-newline delimited sequence」追補がsupersedeする。element count、terminal comma marker、uniform
> `ParenthesizedExpression` node、unit / grouping / tupleを推論側で判定するruleは維持する。
> grammar、AST sketch、control flowは末尾のprecedence-neutral operator-chain追補に合わせて
> `elements: Vec<OperatorChain>`へ更新済みであり、各elementをcurrent-depth `Comma | RParen`までflatにparseする。

この節は、直前のhistoricalなparenthesized grouped-expression追補のうち、
single inner expressionを前提とするAST / CST shapeとrecoveryをsupersedeする。
Yulang3のparenthesis NUDは、grouping、unit、tupleというsemantic formをparse時に選ばず、
sourceに書かれたparenthesis、expression列、comma、triviaを一つのuniformなsurface formとして保持する。

直前の追補から次は維持する。

- opening `(`はshared sink-free `recognize_nud`が認識し、accept後にcutする。
- parenthesis内の各elementはcurrent-depth `Comma | RParen`をstop setとするflat
  `OperatorChain`としてparseし、outer chainのoperator useを内側へ持ち込まない。
- closing `)`後はcompleted `ParenthesizedExpression` primaryをouter `OperatorChain`の
  operand-complete stateへ戻す。
- speculative branchはRowan sinkへ書かず、commit後だけdirect CSTを一度emitする。
- parenthesis内trivia、delimiter scope、closing-delimiter recovery、`Recovered<T>`によるtotal continuation、
  one committed recovery node = one recovery diagnosticの原則を維持する。

変更するのは、parenthesis内部のcardinality、comma所有、surface node名、parser-side AST、
empty formのvalidity、およびそれらからsemantic formを決めるphase boundaryである。
この追補のuniform `Expression::Parenthesized` / `SyntaxKind::ParenthesizedExpression`とcomma-list shapeは
現行`crates/yu-syntax`へland済みである。ただし現行elementはfully-associated `Expression`であり、
flat `OperatorChain` elementへの移行は末尾追補の別implementation sliceとする。

### Core invariant

parenthesized expressionのCSTは、内側のsemantic contentからouter node kindを決めない。
parserが決めてよいのは、sourceにliteralに存在する次のsyntax factだけである。

- opening / closing parenthesisの有無とrange。
- expression elementの個数と各subtree。
- element間のcommaとterminal trailing commaの有無。
- それらの間にあるtrivia。
- malformed sourceに対する`Missing` / `Error`とrecovery boundary。

parserは「これはgroupingかtupleか」を判定しない。elementが0個、1個、2個以上のどれでも、
trailing commaがあってもなくても、outer CSTは常に
`SyntaxKind::ParenthesizedExpression`一種である。child countとterminal `Comma`の有無は
sourceに書かれた差であり、semantic node kindの選択ではない。

unit / grouping / tupleの解釈は、将来のtype inference / infer-side loweringだけが所有する。
`yu-syntax`はtype、tuple value、identity semanticsを所有せず、後段が判定に必要な
element列とtrailing-comma markerを欠落なく渡す。Yulang3のその後段はまだ実装されておらず、
本追補のimplementation scopeにも含めない。

### Grammar

valid sourceのgrammarを次で固定する。

```text
ParenthesizedExpression :=
    LParen G*
    [
        OperatorChain G*
        { Comma G* OperatorChain G* }
        [ Comma G* ]
    ]
    RParen
```

`G*`はemptyでもよい一回のmaximal `TriviaRun`で、`Whitespace` / `Newline` /
`LineComment` / `BlockComment`を含む。triviaと`Comma`は
`ParenthesizedExpression`直下へsource orderでemitし、list用またはtrivia用のwrapper nodeは作らない。

separatorとして認めるのはfixed punctuationの`Comma`だけである。newlineは`G*`としてdelimiter、
element、commaの間に存在できるが、newline自体を次elementのseparatorとは解釈しない。

### Parser-side ASTとCST shape

parser-side ASTはsemanticな`Grouped`をやめ、surface syntaxをそのまま表す。dynamic operatorを
precedence-neutralにする後続決定により、element typeはassociated `Expression`ではなくflat
`OperatorChain`になる。

```rust
pub(crate) enum PrimaryExpression<'source> {
    Parenthesized {
        elements: Vec<OperatorChain<'source>>,
        trailing_comma: Option<Range<usize>>,
        range: Range<usize>,
    },
    // other structural primary variants
}
```

`range`はopening `(`のstartからmatching `)`のendまでを持つ。
`trailing_comma`はterminal commaがsourceに存在するときだけそのexact rangeを`Some`で持ち、
存在しなければ`None`とする。lossless CST側では同じfactのauthorityはclosing `RParen`直前の
terminal `Comma` tokenである。AST fieldはsemantic tuple判定の結果ではなく、そのliteral tokenを
後段へ渡すsurface markerである。

CSTには`SyntaxKind::ParenthesizedExpression`を一つだけ置く。
`SyntaxKind::GroupedExpression`と、将来の`SyntaxKind::TupleExpression`をarityやtrailing commaで
選び分ける構成は禁止する。valid formの分類は次になる。

| source | `elements.len()` | `trailing_comma` | infer-side interpretation |
| --- | ---: | --- | --- |
| `()` | 0 | `None` | unit |
| `(a)` | 1 | `None` | grouping / identity |
| `(a,)` | 1 | `Some(comma_range)` | one-tuple |
| `(a,b)` | 2 | `None` | two-tuple |
| `(a,b,)` | 2 | `Some(comma_range)` | two-tuple |

表の右端はparser outputではない。parser / CSTは左三列のsurface factだけを作り、
type inference / infer-side loweringが次のruleを一箇所で適用する。

```text
elements.len() == 0
    => unit
elements.len() == 1 && trailing_comma.is_none()
    => grouping / identity
otherwise
    => tuple
```

したがって、`(a,)`はone-tupleであり、`(a)`と同じidentity expressionへcollapseしてはならない。

### Yulang2からの意図的なsemantic correction

Yulang2のparser自体は、このsurface invariantを保っていた。
`yulang2-oracle@a58eefc3:crates/parser/src/expr/core.rs:102-105`はprefix `(`を常に
`SyntaxKind::Paren`へ送り、`crates/parser/src/expr/group.rs:48-79`は同じnode内を
`ExprListMachine`でparseした。generic list loopはseparatorを`Separator > Comma`として保持し、
separator直後のclosing tokenも受理した
(`crates/parser/src/parse/mod.rs:25-77`)。したがって`(a)`と`(a,)`は同じouter `Paren`を持ち、
後者だけがliteralなterminal `Separator > Comma`を持っていた。

一方、Yulang2のinfer-side `lower_paren`は`Expr` childだけを収集し、0個をunit、1個をidentity、
2個以上をtupleへlowerした
(`yulang2-oracle@a58eefc3:crates/infer/src/lowering/expr/block_local.rs:7-26`)。
`Separator`を見なかったため、`(a,)`も`(a)`と同じ1-child identity caseへcollapseした。
これはYulang3が維持するcompatibilityではなく、surfaceに保存済みのtrailing commaをsemantic phaseが
捨てたYulang2のbugとして扱う。

Yulang3はこの点を意図的に修正する。parserはterminal commaを
`trailing_comma: Some(comma_range)`として後段へ伝え、infer-side interpretationは
「1 element + trailing commaあり」をone-tupleにする。この差は偶発的な出力変更ではなく、
`(a)`と`(a,)`のliteralなsource差をsemantic interpretationへ正しく接続するlanguage correctionである。

### Comma-only separator scope

Yulang2の`ExprListMachine::is_group_sep`は`Comma | Semicolon`を受け入れ、generic
`DelimitedListMachine`はindent条件を満たすnewlineもimplicit separatorとして扱った
(`yulang2-oracle@a58eefc3:crates/parser/src/expr/group.rs:72-79`、
`crates/parser/src/parse/mod.rs:21-23,41-49`)。

Yulang3の`ParenthesizedExpression`は、この挙動をそのまま移植しない。本追補でelement separatorとして
受理するのはcommaだけである。semicolon-separated formとimplicit-newline-separated formは
意図的にscope外とし、未対応をoversightやtemporary parser gapとして扱わない。
それらを将来追加する場合は、newlineがelement内trivia / ML application / outer statement boundaryの
どれに属するかを含め、別のdesign decisionとして明示する。本追補のcomma loopへ暗黙に混ぜない。

### Commit continuationとstop scope

direct CST continuationは次のcontrol flowを持つ。

```text
accept parenthesis NUD { open }; cut
start ParenthesizedExpression at the NUD checkpoint
emit LParen(open)
push ParenthesizedExpression delimiter scope
push StopSet { Comma, RightParenthesis }
scan and emit leading TriviaRun
if the next token is RParen:
    commit the valid zero-element form
else:
    parse or recover one flat OperatorChain until Comma | RightParenthesis
    loop:
        scan and emit TriviaRun
        if the next token is Comma:
            emit Comma
            scan and emit TriviaRun
            if the next token is RParen:
                record this Comma as trailing_comma and leave the loop
            parse or recover the next flat OperatorChain until Comma | RightParenthesis
            continue
        leave the loop
commit or recover RParen
pop the stop / delimiter scope on every Complete / Incomplete path
finish ParenthesizedExpression
return one completed primary to the outer OperatorChain's operand-complete state
```

`StopKind::Comma`は既存のstop vocabularyとoperator scannerの
`next_is_expression_stop`に存在する。parenthesized scopeは現在の
`RightParenthesis`だけのstop setを`Comma | RightParenthesis`へ広げる。
これにより各elementのflat chain parserはcurrent-depth commaをconsumeせずlist continuationへ返す。

commaはaccepted `(`後のcommitted list continuationが所有するfixed punctuationである。
commaの後ろがmatching `)`か次elementかという判定に、semantic ASTやsubtree rollbackは使わない。
matching closeのsink-free punctuation probeとshared NUD candidate probeだけで次のmandatory slotを決め、
commit済みCSTを巻き戻さない。

### Empty formとrecoveryの変更

element listはoptionalなので、`()`はvalid zero-element formであり、
`Missing(ExpectedSyntax::Expression)`を作らない。この点は直前のhistorical sectionの
mandatory-inner ruleと、そのruleを固定したcurrent test expectationをsupersedeする。

同じ理由により、`(`または`(`の後のtriviaでEOF / owner safe pointへ達した場合、欠けているmandatory
slotはclosing `)`だけである。zero-width `Missing(')')`を一件置き、expected expressionを同じrecordへ
unionしない。`header-full-diagnostic-identity`のopening parenthesis後にnewlineを挟んでEOFへ至るcaseは
引き続き`Missing @ 26..26`を一件だけ持つが、そのexpectationはclosing parenthesisだけになる。

一個以上のelementを開始した後のinvalid source、comma後のmissing element、mismatched close、
missing closeは、既決のmandatory-slot / closing-delimiter recoveryをlist ownershipへ適用する。
recovery後もaccepted parenthesis NUDはtotal continuationとしてnodeを必ずfinishし、outer body/valueが
同じsource positionへduplicate `Missing(expression)`を追加しない。

comma / `)`をboundaryとして見るのは、active embedded lexical regionがなく、current
`ParenthesizedExpression` delimiter depthにいるときだけである。string、heredoc、interpolation、
rule literal、quoted / block Yumark、comment、fence内のcommaやparenthesisをraw character searchで
separator / closeと判定しない。既決のoperator-independent lexical-region authorityとrollback対象の
`ParseLocal` scopeを共有し、parenthesized recovery専用の簡易quote counterを作らない。

### 既存architecture principleとの整合

- **rollback discipline:** opening `(`のrecognitionはsink-free、accept後はcut、list continuationは
  committedなfixed-punctuation loopとする。grammar subtreeの試行emit / rollbackを導入しない。
- **immutable operator table:** full parse前に一度構築した`OperatorTable`を全element parseで共有する。
  element境界ごとにtable / mapを作り直さず、commaをoperator entryとして追加しない。
- **BpVec-equivalent binding power:** body elementのrecognition / CST hierarchyではnumeric BPを読まない。
  BpVec相当のfull-fixity capabilityとjudge tableは維持し、comma stopはbinding powerではなく
  delimiter-local stop setで表す。numeric BPは後段associatorだけが使う。
- **oracle judge table:** prefix / nullfix / infix / suffixのcandidate selection、whitespace judge、
  longest-match fallbackは各elementで既存authorityをそのまま使う。element countやtrailing commaを
  operator judgeへ入力しない。
- **direct CST / no event buffer:** branch decision前にRowanへ書かず、commit後は
  `ParenthesizedExpression`一nodeへsource順で一度だけemitする。element列をCST event bufferへ貯めて
  grouping / tuple判定後にreplayする構成は禁止する。
- **lexical-region-aware recovery:** stop / delimiter / lexical-mode stackはinput checkpointと同時に
  rollbackされる`ParseLocal`が所有する。comma / close探索をgrammar-localなraw scanへ複製しない。

### Implementation boundary

この追補を実装するyu-syntax sliceは、parser-side AST / CST、flat `OperatorChain` element、comma loop、
stop scope、recovery、lossless fixtureだけを変更する。operator associationはdedicated pre-HIR associator、
unit / grouping / tuple classificationは後続のinfer-side lowering / inferenceが所有する。one-tupleのruntime表現、
formatter policyは変更しない。infer-side sliceはassociated `elements`と`trailing_comma`を受け取り、上で
固定したsemantic ruleを一箇所で実装する。

semicolon / implicit newline separator、record / list literal、call argument list、pattern / typeの
parenthesized formは本追補へ含めない。それぞれが同じsurface invariantを必要とする場合も、
このexpression nodeへ無名で統合せず、各grammar ownerのdesignとして扱う。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定、ユーザ承認済み
（2026-08-22、parenthesized expression-list CST / inference boundary追補案）。

## 追補: body内の未宣言 operator-shaped token

operator tableのどこにも一致entryを持たないoperator-shaped tokenがbodyに現れたとき、
専用のdiagnosticやoperator専用fallbackは定義しない。context-dependentな既存generic recoveryへ
委ねることを、意図した挙動として確認する。

left operandがまだないNUD位置では、`scan_operator`がtrieのlongest-matchからcandidateを得られず
`None`を返す（`scan/operator.rs:110,163`）。`recognize_nud`はその失敗を他のNUD alternativeへ
fall throughさせる（`grammar/expression.rs:282`）。left operandがある位置では、unmatched runは
generic expression recovery、またはrootのtrailing-input recoveryがそのcontextに応じて消費する。
前者のexpression-slot retryは`grammar/declaration.rs:817`にある。

この挙動は未宣言operatorを有効なoperatorとして扱う規則ではない。どのgeneric recovery pathが
発火するか、そのCST shapeとdiagnosticは既存のcontextごとのrecovery machineryが決める。ここで
新しいdiagnostic、recovery node、またはoperator-table外のtokenに対する特別扱いを追加しない。

著者: ユーザー確認済みの決定（Claude Sonnet 5 との会話、2026-08-22）。

## 追補案: dynamic operatorのprecedence-neutral surface chainとassociation境界

Status: Claude review / exact wordingのfinal sign-off待ち。

Date: 2026-08-22。

### Decision summary

Yulang3の`yu-syntax`は、dynamic prefix / infix / suffix operatorのnumeric binding powerを
CST hierarchyの決定に使わない。source-localなoperator chainは、同じoperator spellingとfixity role列を
持つ限り、headerまたはimported syntax dependencyのbinding-power数値だけが変わっても同じouter node kind、
同じparent / child relation、同じsource-order child列を持つ。

parserが確定するのはoperator spellingとprefix / infix / suffix / nullfixという**fixity role**である。
fixity roleは、現在位置がoperandを要求するNUD siteか、operand後のcontinuationを要求するLED siteか、
operator capability、前後trivia、後続value-start、delimiter / layout boundaryから決まるsyntax factなので、
oracle judge tableを使って`yu-syntax`が所有する。一方、prefixがどこまでをoperandに取るか、infixが左右の
どのsubexpressionを所有するか、suffixがどのleft expressionへ適用されるかはnumeric binding powerから
導かれるassociation factであり、CST node ownershipにはしない。

全direct dynamic expressionは、operatorが一個もないidentifier / integerだけのcaseを含め、
`SyntaxKind::OperatorChain`一種をouter surface nodeとして使う。prefix / infix / suffix / nullfix useは
role-specific child nodeとしてsource orderに並ぶが、application subtreeを作らない。

flat chainからprecedence-shaped expression treeを作るのは、`ParsedFile -> HirModule` transitionに属する
dedicated associator、またはそのassociatorを呼ぶHIR loweringである。これはtype inferenceではなく、
declared syntax factをHIRへ投影する前処理である。`yu-syntax`もtype inferenceもoperator associationの
第二authorityを持たない。

この設計はYulang2内部構造の復元ではない。`yulang2-oracle@a58eefc3`は
`crates/parser/src/expr/core.rs:31-38,128-150`と`expr/tail.rs:226-271`でPratt binding-power比較を行い、
stronger RHSをparser時にnested `Expr`へした。`crates/infer/src/lowering/expr/chain.rs:69-162`は
そのparser-shaped CSTをleft foldしただけで、deferred precedence passではない。Yulang3はこのhistorical
shapeと意図的に異なる、新しいsurface-CST boundaryを採用する。

### Supersession scope

本追補は、この文書の次のPratt-CST commitmentをsupersedeする。

- Decision summaryの「Yulang2のPratt / precedence climbingを維持する」というexpression paragraph。
- `yulang2-oracle`調査の`Expression parser`節にある「Yulang2のalgorithmを維持する」というYulang3側の結論。
  Yulang2のactual behaviorを記録するhistorical evidence自体は維持する。
- `Direct Rowan sink without parse-event buffering`節の、emitted leftを
  `start_node_at`で`InfixExpression` / `SuffixExpression`へ包むparagraph。
- `Recognition と commit continuation の境界`節のoutput-generic Pratt control、boxed application AST、
  `ParsedExpression`のleft-wrap checkpoint。
- `Pratt NUD / LED の probe / commit`節全体のminimum-BP rejection、recursive RHS parse、application node shape。
- `SyntaxKind vocabulary`の`PrefixExpression` / `InfixExpression` / `SuffixExpression` /
  `NullfixExpression`をsemantic application nodeとして使うexpression row。
- implementation slice / gate / testにあるPratt tree shape、binding-power reset、weak LEDをcallerへ返すことを
  CST acceptance条件にした箇所。
- parenthesized expression-list追補の`elements: Vec<Expression>`、elementを
  `BindingPower::scalar(i8::MIN)`でparseするcontrol、closing `)`後にoriginal minimumのLED loopへ戻す記述。

次はsupersedeしない。

- integrated character input、source-range authority、lossless CST、`green.to_string() == source`。
- sink-free candidate probe、accepted後のcut、direct sink、event buffer / replay禁止。
- immutable full-fixity `OperatorTable`、header/full parity、operator provenance。
- longest-match spelling、boundary、whitespace、value-startを使うoracle judge table。
- rollback-aware `ParseLocal`、stop / delimiter / lexical-region scope。
- mandatory-slot recovery、`Recovered<T>`、zero-width `Missing`、non-empty `Error`、
  one committed recovery node = one recovery diagnostic。

### Strong surface invariant

同じexpression source rangeと同じoperator spelling / selected fixity role列に対し、numeric binding powerだけが
異なる二つのvalid `SyntaxEnvironment`を与えたとき、次が一致しなければならない。

1. `OperatorChain`以下の`SyntaxKind`列。
2. nodeのparent / child relation。
3. token / triviaのsource-order ownership。
4. `Missing` / `Error`を含むparse recovery shapeとparse diagnostic。
5. parser-side surface ASTのvariant / item列 / source range。

異なってよいのは、後段associatorが作るapplication tree、そこから作るHIR hash、そのHIRを読むsemantic
diagnosticである。operator spelling、available fixity capability、visibilityが変わるcaseはscanner / judgeの
入力自体が変わるため、このinvariantの「BP-only」caseには含めない。

このinvariantは「parserが一切のgrammar decisionをしない」という意味ではない。delimiter、keyword、call、
field、index、ML argument boundary、operator fixity role、recovery safe pointは引き続きsyntax grammarが決める。
禁止するのは、numeric BP比較からsource-local CSTのapplication ownershipを作ることである。

### Surface grammar

dynamic operator部分のvalid grammarを次で固定する。`G*`はemptyでもよい一回のmaximal `TriviaRun`である。
operator use前後の`G*`がrole judgeのpre / post whitespace factになるが、CSTでは
`OperatorChain`直下のinter-item triviaとしてsource orderに置く。

```text
DirectExpression :=
    OperatorChain

OperatorChain :=
    OperandSlot
    {
        FixedPostfixContinuation
      | G* SuffixUse
      | G* InfixUse G* OperandSlot
      | MlApplicationContinuation
      | G* TypeAnnotationContinuation
    }
    [ G* TerminalOuterContinuation ]

OperandSlot :=
    { PrefixUse G* }
    Value

Value :=
    PrimaryHead
  | NullfixUse

FixedPostfixContinuation :=
    CallTail
  | IndexTail
  | FieldTail
  | ProjectionTail
  | PathTail

MlApplicationContinuation := MlArgumentSeparator MlArgument
MlArgument := OperatorChain under the ml_arg stop scope

TypeAnnotationContinuation := AsKw G* Type

TerminalOuterContinuation :=
    ColonApplicationTail
  | AssignmentTail
  | WithBodyTail

PrefixUse := accepted operator spelling with selected role Prefix
InfixUse  := accepted operator spelling with selected role Infix
SuffixUse := accepted operator spelling with selected role Suffix
NullfixUse := accepted operator spelling with selected role Nullfix
```

`OperatorChain`は最低一個の`OperandSlot`を要求する。`PrefixUse`は後続`Value`をCST childとして所有せず、
`InfixUse`もleft / right subtreeを所有せず、`SuffixUse`もleft subtreeを所有しない。上のBNFにある
`OperandSlot`はparser stateのmandatory slotを表すだけで、semantic application nodeではない。

`FixedPostfixContinuation`の各ruleはconstruct固有のadjacency / punctuation条件をgrammar内部に含む。
`MlArgumentSeparator`はML applicationを開始できるnon-empty whitespace / layout factであり、genericな
`G*`ではない。`TypeAnnotationContinuation`は後続dynamic continuationを許すが、
`TerminalOuterContinuation`はcurrent `OperatorChain`を必ず終了する。

role-specific useは次のnode kindを使う。

```text
SyntaxKind::OperatorChain
SyntaxKind::PrefixOperatorUse
SyntaxKind::InfixOperatorUse
SyntaxKind::SuffixOperatorUse
SyntaxKind::NullfixOperatorUse
SyntaxKind::CallTail
SyntaxKind::IndexTail
SyntaxKind::FieldTail
SyntaxKind::ProjectionTail
SyntaxKind::PathTail
SyntaxKind::MlArgument
SyntaxKind::TypeAnnotationTail
SyntaxKind::ColonApplicationTail
SyntaxKind::AssignmentTail
SyntaxKind::WithBodyTail
```

各operator-use nodeのnormal childはexact source rangeを持つ`SyntaxKind::Operator` token一個だけである。
leading / trailing triviaはoperator-use nodeへ押し込まず、最小の共通surface ownerである`OperatorChain`直下へ
置く。これによりoperator-use nodeのrangeやchildrenがoperand ownershipを暗示しない。operator token自体の
spellingとrole-specific node kindが、parserが確定したsurface factのauthorityになる。

structural continuation nodeもtargetとなるleft expressionをchildにしない。call / index tailはdelimiter内の
argument、field / projection / path tailはliteral punctuationとmandatory following slot、`MlArgument`は
nested flat `OperatorChain`、type annotationは`Type`、terminal tailはconstruct固有RHSだけを所有する。
targetは同じouter `OperatorChain`内でそのnodeより前にあるsource-order item列から後段が作る。

operatorのない`a`も次のshapeを持つ。

```text
OperatorChain
  IdentifierExpression "a"
```

たとえば`-a * b!`は、numeric BPに関係なく次のsource-order shapeを持つ。

```text
OperatorChain
  PrefixOperatorUse
    Operator "-"
  IdentifierExpression "a"
  InfixOperatorUse
    Operator "*"
  IdentifierExpression "b"
  SuffixOperatorUse
    Operator "!"
```

`a + b * c`の`+` / `*`のBPを入れ替えてもCSTは同じordered child列である。association結果だけが
`a + (b * c)`と`(a + b) * c`の間で変わる。

### `StructuralPrimary`とfixed structural tailの境界

numeric binding powerを使わず、literal punctuation、adjacency、keyword、whitespace / layoutから境界が
一意になるconstructも、dynamic operator useとsource順にinterleaveできるtailは同じflat
`OperatorChain`へ置く。ただしrole-specific dynamic operator nodeへ偽装しない。分類を次で固定する。

| construct | owner | BP-neutrality / shape rule |
| --- | --- | --- |
| identifier、number、string、rule literal、lambda、`if` / `case` / `catch`、brace / bracket form | `PrimaryHead` | construct固有starter / delimiterがnodeを決める。dynamic BPを読まない |
| `ParenthesizedExpression` | `PrimaryHead` | elementごとにflat `OperatorChain`を持つ。unit / grouping / tuple解釈は別phase |
| nullfix operator | `Value`としての`NullfixOperatorUse` | judgeがNullfix roleを確定するがoperand edgeを持たない |
| no-space C-style call `(...)`、index `[...]` | `CallTail` / `IndexTail` chain item | delimiterとadjacencyがtailを決める。targetはCST childにせず、source positionでflat chainへ置く |
| field / projection `.`、path `::` | corresponding fixed-postfix chain item | fixed punctuationとmandatory following slotを所有するがtarget edgeを持たない |
| ML application | `MlArgument` chain item | whitespace / layoutと既存`ml_arg` stop scopeでargument boundaryを決める。各argument内部はflat `OperatorChain` |
| type annotation `as Type` | non-terminal `TypeAnnotationTail` chain item | current pending dynamic segment全体をassociateした結果へ適用し、その後のchain continuationを許す |
| colon application `:`、assignment `=`、`with:` body | terminal chain item | current pending dynamic segment全体をassociateした結果へ適用し、construct固有RHSの後でchainを終了する |

tight structural head / tailは概念上次のlayerに属する。

```text
OperandSlot := { PrefixUse G* } (PrimaryHead | NullfixUse)
FixedPostfixContinuation := CallTail | IndexTail | FieldTail | ProjectionTail | PathTail
```

call / index / field / projection / pathはdynamic suffixとinterleaveできるため、target込みのleft-nested CSTには
しない。たとえば`a!()`でcallがtargetに取るassociated leftは`!`のBPと周囲のprefixによって変わり得るが、
CSTは常に`PrimaryHead("a"), SuffixUse("!"), CallTail("()")`の同じ列である。fixed tail nodeの内部にある
argument / field slot / delimiter shapeだけをconstruct grammarがnested CSTとして所有する。

ML applicationはまだcurrent `yu-syntax`に実装されていないため、whitespaceとnewlineのexact acceptance tableは
future ML-application addendumがoracle fixtureに基づいて固定する。ただしarchitecture decisionはopenに戻さない。
ML applicationをdynamic BP operatorとしてPratt treeへ入れず、outer chainにsource-orderの`MlArgument`を
一個ずつ置く。各argumentは既存`ml_arg` stop scopeで終わるnested flat `OperatorChain`であり、argument内の
prefix / infix / suffix associationはHIR側へdeferする。`f x y`を`f (x y)`へsemantic nestingする判断を
parserへ入れず、`PrimaryHead("f"), MlArgument("x"), MlArgument("y")`を保持し、fixed left-associative
application loweringはHIR側が行う。

`as` / `:` / `=` / `with:`はdynamic operator useではなく、既存通りdedicated keyword / punctuation
continuationである。`as`はouter-only association barrierとして、その直前までのpending dynamic segmentを
後段でassociateしてからannotationを適用し、同じflat chainのcontinuationを再開する。`:` / `=` / `with:`は
同じflush後にconstruct固有RHSを適用し、chainを終了する。`ColonApplicationTail`のexact RHS arityと
block ownershipは末尾のcolon-application追補で確定する。assignmentと`with:`のdetailは引き続き
各grammar familyのaddendumが所有する。本追補が固定するのは、numeric operator BPをparserが読んで境界を
決めたり、dynamic operator-use nodeへ偽装したりしないことである。pipeline `|`のようにoperator tableへ
登録されるformはfixed structural tailではなく、普通の`InfixOperatorUse`としてflat chainへ入る。

### Parser-side surface AST

test projectionと将来のsyntax-to-HIR handoffに使うparser-side valueもprecedence-neutralにする。
current `Expression::{PrefixApplication,InfixApplication,SuffixApplication,NullfixApplication}`は削除対象であり、
次のshapeへ置き換える。

```rust
pub(crate) struct OperatorChain<'source> {
    items: Vec<OperatorChainItem<'source>>,
    range: Range<usize>,
}

pub(crate) enum OperatorChainItem<'source> {
    PrefixUse(OperatorUse<'source>),
    Primary(PrimaryExpression<'source>),
    NullfixUse(OperatorUse<'source>),
    InfixUse(OperatorUse<'source>),
    SuffixUse(OperatorUse<'source>),
    FixedPostfix(FixedPostfixTail<'source>),
    MlArgument {
        argument: Box<OperatorChain<'source>>,
        range: Range<usize>,
    },
    TypeAnnotation(TypeAnnotationTail<'source>),
    TerminalOuter(TerminalOuterTail<'source>),
    MissingOperand { range: Range<usize> },
    Error { range: Range<usize> },
}

pub(crate) struct OperatorUse<'source> {
    text: &'source str,
    range: Range<usize>,
    role: OperatorRole,
}

pub(crate) enum OperatorRole {
    Prefix,
    Infix,
    Suffix,
    Nullfix,
}

pub(crate) enum FixedPostfixTail<'source> {
    Call { group: CallArguments<'source>, range: Range<usize> },
    Index { group: IndexArguments<'source>, range: Range<usize> },
    Field { name: WordSpan<'source>, range: Range<usize> },
    Projection { body: ProjectionSyntax<'source>, range: Range<usize> },
    Path { segment: WordSpan<'source>, range: Range<usize> },
}

pub(crate) struct TypeAnnotationTail<'source> {
    ty: TypeExpression<'source>,
    range: Range<usize>,
}

pub(crate) enum TerminalOuterTail<'source> {
    ColonApplication { rhs: ColonApplicationRhs<'source>, range: Range<usize> },
    Assignment { rhs: AssignmentRhs<'source>, range: Range<usize> },
    WithBody { body: WithBody<'source>, range: Range<usize> },
}

pub(crate) enum PrimaryExpression<'source> {
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Parenthesized {
        elements: Vec<OperatorChain<'source>>,
        trailing_comma: Option<Range<usize>>,
        range: Range<usize>,
    },
    Structural(StructuralHead<'source>),
}
```

`CallArguments` / `IndexArguments` / `ProjectionSyntax` / type / terminal RHSの内部shapeは各construct grammarの
authorityであり、このsketchはその既存またはfuture typed valueを参照する。concrete Rust module split、
`Box` / `Arc` / small-vector choice、private field accessorはimplementation detailとして調整してよい。
固定するのはordered item列、上のchain-item variant、parenthesized / ML argumentが`OperatorChain`であること、
および全continuation variantがtarget application edgeを持たないことである。

`OperatorUse`はnumeric binding power、parse-session-local table index、生pointerを保存しない。
それらを保存するとBP-only environment changeでsurface AST valueまでinvalidateし、stale entryを別revisionで
参照できるためである。associatorは`OperatorUse.text + role`と`ParsedFile`に対応するexact
`OperatorAssociationKey`からcanonical operator definitionを解決する。必要なら将来stable operator-syntax keyを
追加できるが、そのkeyもnumeric BP valueやoperand ownershipをsurface nodeへ複製してはならない。

lossless CSTがtriviaとrecovery byteのauthorityであり、parser-side ASTはそれらを重複保持しない。
`MissingOperand` / `Error`はassociationをtotalにするtyped surface projectionで、CSTのzero-width `Missing` /
non-empty `Error`と同じrangeを参照する。ASTを作らないproduction pathでも、HIR loweringがCST child列から
同じordered item streamを一回だけprojectできなければならない。

### Role recognitionとparse control

normal valid-source continuationを次で固定する。

```text
start OperatorChain
expect OperandSlot

while expecting OperandSlot:
    consume zero or more accepted PrefixUse values in source order
    accept one PrimaryHead or NullfixUse as Value
    if Value is absent, run mandatory operand-slot recovery

while an operand is complete:
    probe one continuation at LED site without reading numeric BP
    if a fixed call / index / field / projection / path tail is accepted:
        emit its target-free tail node and remain in operand-complete state
    if an ML argument boundary is accepted:
        parse one nested flat OperatorChain under ml_arg scope,
        emit MlArgument, and remain in operand-complete state
    if TypeAnnotationContinuation is accepted:
        emit TypeAnnotationTail and remain in operand-complete state
    if TerminalOuterContinuation is accepted:
        emit its target-free tail with construct-specific RHS and finish the chain
    if Suffix role is accepted:
        emit SuffixOperatorUse and remain in operand-complete state
    if Infix role is accepted:
        emit InfixOperatorUse and return to OperandSlot state
    if no dynamic operator role is accepted:
        stop before the unconsumed owner boundary / outer structural tail

finish OperatorChain
```

`probe_nud` / `probe_led`というsite名は、operand expected / operand completeというjudge contextの名前として
残してよい。削除するのは`minimum: &BindingPower` parameter、BP不足によるcandidate rejection、recursive
`parse_expression_bp`、lower-precedence LEDのrollback / return、left-wrap checkpointである。

fixed punctuation / keyword tail、ML argument、dynamic LED roleのcandidateは、既存oracleの
call/path-sensitive ordering、whitespace / value-start rule、mode / stop scopeを一つのcontinuation judgeで
裁定する。operator scannerの`is_call_or_path_sensitive` conditionを削除してoperator spellingが`(`/`:`を
飲み込む形へ変えない。accepted structural continuationとoperator useのどちらも、commit前はsink-freeであり、
role / punctuationが確定してからだけdirect sinkへ一度emitする。

### Dangling / malformed operator recovery

operator chainは、上のmandatory-slot共通規則を専用の第二recovery systemなしで適用する。
operand slotのtyped expectationは既存の
`GrammarRole::Expression(ExpressionRole::Nud)`と`ExpectedSyntax::Expression`を使う。
chain-local candidateはprefix / nullfix / `PrimaryHead`であり、owner safe pointはactive stop set、matching
delimiter、outer structural-tail introducer、statement separator / root boundary、EOFである。

normal oracle judgeはvalid sourceのrole authorityのまま維持する。value-start不在のためnormal judgeが
infix / prefix candidateを拒否した後、recoveryだけが同じcanonical trie / boundary scannerを使って
**一意なdangling role**を認識してよい。これは次を全て満たす場合に限定する。

1. current parser stateがinfixまたはprefix operandを要求するsiteを一意に定める。
2. longest accepted spellingがtable上でそのrole capabilityを持つ。
3. normal judgeが別のvalid role、特にsuffixまたはnullfixを選んでいない。
4. spelling後がowner safe point、EOF、またはoperand recoveryが同期できるinvalid regionである。
5. 複数roleが残る場合はroleを推測せず、既存generic `Error` recoveryへ渡す。

recovery-only probeもsink-freeであり、numeric BPを読まない。roleが一意ならoperator-use nodeとtokenをcommitし、
直後のoperand mandatory slotに既存`Missing` / `Error` ruleを適用する。unknown spellingは直前の
「body内の未宣言 operator-shaped token」追補通りgeneric `Error`であり、role-specific use nodeを作らない。

代表caseを次で固定する。

| source situation | CST / recovery |
| --- | --- |
| `a <infix> EOF` | unique `InfixOperatorUse`を保持し、EOFにzero-width `MissingOperand`一件を置く |
| `<prefix> EOF` | unique `PrefixOperatorUse`を保持し、EOFにzero-width `MissingOperand`一件を置く |
| `a <infix> )` inside parenthesis | infix use後、`)`直前に`MissingOperand`を置き、`)`はparenthesized ownerへ残す |
| `a <infix> <operator> b`で二個目がvalid prefix | 二個目を`PrefixOperatorUse`としてnormal parseし、errorにしない |
| 同じ形で二個目がNUD roleを持たない | 次のNUD candidate `b`直前までを一個のnon-empty `Error`にし、同じoperand slotを`b`からretryする |
| invalid runがowner safe pointまで続く | invalid runの`Error`をrecovered operand sentinelとして使い、同じcauseへ追加の`Missing`を重ねない |
| suffixが連続する | judgeが各suffix roleをacceptする限りsource orderの`SuffixOperatorUse`列としてvalid |
| undeclared operator-shaped run | roleを捏造せず、context既存のgeneric `Error` / trailing-input recovery |

一個のinvalid runをbyteごとの複数`Error`へ分割しない。candidate retryが成功した場合、先行`Error`は
source-preservation itemであってoperandではなく、後続primaryがoperand slotを満たす。candidateなしで
safe pointへ到達した場合は、その`Error`自体をassociator用error operand sentinelとして扱い、同じ位置へ
第二のabsence diagnosticを作らない。source byteを持たない純粋なabsenceだけが`MissingOperand`になる。

accepted infix / prefix後のrecoveryはchain continuationを`Option::None`でabortしない。
`Recovered<OperatorChain>`としてnodeを必ず閉じ、callerが同じpositionへbinding value / operator bodyの
duplicate `Missing(expression)`を追加しない。`Missing` / `Error`一nodeにつき一committed recovery record、
一parse diagnosticという既存bijectionを維持する。

fixed structural continuationも同じcommit contractに従う。call open、index open、field / path punctuation、
`as`、`:`、`=`、`with:`などのconstruct introducerをacceptした後はcutし、argument、name、type、RHS、closeの
mandatory slotをそのconstructの既存`Missing` / `Error` ruleで回復する。malformed tailをdynamic operatorへ
reinterpretしてbranch rollbackせず、targetとなるpreceding item列へsynthetic application edgeも追加しない。
`MlArgumentSeparator`をcommitした後にargument headがないcaseも一個のmandatory operand recoveryとし、
outer chainを同じsource位置から二重retryしない。

### Association phase contract

association ownerは`yu-hir`のsyntax-to-HIR lowering、または`yu-hir`が唯一呼ぶdedicated pre-HIR moduleとする。
public phase boundaryは概念上次になる。

```text
ParsedFile + exact OperatorAssociationEnvironment
    -> associate_operator_chains
    -> HirModule containing precedence-shaped applications
    -> type inference / solving
```

associatorは各`OperatorChain`をsource orderで一回読み、prefix right BP、infix left / right BP、suffix left BPを
canonical tableから引き、vector-valued lexicographic comparisonでapplication treeを作る。同じpassが
target-free structural continuationもassociated HIR operationへ変換する。recursive Pratt over the flat sequence
でもoperator stackでもよいが、次のobservable contractを満たす。

- 同じflat item列と同じassociation environmentからdeterministicに同じtreeを作る。
- prefix / infix / suffix全roleを一つのassociation authorityで扱う。infixだけを後段化しない。
- call / index / field / projection / pathと`MlArgument`は、dynamic minimumに関係なくcurrent association
  cursorでacceptされるreserved structural postfixとして扱う。これは全dynamic BPより大きい数値をtableへ
  捏造する意味ではなく、grammar-fixed continuationをdynamic comparisonより先に処理するruleである。
- `TypeAnnotationTail`ではその直前までのpending dynamic segmentを全てreduceし、annotationを適用した結果を
  次continuationのleft seedにする。terminal outer tailも同じreduce後のleftへ適用し、chainを終了する。
- nested `MlArgument` chainを先にassociateし、outer leftへsource orderでfixed left applicationする。
  `f x y`は`(f x) y`になるが、そのnestingをsurface CSTへ書き戻さない。
- `OperatorUse`のsource rangeをassociated applicationとHIR provenanceへ直接渡し、CSTを後からrange探索しない。
- `MissingOperand` / operand-position `Error`にはtyped error expressionを一個対応させ、全itemをconsumeして
  total resultを返す。
- recovery noiseの`Error`はsource order / provenanceへ残すが、後続retry operandと二重にoperand化しない。
- parserがすでに発行したrecovery diagnosticを再発行せず、同じmalformed sourceからduplicate syntax
  diagnosticを作らない。
- operator entryがexact environmentで解決不能なcaseを型推論のunknown operatorへ偽装しない。
  revision/key mismatchはcompiler invariant failure、既存syntax recovery itemはerror expressionとして扱う。
- association resultをCSTへ書き戻さず、green treeやsurface ASTのparent / child relationをmutationしない。

BindingPowerはtypeではなくdeclared syntax factなので、type inferenceがassociationを選ぶ余地はない。
overload resolution、operator value identity、result type、lazy application semanticsはassociation後のHIR /
inferenceが扱うが、tree shapeは`OperatorAssociationEnvironment`だけで確定する。

### Parenthesized-expression reconciliation

preceding `parenthesized expression-listのsurface CSTと推論境界`追補のsemantic decisionは維持し、
element representationだけを次へ置き換える。

```text
ParenthesizedExpression :=
    LParen G*
    [
        OperatorChain G*
        { Comma G* OperatorChain G* }
        [ Comma G* ]
    ]
    RParen
```

parser-side primary shapeは次になる。

```rust
PrimaryExpression::Parenthesized {
    elements: Vec<OperatorChain<'source>>,
    trailing_comma: Option<Range<usize>>,
    range: Range<usize>,
}
```

各elementはcurrent `ParenthesizedExpression` scopeの`StopSet { Comma, RightParenthesis }`までparseする。
「inner minimumを`i8::MIN`へresetする」というoperationは存在しない。comma / closeによるliteral boundaryが
flat chainを止める。closing `)`後、completed parenthesized primaryを同じouter `OperatorChain`の
operand-complete stateへ返し、suffix / infix useをsource orderで続ける。

`()`、`(a)`、`(a,)`、`(a,b)`、`(a,b,)`のelement count / trailing-comma table、comma-only scope、
uniform `SyntaxKind::ParenthesizedExpression`、`(a,)`をone-tupleにするcorrectionは変更しない。
downstream orderは次である。

1. 各`OperatorChain`をHIR associatorがprecedence-shaped expressionへ変換する。
2. parenthesized formはassociated element列とtrailing-comma markerを保持する。
3. type inference / infer-side loweringが0 elementをunit、1 elementかつcommaなしをgrouping / identity、
   それ以外をtupleと解釈する。

operator associationはunit / grouping / tuple classificationを行わず、parenthesized inferenceはoperator BPを
読まない。二つのdeferred decisionを一phaseへ混ぜない。

current implementation testのうち、parenthesized elementが`Expression::InfixApplication`であること、
`BindingPower::scalar(i8::MIN)`へのreset、closing後にPratt LED loopへ戻ることをassertするcaseは、
flat child列と後段association resultを別々にassertするtestへ書き換える。uniform node、comma、trivia、
delimiter recovery、lossless rangeのtestは維持する。

### Incremental invalidation split

`docs/yulang3-architecture.md` §7.1の
`parse(FileId, source_hash, syntax_environment_hash)`と「operator name / fixity / binding power / visibilityで
importer parseをinvalidateする」表は、本追補に合わせて将来二種類のkeyへ分割する。

```text
OperatorRecognitionKey includes:
    available operator spelling
    prefix / infix / suffix / nullfix capability presence
    visibility / import selection needed to determine availability
    boundary / judge-table-relevant syntax version

OperatorAssociationKey includes:
    OperatorRecognitionKey identity
    numeric prefix right BP
    numeric infix left / right BP
    numeric suffix left BP
    association-rule schema version
```

source textまたは`OperatorRecognitionKey`が変わればsurface parseをinvalidateする。
`OperatorRecognitionKey`が同じで`OperatorAssociationKey`のnumeric BPだけが変わる場合、unchanged importerの
green CSTとparse diagnosticは再利用し、association / HIR以降だけをinvalidateする。changed provider自身は
header sourceが変わるため通常通りheader / full parse対象になり得る。

現行`ParsedFile.syntax_environment: SyntaxEnvironmentKey`を二fieldへ直ちに分割するか、compiler queryが
recognition projectionを別hashとして持つかはincremental implementation sliceが決めてよい。ただし
BP-only changeをsurface CST rebuildのsemantic requirementとして扱わないこと、associatorが必ず
`ParsedFile`と同じrevisionに対応するassociation keyを見ることはcontractである。

operator bodyだけのchange、semantic public interfaceだけのchange、persistent cache policyは既存§7.1の
invalidation ruleを変更しない。本追補はoperator syntax environment内のrecognition factとassociation factを
分離するだけで、fine-grained owner schedulerやpersistent parse cacheを先行導入しない。

### Existing architecture principlesとの整合

- **rollback discipline:** longest spelling、boundary、whitespace、value-start、fixity roleのprobeだけを
  rollback可能にする。accepted useとrecovery-only unique dangling roleはcut後にsource orderで一度emitする。
  BP不足によるLED rollbackとrecursive subtree rollbackはなくなる。
- **immutable operator table:** full parse前にcompileしたfull-fixity tableをmutationしない。parserはspelling /
  capability / role selectionだけを読み、associatorは同じrevisionのnumeric BPを読む。expressionごとのtable
  rebuildやCST再走査を置かない。
- **BpVec / BindingPower:** vector representation、header parsing、validation、provenanceは維持する。
  body `OperatorChain`のrecognition / CST hierarchyには使わず、association時のordering authorityとして使う。
- **oracle judge table:** NUD / LEDというsite distinctionはoperand expected / operand completeのrole judgeとして
  維持する。fixed structural continuation / ML argumentとの既存call/path-sensitive orderingも同じjudge
  authorityに残す。dynamic judge resultをCST role nodeへ記録するが、judge後にminimum BP filterをかけない。
- **direct CST / no event buffer:** `OperatorChain`を開始した後、primary、operator-use、structural continuation、
  trivia、recovery nodeをsource orderで即時emitする。left wrap、forward parent、event replay、flat itemの
  一時CST bufferは不要である。
- **lexical-region-aware recovery:** operator / delimiter / outer-tail safe pointはactive lexical-region、delimiter、
  stop-set scopeを共有する。string、comment、heredoc、interpolation、rule literal、Yumark、fence内のoperator-like
  textをchain itemやrecovery boundaryへ誤分類するraw scanを作らない。
- **single authority:** parser-side surface ASTとproduction CSTは同じrole recognition / chain continuationから
  同時投影する。association testのために第二のPratt parserを`yu-syntax`へ残さない。

### Implementation boundary and required gates

本追補の最初のimplementation sliceは`yu-syntax`のsurface grammar / CST / parser-side AST / recovery / testを
変更する。HIR associatorは別sliceだが、flat shapeをlandする前にそのinput contractとfixture expected treeを
固定する。current Pratt pathをlong-lived feature flag / fallbackとして残さず、production expression authorityは
一つにする。短命なtest-only differential prototypeは許すがpublic parse productへ二shapeを出さない。

yu-syntax implementation gateを次で固定する。

1. identifier-onlyとfixed-tail formを含む全direct expressionが一つの`OperatorChain` nodeを持つ。
2. prefix / infix / suffix / nullfix useがrole-specific node + exact `Operator` tokenとしてsource orderに並び、
   application childを持たない。
3. call / index / field / projection / path / ML argument / type annotation / terminal outer tailがtarget-free
   chain itemとしてdynamic useとsource orderに並び、nested argument / RHSだけを所有する。
4. 同一source / spelling / capabilityに対してnumeric BPだけを変えた二tableで、green tree、surface AST、
   recovery record、parse diagnosticがexact一致する。
5. 同じflat chainに対するassociation fixtureはBP変更でexpected treeが変わり、parse fixtureとは別ownerになる。
6. prefix extentを変えるfixture、mixed infix precedence、left / right associativity、suffix precedenceを全て含め、
   yu-syntax側では同じflat shape、associator側では正しいtreeを固定する。
7. `a!()`、`-a!()`、`a + b(x)`、`f x y`、`a + b as T + c`を含むstructural/dynamic interleaveで、
   flat source-order shapeとreserved structural association ruleを別々に固定する。
8. `+!a` / `a+!b` longest-candidate fixtureはoracle judgeとrole列を維持し、tree assertionだけをassociatorへ移す。
9. `a <infix> EOF`、`<prefix> EOF`、parenthesis close前のdangling infix、valid second prefix、invalid
   consecutive operator、undeclared operator-shaped runを上のrecovery table通り固定する。
10. all recovery caseで`Missing`はzero-width、`Error`はnon-empty、node / diagnosticが一対一、owner boundaryを
   consumeせず、chain / parenthesized / statement nodeがbalancedに閉じる。
11. `ParenthesizedExpression.elements`はflat chainで、`()`, `(a)`, `(a,)`, `(a,b)`, `(a,b,)`のuniform node /
   comma / trailing marker / inference classification contractを維持する。
12. dynamic operator parsingで`start_node_at`によるapplication wrapがなく、candidate probe中のsink callは0、
    commit後のrange coverageはgap / overlap / duplicateなし、`green.to_string() == source`である。
13. binding valueとoperator definition bodyが同じflat chain authorityを使い、AST-only / direct-CST-onlyの
    grammar divergenceを作らない。
14. source-wide token/event buffer、parse後CST replay、parse中table mutation、BP-driven subtree recursion、
    CSTからBP association用rangeを再探索する処理がない。

HIR association sliceのgateを次で固定する。

1. Yulang2 standard operator tableとcanonical yulang3 fixtureに対し、valid expressionのintended precedence /
   associativity treeを作る。
2. prefix / infix / suffixを同じauthorityでassociateし、nullfixをvalueとして扱う。fixed structural postfix、
   ML argument、type annotation barrier、terminal outer tailも上のreserved ruleで同じordered passがlowerする。
3. `MissingOperand` / `Error`を含む全flat fixtureでpanic / hang / unconsumed itemがなく、deterministic error HIRを返す。
4. parser recovery diagnosticを複製せず、operator source rangeをHIR provenanceへ一回だけ渡す。
5. BP-only environment changeでsurface CSTを再parseせずassociation / HIRだけを再計算した結果が、clean full
   parse + associationと一致する。

### Closed decisions and remaining provisional detail

本追補のimplementation directionをblockするopen questionはない。次は確定である。

- strong BP-neutral CST invariant。
- prefix / infix / suffix全てのflat化とnullfix roleのsurface保存。
- role-specific operator-use node、numeric BP / operand edgeを持たないsurface AST。
- HIR-side single associator、type inferenceからの分離。
- mandatory-slot recoveryとtotal error association。
- BP-only invalidationをassociation / HIR以降へ限定するkey split。
- parenthesized elementを`Vec<OperatorChain>`にするreconciliation。

ML applicationのexact whitespace / newline acceptance tableだけは、current `yu-syntax`に未実装なので
future construct-specific addendumでoracle fixtureとともに具体化する。そのaddendumが選べるのは
`MlArgument`のargument boundary / trivia ownership / recovery safe pointであり、dynamic numeric BPで
CST application treeを作る案へ戻すことはできない。colon applicationのdetailは直後の追補で確定済みである。
call / field / index / assignment / `with` / `as`は各constructのfuture recovery detailを追加できるが、
本追補のBP-neutral layer分類を変更しない。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定、ユーザ承認済み
（2026-08-22、precedence-neutral dynamic operator chain / association boundary追補案）。

## 追補案: lone `:`によるcolon applicationのsurface grammarとblock境界

Status: Claude review / exact wordingのfinal sign-off待ち。

Separator-scope status: superseded。`InlineColonArguments`のcomma-only loopとouter-comma-only ownership判定は、末尾の
「layout-aware comma-or-newline delimited sequence」追補へ置き換える。colon tail / inline-vs-indented / CST / ASTの他の決定は維持する。

Date: 2026-08-22。

### Decision summary

Yulang3のgeneric colon applicationは、precedence-neutral chain追補が予約した
`TerminalOuterContinuation::ColonApplicationTail`を次の一productionとして実体化する。

```text
ColonApplication := completed OperatorChainPrefix ":"
                    (InlineExpressionList | IndentedStatementBlock)
```

RHSはYulang2と同じく、one-or-moreのcomma-separated inline expression listとindented statement blockの
両方を最初のimplementation sliceから採用する。inline-onlyにもsingle-expression-onlyにも狭めない。
colonの主要な設計目的は、Python-likeなblock introductionとHaskell-likeなlow-parenthesis applicationを
一つのsurface formへ接続することだからである
(`yulang2-oracle@a58eefc3:notes/design/old-zenn-yulang.md:57,203-215`)。block branchを後回しにすると
`ColonApplicationRhs`、CST child shape、layout recoveryを後で作り直すことになり、foundational tailの
小さいsliceにはならない。

Yulang2のactual parserも、outermost tailのlone colonを`ApplyColon`としてcommitし
(`crates/parser/src/expr/tail.rs:115-137`)、RHSをindent blockまたはinline comma loopへ分けていた
(`expr/tail.rs:304-349`)。fixtureは`f: x + y`、`f: x, y + z`、`f:\n  x\n  y`をそれぞれ固定する
(`crates/parser/tests/expr_grammar.rs:1041-1089,1295-1313`)。Yulang3はそのsurface capabilityを維持するが、
RHS expressionはassociated Pratt treeではなくflat `OperatorChain`として保存する。

parserが決めるのは、lone `:` tokenのownership、inline / indentedというliteral layout branch、inline argument
countとcomma ownership、block statement boundary、recovery rangeだけである。preceding chainをどのapplication
treeへassociateするか、colon-applied bodyをordinary call sugar、block argument、またはconstruct-specific
operationのどれとしてHIRへlowerするかは`yu-syntax`の責務ではない。

### Scope boundary: generic colon applicationだけを所有する

Yulang2にはlone `:`を使うgrammar familyが多数あるが、一個のshared "colon clause" productionはない。
本追補が所有するのは、completed expressionのLED-continuation siteに現れるgeneric colon applicationだけである。
`if` conditionの終端、declaration headの終端、pattern / type内部など、active ownerがcolonを予約した位置では
generic tailをprobeしない。

このroutingを型付きにするため、stop vocabularyへ`StopKind::Colon`を追加する。construct-specific parserは
自分のcolonを読む範囲でこのstopをpushし、flat chain parserはcolonをconsumeせずownerへ返す。
stopがなく、`ml_arg` scopeでもなく、operand-complete stateにいる場合だけ`ColonApplicationTail`候補になる。
`::`はfixed punctuation scannerがlone `:`より先にlongest matchするため、path separatorをcolon applicationへ
分割しない。

### Valid grammar

`G0`はphysical newlineを含まないmaximal trivia run、`G*`はnewlineを含み得るmaximal trivia runである。
`Statement`はroot / brace bodyと同じcanonical statement grammarを指し、colon専用statement subsetを作らない。

```text
DirectExpression := OperatorChain

OperatorChain :=
    OperandSlot
    {
        FixedPostfixContinuation
      | G* SuffixUse
      | G* InfixUse G* OperandSlot
      | MlApplicationContinuation
      | G* TypeAnnotationContinuation
    }
    [ G* TerminalOuterContinuation ]

TerminalOuterContinuation :=
    ColonApplicationTail
  | AssignmentTail
  | WithBodyTail

ColonApplicationTail :=
    Colon G0 InlineColonArguments
  | Colon IndentedStatementBlock

InlineColonArguments :=
    OperatorChain
    { G* Comma G* OperatorChain }

IndentedStatementBlock :=
    BlockOpeningTrivia
    Statement
    { BlockStatementSeparator Statement }
    [ Semicolon ]

Colon := the lone fixed punctuation token ":"
```

BNFのinline comma loopは、incoming ownerがcurrent-depth commaを予約していない場合のshapeである。
`InlineColonArguments`は最低一argumentを要求し、terminal trailing commaをvalid formとして認めない。
semicolonはinline argument separatorではない。

colon前の`G*`にはordinary LED-continuation layout ruleを適用する。physical newline後のcolonは、そのlineの
indentがcurrent expression baseより深いcontinuation lineである場合だけ同じchainへ属する。equal / lower
indentのnewlineではchainをcolon前で終了し、colonを次ownerへ残す。post-colon blockの`base_indent`は
colon tokenのvisual columnではなく、引き続きそのcurrent expression baseである。

colon直後のtriviaにphysical newlineがなければinline branchだけを試す。physical newlineがあればinline branchへ
戻らず、indent ruleを満たすときだけindented branchになる。したがって`f:\n  x`をsingle inline expressionが
偶然newline越しに始まったcaseとして扱わない。

### IndentedStatementBlockのtriggerとlayout ownership

colonをrecognizeした時点、post-colon triviaを読む前に、current expression / statement ownerの
`base_indent`をsnapshotする。post-colon triviaが一個以上のphysical newlineを含み、そのtrivia後のlineの
indentation column `block_indent`が`base_indent`よりstrictly greaterなら`IndentedStatementBlock`を開始する。

```text
has_physical_newline(post_colon_trivia)
&& block_indent > base_indent
    => IndentedStatementBlock
```

これはYulang2 specのtriggerと同じである
(`yulang2-oracle@a58eefc3:spec/2026-06-06-syntax-design.md:195-199`)。blockは
`block_indent`未満の次lineで終了し、同じindent以上のlineをcanonical statement parserへ渡す。各statement
内部のcontinuation / nested layoutはそのstatement grammarが所有し、colon block scannerがraw line textを
statementへ分割しない。

`base_indent`はpost-colon triviaをscanした後の`LineState.line_indent`から逆算しない。active
`IndentationBaseline`のcolumnを使い、rootにframeがなければ0とする。colon continuationは判定中に
`IndentationBaselineKind::Introducer { column: base_indent }`相当のscopeを持ち、block accept後は
`IndentationBaselineKind::Block { column: block_indent }`相当のframeをpushする。実際のenumは既存通り
kindとcolumnを別fieldに持ってよい。全frame、`inline = false`、`ml_arg = false`、stop set変更は
Complete / Incompleteの全pathでpopし、probe rejectionではinputと一緒にrollbackする。

current `yu-syntax`はlayout grammarを持たないわけではないが、block continuationはまだ完成していない。
`ParseLocal`にはrollback-awareな`LineState`、`indentation_baselines`、`inline`、`ml_arg`があり
(`crates/yu-syntax/src/session.rs:83-196,306-340`)、trivia scannerはnewline後の`line_indent`を更新する
(`scan/trivia.rs:206-214`)。operator value-start judgeもactive baselineより深いnewlineだけを継続として認める
(`scan/operator.rs:184-233`)。一方、production `IndentedStatementBlock` nodeとstatement-loop grammarは
まだ存在せず、current root statement introもuse / binding / operator definitionに限られる
(`grammar/declaration.rs:68-72,217-243`)。本追補はinline-onlyへ縮めず、最初のcolon implementation sliceに、
この既存stateを使う最小のreusable indented-statement continuationとordinary expression-statement entryを
含める。他のcontrol / declaration colon formを同時に実装する意味ではない。

`BlockOpeningTrivia`はcolon後のnewline、blank line、comment、accepted first statementまでのindent triviaを
losslessに持つ。sink-free probeでblock branchを確定してから`IndentedStatementBlock`を開始し、そのtriviaを
blockの先頭childとして一度emitする。block内のinter-statement triviaもblock直下に置く。dedentを示す
boundary-leading triviaはconsumeせずouter ownerへ返す。

`BlockStatementSeparator`はcanonical statement loopと同じphysical newlineまたはexplicit semicolonである。
newlineはlossless triviaとして保持し、sourceにないseparator tokenを合成しない。semicolonはliteral
`Semicolon` tokenをblockが所有し、terminal semicolonもvalidとする。より深いlineが前statementのcontinuationか次statement starterかは
canonical statement / expression grammarが判定し、indent scannerだけでsynthetic siblingを作らない。

### Inline comma ownership

inline argument listのcomma ownershipはinner-winsではなく、既存ownerを優先する。

1. incoming active `StopSet`が`StopKind::Comma`を含まない場合、colon tailがlocal comma stopをpushし、
   `OperatorChain (Comma OperatorChain)*`を所有する。
2. incoming active `StopSet`がすでに`StopKind::Comma`を含む場合、そのcommaはparenthesized / brace / callなど
   outer list ownerのseparatorである。colon tailは一argumentだけをparseしてcomma直前で終了し、commaを
   consumeしない。
3. colon tail自身がcommaを所有するcaseでcommaをconsumeした後は、次argumentがmandatoryである。
   trailing comma markerは持たない。

これはYulang2の`parse_apply_colon_inline_args`がincoming comma stopを検査し、outer commaがない場合だけ
local separator loopを有効にしたruleを明文化したものである
(`yulang2-oracle@a58eefc3:crates/parser/src/expr/tail.rs:322-349`)。

したがってrootの`f: x, y`は二argument colon applicationである。一方、`(f: x, y)`はparenthesized listの
二element、`f: x`と`y`であり、`{x: 1, y: 2}`のcommaもbrace ownerが保持する。colon側がouter commaを
横取りしてrecord-like fieldを一個のmulti-argument colon tailへまとめない。

### Precedence-neutral OperatorChainとのintegration

recognition / commit controlを次で固定する。

Yulang2も`:`をinfix RHS / ML argument内ではparentへ返し、outermost tailだけでacceptした
(`yulang2-oracle@a58eefc3:spec/2026-06-06-syntax-design.md:818-819`)。flat chainではinfix RHSの
recursive parser自体がなくなるため、pending infix列を保持した同じouter chainがcolonをterminal itemとして
acceptする。nested `MlArgument`とconstruct-owner stopだけは明示的にcolonをparentへ返す。

```text
while OperatorChain is operand-complete:
    if active StopKind::Colon or ml_arg scope reserves this position:
        stop before colon and return it to the owner
    probe fixed punctuation with longest-match (:: before :)
    if lone Colon is absent:
        continue the ordinary structural/dynamic continuation judge
    if lone Colon is present:
        accept ColonApplicationTail and cut
        snapshot base_indent
        choose inline or indented RHS from post-colon trivia
        parse or recover the mandatory RHS
        finish ColonApplicationTail
        finish OperatorChain; no later chain item is accepted
```

colon candidateとpost-colon trivia / indent branchはcommit前までsink-freeである。lone colonを
`ColonApplicationTail`としてacceptした後は、RHSがmalformedでもoperator branchやouter expression armへ
戻らない。RHS recoveryを含むtotal continuationとしてtailとchainを必ず閉じる。

surface CSTではcolon tailより前の`Primary` / prefix / infix / suffix / structural itemをtailのchildへ移さない。
たとえば`a + b: x`は常に次のsource-order shapeを持つ。

```text
OperatorChain
  IdentifierExpression "a"
  InfixOperatorUse "+"
  IdentifierExpression "b"
  ColonApplicationTail
    Colon ":"
    Whitespace " "
    OperatorChain
      IdentifierExpression "x"
```

HIR associatorはcolon tailに到達した時点で直前までのpending dynamic segmentを全てreduceし、そのresultを
colon applicationのtargetにする。colon RHS内の各`OperatorChain`も同じassociation authorityでassociateする。
numeric BPだけが変わっても上のCST hierarchy、colon range、inline / block branch、recoveryは変わらない。
colon tailはdynamic operator useでもbinding-power sentinelでもなく、association後に適用されるterminal
structural operationである。

### CST shape

新しいnode kindを次で固定する。

```text
SyntaxKind::ColonApplicationTail
SyntaxKind::IndentedStatementBlock
```

`SyntaxKind::Colon` tokenは既存fixed punctuation kindを使う。inline branch専用のlist wrapperやgeneric
`ColonClause` nodeは作らない。

inline formは次になる。

```text
ColonApplicationTail
  Colon
  G0
  OperatorChain
  G*
  Comma
  G*
  OperatorChain
```

indented formは次になる。

```text
ColonApplicationTail
  Colon
  IndentedStatementBlock
    BlockOpeningTrivia
    Statement
    BlockStatementSeparator
    Statement
```

`ColonApplicationTail`のnormal rangeはcolon startからlast inline argumentまたはblock endまでである。
target expressionはrangeにもchildrenにも含めない。inlineのtrivia / commaはtail直下、block openingと
inter-statement triviaは`IndentedStatementBlock`直下にsource orderで置く。全source byteを一回だけ所有し、
`green.to_string() == source`を維持する。

### Parser-side AST shape

precedence-neutral chain追補のplaceholderを次へ具体化する。

```rust
pub(crate) enum OperatorChainItem<'source> {
    // Primary / operator-use / other structural items...
    TerminalOuter(TerminalOuterTail<'source>),
    MissingOperand { range: Range<usize> },
    Error { range: Range<usize> },
}

pub(crate) enum TerminalOuterTail<'source> {
    ColonApplication(ColonApplicationTail<'source>),
    Assignment(AssignmentTail<'source>),
    WithBody(WithBodyTail<'source>),
}

pub(crate) struct ColonApplicationTail<'source> {
    colon: Range<usize>,
    rhs: Recovered<ColonApplicationRhs<'source>>,
    range: Range<usize>,
}

pub(crate) enum ColonApplicationRhs<'source> {
    Inline {
        // Invariant: non-empty in Complete; recovered form may contain Missing/Error.
        arguments: Vec<Recovered<OperatorChain<'source>>>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}

pub(crate) struct IndentedStatementBlock<'source> {
    base_indent: usize,
    block_indent: usize,
    // Invariant: non-empty in Complete; recovered form may contain Missing/Error.
    statements: Vec<Recovered<Statement<'source>>>,
    range: Range<usize>,
}
```

`ColonApplicationTail`にtarget fieldを置かない。targetは同じouter `OperatorChain`の先行item列からassociatorが
作る。ASTのindent columnはlayout lowering / test projection用であり、lossless whitespace authorityはCSTである。
inline comma tokenもASTへduplicateせず、argument countとrecovery itemだけを渡す。

### BracedStatementBlockExpression内のrecord-literal-looking form

`{x: 1}`にrecord-literal専用CST nodeを追加しない。braceがexpression primaryとして現れてもcanonical
statement blockの`BracedStatementBlockExpression`であり、その中の`x: 1`がordinary `OperatorChain` +
`ColonApplicationTail`になる。Yulang2もこのshapeを明示していた
(`yulang2-oracle@a58eefc3:spec/2026-06-06-syntax-design.md:793-795`、
`crates/parser/tests/expr_grammar.rs:1093-1124`)。historical `{..base, x: 1, ..tail}`のfixed
`ExprSpread` itemはcolon grammarのownerではなく、末尾のbraced statement-block追補がfuture scopeへ分離する。
将来spread itemを追加しても、`x: 1`部分をgeneric colon applicationとして読む境界は変えない
(`crates/parser/tests/expr_grammar.rs:1128-1145`)。

後段がbrace statement列をrecord value、block value、または別のconstructとして解釈する場合も、
`yu-syntax`は`ColonApplicationTail`を`RecordField`へrename / reshapeしない。同じ`x: 1` surface formは
brace外でも同じcolon tail authorityを使う。

### Mandatory RHS recovery

colon accept後のRHSはmandatory slotであり、新しいrecovery primitiveを作らない。typed recovery vocabularyには
`GrammarRole::ColonApplication(ColonApplicationRole::{Rhs, InlineArgument, IndentedStatement})`を追加し、
期待値は既存`ExpectedSyntax::Expression`と、block item用に追加するtyped
`ExpectedSyntax::Statement`を使う。`Missing`はzero-width、`Error`はnon-empty、one recovery node = one
committed diagnosticを維持する。

代表caseを次で固定する。

| source situation | recovery / ownership |
| --- | --- |
| `f:` + EOF | colonを保持し、EOFにRHS用zero-width `Missing`一件。tail / chainをfinishする |
| `f:   ` + EOF | horizontal triviaをtailへ保持し、EOFに同じ`Missing`一件 |
| `f:\nnext`で`indent(next) <= base_indent` | post-colon newline probeをrollbackし、colon直後に`Missing`。newlineと`next`はouter ownerへ残す |
| `f:\n  ` + EOFでwritten indentがbaseより深い | `IndentedStatementBlock`とopening triviaを保持し、block内EOFにstatement用`Missing`一件 |
| `f: , x`でcolonがcomma owner | first argument位置に`Missing`、commaを保持し、`x`をsecond argumentとしてretryする |
| `f: x,` + EOFでcolonがcomma owner | comma後にnext-argument用`Missing`一件。trailing commaをvalid markerへ変えない |
| commaをouter ownerが予約 | colonはcommaをconsumeせず、missing RHSが必要ならcomma直前に一件置いてouterへ返す |
| inline invalid run後にvalid value start | run全体を一個のnon-empty `Error`にし、同じargument slotをvalid startからretryする |
| block内のmalformed statement | canonical statement recoveryで`Error` / `Missing`を一件作り、次sibling indentまたはdedentへ同期する |

wrong-indent newline、outer comma、matching close、dedent、statement/root boundaryはowner safe pointとして
consumeしない。invalid bytesを一byteずつの`Error`へ分割せず、block recoveryが作ったdiagnosticをcolon tailや
後段associatorが重複発行しない。recovered `ColonApplicationRhs`はHIR associatorがtyped error target/bodyへ
totalにlowerできなければならない。

### Interpretation boundary

association / lowering orderを次で固定する。

1. colonより前のouter flat item列をdedicated HIR associatorが一個のtarget expressionへassociateする。
2. inline RHSの各`OperatorChain`、またはblock内statement expressionを同じauthorityでassociateする。
3. syntax-to-HIR loweringはinline / indented shape、source range、recoveryを保持したneutral colon-application
   operationを作る。
4. function-call sugar、block argument、brace composition、construct固有desugaringなどのsemantic interpretationを
   後段ownerが決める。

type inferenceはoperator associationもcolon surface classificationも行わない。parserもtarget type、callee
arity、record field name、block result typeを見てCST shapeを変えない。

### Existing architecture principlesとの整合

- **rollback discipline:** `:` / `::`、post-colon trivia、inline / block branch、outer comma ownershipを
  sink-freeにprobeする。colon accept後はcutし、RHS recovery込みでtotal continuationにする。
- **direct CST / no event buffer:** branch確定後、colon、trivia、argument chain / block、recoveryをsource orderで
  一度emitする。preceding targetをwrapせず、event replayを置かない。
- **precedence-neutral chain:** colonはnumeric BPを読まずterminal structural itemになる。associatorだけが
  preceding pending segmentをflushする。BP-only changeでcolon CSTをreparseしない。
- **immutable operator table / oracle judge:** lone colonはfixed punctuationでoperator tableに追加しない。
  continuation judgeは`::`、owner stop、call/path-sensitive ruleを先に裁定し、dynamic operator spellingと競合させない。
- **stop-set ownership:** `StopKind::Colon`はconstruct owner予約、`StopKind::Comma`はinline-list ownershipに使う。
  nested scopeはpush / popし、outer setをin-place mutationして漏らさない。
- **layout state:** `LineState`と`IndentationBaseline`だけをindent authorityにし、colon専用raw whitespace counterを
  作らない。input checkpointと同時にbaseline / inline / ml_arg / stop stateをrollbackする。
- **lexical-region-aware recovery:** string、comment、heredoc、interpolation、rule literal、Yumark、fence内のcolon /
  comma / newlineをtail、separator、dedentへ誤分類しない。
- **single grammar authority:** inline argumentとblock statementはcanonical `OperatorChain` / `Statement`を呼ぶ。
  colon専用expression parser、record-field parser、second Pratt parserを作らない。

### Implementation boundary and required gates

最初のyu-syntax implementation sliceは、lone-colon LED recognition、`ColonApplicationTail`、inline argument loop、
reusable `IndentedStatementBlock` continuation、typed recovery、lossless CST / parser-side AST testまでを含む。
HIR association / colon desugaringは別sliceだが、target-free chain itemとfixture expected shapeを先に固定する。
assignment、`with:`、その他colon grammar familyを同じchangeへ混ぜない。

current implementationでは`scan/punctuation.rs`が`PunctuationKind::Colon`をlossless rangeとしてrecognizeするが、
expression continuationはまだlone colonをconsumeせず、grammarで使われるcolon spellingはuse pathの`::`だけである。
したがってこのsliceはscanner追加ではなく、既存fixed tokenをchain continuationとlayout ownerへ接続するchangeになる。

yu-syntax gateを次で固定する。

1. current `PunctuationKind::Colon`をoperand-complete continuationだけがconsumeし、`::`を分割しない。
2. `f: x + y`がterminal `ColonApplicationTail` + one flat RHS chain、`f: x, y + z`がtwo argument chainになる。
3. colonより前後のdynamic BPだけを変えてもgreen CST、surface AST、diagnostic、rangeがexact一致する。
4. `a + b: x`でpreceding itemをtailへnestせず、colon後に同じchainのitemを受理しない。
5. `f:\n  x\n  y`がone `IndentedStatementBlock`を持ち、equal / lower indentでblockを開始しない。
6. first statementのindentを`block_indent`に固定し、dedent boundaryをconsumeせず、baseline / inline / ml_arg /
   stop scopeを全exit pathでrestoreする。
7. root `f: x, y`ではcolonがcommaを所有し、`(f: x, y)`と`{x: 1, y: 2}`ではouter ownerがcommaを保持する。
8. `{x: 1}`がdedicated record CSTなしで`BracedStatementBlockExpression` + ordinary colon tailになる。
9. EOF、horizontal-trivia EOF、wrong indent、empty indented block、leading / trailing comma、invalid run、malformed
   block statementをrecovery table通り固定する。
10. all recoveryで`Missing` zero-width、`Error` non-empty、node / diagnostic一対一、owner boundary unconsumed、
    node balanced、`green.to_string() == source`を満たす。
11. candidate probe中のsink callは0、colon commit後のemissionは一回、source-wide buffer / replayは0である。

HIR gateを次で固定する。

1. preceding flat segmentをassociateしてからcolon targetへ使い、surface CSTへtreeを書き戻さない。
2. inline全argumentとblock内expressionをassociateし、source order / rangeを失わない。
3. inline / indented shapeを保持するneutral colon HIRを作り、type inferenceへsyntax decisionを移さない。
4. recovered RHSをpanic / hang / unconsumed itemなしでdeterministic error HIRへlowerし、parser diagnosticを複製しない。

### Other lone-colon grammar families: explicit future scope

本追補は次を設計しない。各ownerは`StopKind::Colon`でgeneric tailを止め、future addendumでtoken ownership、
inline / block body、recoveryを個別に固定する。

- `if` / `elsif` / `else`は末尾の`if`-expression追補が所有する。`catch`、`case` arm、`for`、
  `sub` / lambdaなど残りのcontrol-expression / statement body introducerはfuture scopeである。
- `impl`、`where`、`mod`、`role`、`struct`、`enum`、`type`、`error`、`act`、castなどdeclaration head / body。
- struct field、enum variant payload、act member、where predicateなどdeclaration-internal separator / annotation。
- pattern type annotation、pattern field / named slot、polymorphic-variant-like colon starterなどpattern grammar。
- type field / named argument、polymorphic-variant-like colon starterなどtype grammar。
- `with:`の二token structural continuation。これは`WithBodyTail` ownerであり、generic colon applicationではない。

`{x: 1}`だけはfuture record grammarではない。本追補と末尾のbraced statement-block追補で決めた
`BracedStatementBlockExpression` + generic colon application reuseがcurrent surface decisionである。
後段semantic record interpretationを追加してもCST ownerは変えない。

### Closed decisions and remaining implementation detail

本追補のimplementation directionをblockするopen questionはない。次を確定する。

- full RHS scope: non-empty inline comma list **and** indented statement block。
- strict `block_indent > base_indent` triggerとdedent boundary。
- target-free terminal `ColonApplicationTail`、no dynamic BP、no following same-chain item。
- outer comma ownership優先、colon-owned trailing comma禁止。
- `BracedStatementBlockExpression`内のrecord-like reuseとdedicated record CST禁止。
- existing mandatory-slot / `Missing` / `Error` / typed diagnostic machineryによるtotal recovery。
- generic colon applicationと他colon grammar familyの`StopKind::Colon`境界。

future implementationで詰めてよいのは、canonical `Statement` enumのconcrete module split、AST collectionの
small-vector choice、diagnostic display wordingである。inline / block acceptance、indent inequality、comma owner、
CST hierarchy、phase boundaryは変更しない。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定、ユーザ承認済み
（2026-08-22、generic colon application / indented block boundary追補案）。

## 追補案: NUD-primary `if` / `elsif` / `else` expression grammar

Status: Claude review / exact wordingのfinal sign-off待ち。

Date: 2026-08-22。

### Decision summary

Yulang3の`if` expressionは、`ParenthesizedExpression`と同じNUD-positionの
`PrimaryExpression`としてparseする。completed operandの後ろへ付く
`TerminalOuterContinuation`でも、generic `ColonApplicationTail`でもない。したがって`if` expressionは
operandを開始できる全位置に現れ、condition / arm body内部のdynamic operator列はそれぞれflat
`OperatorChain`のまま保持される。outer prefix / infix / suffix / fixed structural continuationは、完成した
`IfExpression` primaryの周囲へordinary chain itemとして続く。

一個の`IfExpression` CST nodeは、最初の`IfKw`を持つ`IfArm`、zero-or-moreの`ElsifKw`を持つ同じ
`IfArm` node kind、optionalな`ElseArm`をsource orderに持つ。`elsif`は`else if`へrewriteしない独立keywordである。
各`if` / `elsif` conditionは`Condition` nodeで包み、arm-owned lone `:`の直前でcurrent-depth
`OperatorChain`を止める。armのcolonは`IfArm` / `ElseArm`が直接所有し、
`ColonApplicationTail` wrapperを作らない。

最初のimplementation sliceは次のbody formを採用する。

- `if` / `elsif`: colon + exactly one inline `OperatorChain`、またはcolon + one
  `IndentedStatementBlock`。
- `else`: 上のcolon formに加え、colonなしのexactly one bare `OperatorChain`。
- colon後のinline bodyをcomma-separated argument listにはしない。
- brace bodyは採用しない。current `yu-syntax`に`BraceGroup` primary / body grammarがなく、token kindだけを
  先行させてもlossless body ownershipを確定できないためである
  (`crates/yu-syntax/src/syntax_kind.rs:6-76`,
  `crates/yu-syntax/src/grammar/expression.rs:125-145,395-403`)。brace group実装後の
  別sliceへdeferする。

`IndentedStatementBlock`はsingle-expression専用nodeではない。colon applicationが実装済みの同じnode、
strict indent trigger、statement loop、separator / dedent ownershipを再利用する。したがってarmのbody slotは
inlineでは一個のexpression、indented formでは一個のblockであり、そのblockは複数の`Statement` childを
持ち得る。current `Statement`の実装範囲はexpression statement subsetであり、declaration statementの追加は
block grammar側のfuture expansionである。

このshapeはYulang2のsurface grammarを基準にする。Yulang2は`if`をprimary expressionとして列挙し
(`yulang2-oracle@a58eefc3:spec/2026-06-06-syntax-design.md:762-787`)、scannerで`if` / `else` / `elsif`を
別keyword tokenにした
(`yulang2-oracle@a58eefc3:crates/parser/src/scan/mod.rs:263-269`)。parserは一個の`IfExpr`内へ
`IfArm*`とoptional `ElseArm`を置き、各conditionを`Cond`で包んだ
(`crates/parser/src/expr/control.rs:365-430,432-457,484-518`)。Yulang3はこのarm hierarchyを維持するが、
child expressionをPratt treeではなくprecedence-neutral `OperatorChain`にする。

### Architectural placement: NUD primary, not terminal continuation

precedence-neutral chain追補のgrammarを次のように具体化する。

```text
OperandSlot :=
    { PrefixUse G* }
    Value

Value :=
    PrimaryExpression
  | NullfixUse

PrimaryExpression :=
    IdentifierExpression
  | IntegerLiteral
  | ParenthesizedExpression
  | IfExpression
  | future primary forms

TerminalOuterContinuation :=
    ColonApplicationTail
  | AssignmentTail
  | WithBodyTail
```

`IfExpression`は`PrimaryExpression` branchであり、最後のproductionには入らない。たとえばprefix useの後、
parenthesized element、colon applicationのinline argument、indented blockのexpression statement、将来のcall
argumentのいずれでもordinary operand valueとして認識できる。`IfExpression`がfinishした後は、同じouter
`OperatorChain`がsuffix / infix / fixed structural tailを認識する。

この位置づけはYulang2 specのprimary classificationと一致するが、implementationはYulang2のPratt ownershipを
復元しない。condition、inline body、bare else body、block statementに現れる各operator chainのassociationは、
既決通りdedicated pre-HIR associator / HIR loweringが所有する。`IfExpression`というcontrol-flow hierarchyの
構築はsyntax lowering、branch result typeの統一はtype inferenceの責務であり、numeric BPによるtree shapeを
`yu-syntax`へ戻さない。

### Valid grammar for the first slice

`G*`はmaximal lossless trivia run、`G0`はphysical newlineを含まないmaximal trivia runである。
`Gcont`はcurrent expression baseに対するordinary continuation layoutを満たすtrivia runを表す。
`ArmContinuation`だけは後述のif-chain専用base-indent ruleを使う。

```text
IfExpression :=
    IfArm
    { ArmContinuation ElsifArm }
    [ ArmContinuation ElseArm ]

IfArm :=
    IfKw G* Condition Gcont ColonIntroducedArmBody

ElsifArm :=
    ElsifKw G* Condition Gcont ColonIntroducedArmBody

Condition :=
    OperatorChain
    under current-depth StopSet { Colon, LeftBrace, Elsif, Else }

ColonIntroducedArmBody :=
    Colon G0 InlineArmExpression
  | Colon IndentedStatementBlock

InlineArmExpression :=
    OperatorChain under IfContinuationStop

ElseArm :=
    ElseKw Gcont
    (
        ColonIntroducedArmBody
      | BareElseExpression
    )

BareElseExpression :=
    OperatorChain under ordinary NUD-start layout and IfContinuationStop

ArmContinuation :=
    HorizontalTrivia
  | NewlineTrivia where next_indent >= if_base_indent

IfContinuationStop :=
    current outer StopSet plus Elsif plus Else

Colon := the lone fixed punctuation token ":"
```

`IfArm`と`ElsifArm`はBNF上のkeyword制約を読みやすく分けた名前であり、CST node kindはどちらも
`SyntaxKind::IfArm`である。最初のarmだけが`IfKw`、二個目以降が`ElsifKw`を持つ。

`ColonIntroducedArmBody`は説明用nonterminalであり、CST wrapper nodeを要求しない。normal CSTではcolon tokenと
inline `OperatorChain`または`IndentedStatementBlock`をarm直下へ置く。generic colon applicationと違い、
inline comma loop、target-before-tail、terminal `OperatorChainItem`のどれも持たない。

`else if ...`は`elsif`の別spellingではない。bare else bodyのprimaryとしてnested `IfExpression`を持つため
validになり得るが、CSTは`ElseArm(ElseKw, OperatorChain(IfExpression(...)))`である。
`ElsifKw`を持つsibling `IfArm`とは異なるliteral shapeを保持する。

### Keyword recognition and NUD routing

current word scannerはkeywordをlexical token classとして先決せず、maximal identifier-shaped spellingとrangeだけを
返す。この原則を維持し、sink-free NUD judgeがexact word `if`をrecognizeしてから
`NudRecognition::If { keyword, base_indent }`をacceptする。`ifx`、`if?`など別のmaximal wordをsplitしない。
accept後にcutし、direct CST側で`IfKw` tokenを一度emitしてrecovery込みの`IfExpression` continuationを完走する。

`elsif`と`else`はgeneric NUD alternativeではない。active `IfExpression` ownerがarm boundaryでexact spellingを
recognizeしたときだけ、それぞれ`ElsifKw` / `ElseKw`としてcommitする。dynamic word-operator、ML argument、
identifier expressionよりowner stopを優先し、前arm bodyへ吸収させない。word scanningのcontextual natureと、
CST token kindとしてkeyword factを保存することは両立する。

required syntax vocabularyを次で固定する。

```text
SyntaxKind::IfExpression
SyntaxKind::IfArm
SyntaxKind::ElseArm
SyntaxKind::Condition
SyntaxKind::IfKw
SyntaxKind::ElsifKw
SyntaxKind::ElseKw
```

separate `SyntaxKind::ElsifArm`、generic `ColonClause`、arm-owned `ColonApplicationTail`は追加しない。

### Condition boundary and scoped stops

condition parse前にincoming stop setをcopyし、current-depth local frameへ次を加える。

```text
StopKind::Colon
StopKind::LeftBrace
StopKind::Elsif
StopKind::Else
```

`StopKind::Colon`によりconditionのcompleted `OperatorChain`はlone colon直前でreturnし、generic
`recognize_colon_application_tail`はそのcolonをconsumeしない。これはYulang2がcondition local stopへ
`Colon`と`BraceL`を入れてownerへ返したboundaryと同じである
(`yulang2-oracle@a58eefc3:crates/parser/src/expr/control.rs:432-457`)。current flat-chain implementationでは
numeric minimum BPを渡す必要はなく、stopだけがboundary authorityになる。

`StopKind::LeftBrace`はbrace bodyをfirst sliceでacceptするためではない。future `BraceGroup` primaryが追加された
とき、condition extentが暗黙に変わってbrace bodyをcondition operandとして飲み込まないためのforward-compatible
reservationである。first sliceでcurrent-depth `{`に到達した場合はconditionをそこで止め、unsupported bodyを
generic expressionとしてconsumeしない。brace tokenはouter recoveryへ残す。

`Elsif` / `Else` stopはmissing condition / body recoveryとinline arm boundaryを守る。delimiter、string、comment、
heredoc、interpolation、rule literal、Yumarkなどnested lexical region内部の同じspelling / colon / braceには
反応しない。parenthesizedなどnested expression ownerは自分のstop frameをpushし、そのdelimiter内部のcolon
applicationを通常どおり許す。全frameはComplete / Incompleteの両pathでpopする。

### Colon body and `IndentedStatementBlock` reuse

arm-owned colonをrecognizeした後のinline / indent branch判定は、colon applicationで実装済みの一個のlayout
primitiveを再利用する。

```text
has_physical_newline(post_colon_trivia)
&& block_indent > if_base_indent
    => IndentedStatementBlock

no_physical_newline(post_colon_trivia)
    => exactly one inline OperatorChain

has_physical_newline(post_colon_trivia)
&& block_indent <= if_base_indent
    => missing body; leave newline/dedent to the outer owner
```

`if_base_indent`は最初の`if`をparseし始めたcurrent expression / statement baselineであり、colon tokenのvisual
columnではない。post-colon trivia scan前にsnapshotし、wrong-indent判定ではcheckpointへrollbackする。
このstrict inequalityはYulang2 specのindent block triggerと一致する
(`yulang2-oracle@a58eefc3:spec/2026-06-06-syntax-design.md:195-205`)。

inline branchは一個のflat `OperatorChain`だけをparseする。generic colon applicationの
`InlineColonArguments := OperatorChain (Comma OperatorChain)*`を呼ばない。したがって`if x: a, b`のcommaは
arm bodyのargument separatorではなく、incoming outer list ownerへ返るか、そのcontextのrecovery対象になる。

indented branchは既存`SyntaxKind::IndentedStatementBlock`と同じstatement loopを使う。Yulang2のshared
`parse_inline_or_indent`もdeep-newline branchで`parse_indent_stmt_block`を呼び
(`yulang2-oracle@a58eefc3:crates/parser/src/expr/control.rs:22-35,460-469,497-506`)、そのblock parserは
dedentまで`parse_statement`を反復した
(`crates/parser/src/stmt/block.rs:242-283`)。fixtureのblockに一個の`1`しかないこと
(`crates/parser/tests/expr_grammar.rs:1755-1784`)は、block arityを一に制限する証拠ではない。
Yulang3側にも`statements: Vec<Recovered<Statement>>`を持つblock projectionとdirect statement loopが実装済みである
(`crates/yu-syntax/src/grammar/expression.rs:88-102,830-908,1011-1077`)。

reuseはnode / trigger / loop / separator ownershipのreuseであって、diagnostic roleの流用ではない。
shared block continuationはowner-specific recovery roleとoptional companion-stop probeを受け取れる形にする。
if armの場合、次statementをcommitする前にcurrent lexical depthの`elsif` / `else` candidateをsink-freeにprobeし、
candidateならboundary triviaとkeywordをconsumeせずblockをfinishする。colon application用
`GrammarRole::ColonApplication`でif-body diagnosticを発行しない。

### `elsif` / `else` chain continuation and layout ownership

`IfExpression`開始時に`if_base_indent`をsnapshotする。各arm bodyがreturnした位置で、次のcandidateを次の順で
probeする。

1. physical newlineを含まないhorizontal triviaの直後にexact `elsif` / `else`があれば同じchainへ入れる。
2. physical newlineを含む場合、next lineのindentが`if_base_indent`以上で、次のnon-trivia tokenがexact
   `elsif` / `else`のときだけ同じchainへ入れる。
3. indentが`if_base_indent`未満、または次tokenがarm keywordでない場合はprobe前へrollbackし、triviaとtokenを
   outer ownerへ残して`IfExpression`をfinishする。
4. `ElseArm`を一個commitした後はchainを必ずfinishする。後続`elsif` / `else`を同じnodeへ追加しない。

この`>=`は「initial `if`とexact same indentだけ」という新規制約ではない。Yulang2 parserは
`base_indent`を一度保存し、horizontal spaceまたは`indent >= base_indent`のnewlineだけをcontinuation候補にし、
newlineではさらにnext tokenが`Elsif` / `Else`かをpeekした
(`yulang2-oracle@a58eefc3:crates/parser/src/expr/control.rs:365-420`)。specも同じruleを明記する
(`yulang2-oracle@a58eefc3:spec/2026-06-06-syntax-design.md:207-208,1075-1077`)。

ordinary expression tailはequal-indent newlineで止まるが、arm continuationはこの専用probeに限って
equal-indent keywordを拾う。`if x:\n  1\nelse: 0`のdedent-leading triviaをblockがconsumeせず、
`IfExpression`が`ElseKw`とともに所有する。Yulang2 fixtureもこの一node shapeを固定していた
(`yulang2-oracle@a58eefc3:crates/parser/tests/expr_grammar.rs:1755-1784`)。

### CST shape and byte ownership

inline multi-arm formは次のshapeを持つ。

```text
OperatorChain
  IfExpression
    IfArm
      IfKw "if"
      Whitespace " "
      Condition
        OperatorChain
          IdentifierExpression "x"
      Colon ":"
      Whitespace " "
      OperatorChain
        IntegerLiteral "1"
    Whitespace " "
    IfArm
      ElsifKw "elsif"
      Whitespace " "
      Condition
        OperatorChain
          IdentifierExpression "y"
      Colon ":"
      Whitespace " "
      OperatorChain
        IntegerLiteral "2"
    Whitespace " "
    ElseArm
      ElseKw "else"
      Colon ":"
      Whitespace " "
      OperatorChain
        IntegerLiteral "0"
```

indented bodyはcolonの直後へ同じblock nodeを直接置く。

```text
IfExpression
  IfArm
    IfKw
    Condition
      OperatorChain
    Colon
    IndentedStatementBlock
      BlockOpeningTrivia
      Statement
        OperatorChain
      BlockStatementSeparator
      Statement
        OperatorChain
  InterArmTrivia
  ElseArm
    ElseKw
    Colon
    OperatorChain
```

`Condition`はconditionのexpression bytesだけを所有する。conditionとcolonの間のtrivia、colon、body、arm間の
triviaは最小の共通ownerである`IfArm` / `ElseArm` / `IfExpression`直下へsource orderで置く。
`IfExpression.range`はinitial `IfKw.start`からlast committed/recovered arm endまで、各arm rangeはkeyword startから
body endまでである。dedent後のnon-arm trivia、outer comma / close、次statement starterをrangeへ含めない。
全byteを一回だけemitし、`green.to_string() == source`を維持する。

generic `ColonApplicationTail`はこのtreeに現れない。arm conditionをtargetにしたcolon applicationへreshapeせず、
inline bodyをgeneric colon argument listへreshapeしない。これはYulang2 fixtureの
`IfExpr(IfArm(If, Cond(...), Colon, Expr(...)), ElseArm(...))` shapeとも一致する
(`yulang2-oracle@a58eefc3:crates/parser/tests/expr_grammar.rs:1723-1751`)。

### Parser-side AST shape

precedence-neutral surface ASTを次で固定する。

```rust
pub(crate) enum PrimaryExpression<'source> {
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Parenthesized {
        elements: Vec<OperatorChain<'source>>,
        trailing_comma: Option<Range<usize>>,
        range: Range<usize>,
    },
    If(IfExpression<'source>),
}

pub(crate) struct IfExpression<'source> {
    // Invariant: non-empty; first is If, remaining entries are Elsif.
    arms: Vec<IfArm<'source>>,
    else_arm: Option<ElseArm<'source>>,
    base_indent: usize,
    range: Range<usize>,
}

pub(crate) struct IfArm<'source> {
    keyword: IfArmKeyword<'source>,
    condition: Recovered<OperatorChain<'source>>,
    body: Recovered<ColonIntroducedArmBody<'source>>,
    range: Range<usize>,
}

pub(crate) enum IfArmKeyword<'source> {
    If(WordSpan<'source>),
    Elsif(WordSpan<'source>),
}

pub(crate) struct ElseArm<'source> {
    keyword: WordSpan<'source>,
    body: Recovered<ElseArmBody<'source>>,
    range: Range<usize>,
}

pub(crate) enum ElseArmBody<'source> {
    Colon(ColonIntroducedArmBody<'source>),
    Bare(Box<OperatorChain<'source>>),
}

pub(crate) struct ColonIntroducedArmBody<'source> {
    colon: Recovered<Range<usize>>,
    rhs: Recovered<ArmBodyRhs<'source>>,
    range: Range<usize>,
}

pub(crate) enum ArmBodyRhs<'source> {
    Inline(Box<OperatorChain<'source>>),
    Indented(IndentedStatementBlock<'source>),
}
```

`Recovered<Range<usize>>`はnormal colon token rangeまたはmissing introducerをsurface projectionへ伝えるための
typed slotであり、CST token / `Missing` nodeの別authorityにはならない。concrete implementationでexisting
`Recovered<T>`がrange payloadを持てない場合、equivalentな`ColonSlot`型へ分けてよいが、normal colonとrecovered
colonを同じarm variantで表すこと、body shapeを推測しないことは変更しない。

condition / bodyの`OperatorChain`はassociation済みtreeではない。HIR loweringは各chainをcanonical associatorへ
一度渡した後、一個のconditional HIR nodeを構築する。type inferenceはbranch type / effectを扱うが、arm count、
colon ownership、operator association、inline / block classificationを再判定しない。

### Recognition / commit control flow

direct parserのcontrolを次で固定する。

```text
at an operand-required NUD site:
    sink-free scan one maximal word
    if the exact spelling is not "if":
        reject and rollback the whole candidate
    accept NudRecognition::If and cut
    start IfExpression
    snapshot if_base_indent

parse initial IfArm:
    emit IfKw
    start Condition
    push incoming stops + Colon + LeftBrace + Elsif + Else
    parse or recover one flat OperatorChain
    pop condition stops
    finish Condition
    recognize and commit the arm-owned colon
    select inline / indented body with the shared post-colon layout probe
    parse or recover exactly one body slot
    finish IfArm

after each IfArm:
    sink-free probe ArmContinuation + exact ElsifKw / ElseKw
    if no candidate, rollback the trivia and finish IfExpression
    if ElsifKw, cut and parse another IfArm total continuation
    if ElseKw, cut and parse one ElseArm total continuation, then finish

finish IfExpression
return it as one completed PrimaryExpression to the enclosing OperandSlot
continue the enclosing flat OperatorChain normally
```

probe中はRowan sink、committed recovery list、header factへ触れない。`IfKw`、`ElsifKw`、`ElseKw`のいずれかを
owner positionでacceptした後はcutし、missing condition / colon / bodyを含めてそのarm continuationを必ず閉じる。
accepted `elsif`をrollbackしてidentifierやoperatorへ読み替えない。

AST-only pathとdirect-CST pathは同じword / stop / layout / continuation recognizerを使う。CST-specific emissionを
surface AST parserへ逆流させず、二pathのarm count、ranges、inline / indented branch、recovery outcomeをfixtureで
一致させる。

### Mandatory-slot recovery

新しいrecovery primitiveを作らない。typed vocabularyへ次を追加する。

```text
GrammarRole::IfExpression(
    IfExpressionRole::{Condition, BodyIntroducer, Body, ElseBody, IndentedStatement}
)

ExpectedSyntax::Keyword(If | Elsif | Else)
ExpectedSyntax::Punctuation(Colon)
ExpectedSyntax::Expression
ExpectedSyntax::Statement
```

rangeがrecovery identityを区別するため、initial / elsifごとのindexをroleへ埋め込まない。
block statement recoveryはshared algorithmへowner roleを渡し、colon application diagnosticとして記録しない。
`Missing`はzero-width、`Error`はnon-empty、one recovery node = one committed diagnosticを維持する。

代表caseを次で固定する。

| source situation | recovery / ownership |
| --- | --- |
| `if : 1` | `Condition`内のcolon直前へcondition用`Missing`一件。colonとbodyをnormal commitする |
| `if` + EOF | `Condition`へ一個の`Missing`を置き、同じEOFへcolon / bodyの連鎖`Missing`を重ねずincomplete armを閉じる |
| `if x` + EOF | conditionを保持し、body-introducer / body absenceを一個のarm-body `Missing`へ集約する |
| `if x:` + EOF | colonを保持し、body用zero-width `Missing`一件でarmを閉じる |
| `if x:\nnext`で`indent(next) <= if_base_indent` | post-colon trivia probeをrollbackし、colon直後にbody `Missing`。newlineと`next`はouter ownerへ残す |
| `if x: @ y`で`@`がvalue startでない | maximal invalid runを一個のnon-empty `Error`にし、同じbody slotを`y`からretryする |
| `if x: 1 elsif : 2` | `ElsifKw`を保持し、その`Condition`内へ一個の`Missing`。second armを同じ`IfExpression`内で完走する |
| `if x: 1 else` + EOF | `ElseKw`を保持し、else body用`Missing`一件。optional elseを消してrollbackしない |
| `if x: 1 else: ` + EOF | colonを保持し、else body用`Missing`一件 |
| `if x: 1 else: 0 else: 2` | first `ElseArm`後に`IfExpression`を閉じ、second `else`をouter recoveryへ残す |
| continuation keywordのnewline indentが`if_base_indent`未満 | trivia / keywordをconsumeせずcurrent `IfExpression`を閉じる |
| current-depth `{` after condition | condition stopがbraceを保持する。first sliceはbrace bodyへcommitせず、incomplete armを閉じてbraceをouter recoveryへ残す |
| indented body内のmalformed statement | shared block recoveryで一個の`Error` / `Missing`を作り、next sibling、arm companion、またはdedentへ同期する |

missing colon recoveryのために`if x y`をcondition `x` + inferred body `y`へ分割しない。ML applicationやfuture
primary adjacencyを含むvalid condition extentと区別できないためである。fixed colonを挿入できるのはfollowing
slot / owner boundaryがgrammar上unambiguousなmandatory-slot caseだけとし、EOFまたはcontinuation keywordでcolonと
bodyが同じcauseから欠ける場合は一個のbody-owned recoveryへ集約する。

optional `ElseArm`がないことはerrorではない。`elsif` / `else` keywordをacceptする前のprobe failureもdiagnosticを
作らない。associator / HIR loweringは全`Recovered` slotをtyped error expression / error blockへtotalにlowerし、
parser diagnosticを複製しない。

### Existing architecture principlesとの整合

- **precedence-neutral chain:** condition、inline arm body、bare else body、block statementはflat
  `OperatorChain`である。`IfExpression`はprimary hierarchyだけを所有し、numeric BPでarm / body CSTを変えない。
- **rollback discipline:** exact keyword、condition delimiter、post-colon layout、arm continuationをsink-freeにprobeする。
  keyword accept後はcutし、mandatory recovery込みのtotal continuationにする。
- **direct CST / no event buffer:** `IfExpression`をprimary開始位置からforward-onlyにemitする。completed childを
  wrap / replayせず、source-wide event bufferを作らない。
- **immutable operator table / oracle judge:** condition / body chainは同じimmutable tableとfixity-role judgeを使う。
  `if` / `elsif` / `else`はowner-recognized keywordでありdynamic operator tableへ追加しない。
- **stop-set ownership:** conditionはincoming setへ`Colon` / `LeftBrace` / arm keywordsを加え、bodyはincoming setへ
  arm keywordsを加える。outer setをin-place mutationせず、nested scope終了時にexact popする。
- **colon-application boundary:** arm-owned colon位置ではactive `StopKind::Colon`がgeneric tailを止める。
  sharedするのはpost-colon layout primitiveと`IndentedStatementBlock`であり、`ColonApplicationTail` node、inline
  comma arity、terminal-chain semanticsではない。
- **layout state:** `LineState` / `IndentationBaseline`を唯一のindent authorityにし、if専用raw whitespace counterを
  作らない。arm continuationだけがdocumented `indent >= if_base_indent` exceptionを所有する。
- **lexical-region-aware scanning:** nested delimiter / string / comment / heredoc / interpolation / rule / Yumark内の
  colon、brace、`elsif`、`else`をouter condition stopやarm continuationへ誤分類しない。
- **single block authority:** `IndentedStatementBlock`のtrigger、opening trivia、statement separator、dedent、recoveryを
  colon application実装から共通化する。if専用block loopをcopyしない。
- **association boundary:** pre-HIR associatorが全child chainを処理し、syntax-to-HIR loweringがconditional hierarchyを
  作る。type inferenceへsurface parse / association decisionを移さない。

### Implementation boundary and required gates

最初の`yu-syntax` sliceは次を一changeとして含む。

1. exact `if` NUD recognition、`IfExpression` / arm continuation、keyword token emission。
2. `SyntaxKind::{IfExpression,IfArm,ElseArm,Condition,IfKw,ElsifKw,ElseKw}`とsurface AST shape。
3. `StopKind::{LeftBrace,Elsif,Else}`、conditionの`Colon` reservation、outer stop preservation。
4. colon-owned exactly-one inline bodyとexisting `IndentedStatementBlock` reuse。
5. shared block loopへのowner-specific recovery role / arm-companion stop hook。block algorithmのcopyは不可。
6. colonなしbare else body。
7. mandatory-slot recovery、lossless direct CST、AST/direct parity fixture。

brace group、case-like abstraction、HIR conditional loweringを同じimplementation changeへ混ぜない。

`yu-syntax` gateを次で固定する。

1. `if x: 1 else: 0`がone `IfExpression`、one `IfArm`、one `ElseArm`を持ち、colon tail nodeを持たない。
2. `if x: 1 elsif y: 2 elsif z: 3 else: 0`がfirst / subsequent keywordを保ったthree sibling `IfArm`になる。
3. `elsif`は一tokenであり、`else if`はbare else body内のnested `IfExpression`になる。
4. `if x:\n  1\n  2\nelse: 0`がif arm直下のone `IndentedStatementBlock`にtwo `Statement`を持ち、dedent
   `else`がsame `IfExpression`へ入る。
5. inlineまたは`indent >= if_base_indent`のnewlineだけがarm continuationを認め、non-keyword / shallower lineで
   boundary triviaをconsumeしない。
6. block statement boundaryの`elsif` / `else`をError statementへせず、ownerへ返す。
7. condition colonは`ColonApplicationTail`にならず、nested parenthesized condition内のordinary colon applicationは
   local delimiter scope内で引き続き有効である。
8. inline arm bodyは一expressionであり、generic colon inline-list loopを呼ばない。
9. whole `IfExpression`の前後にprefix / infix / suffix useを置いても一個のprimary chain itemとしてflat orderを保つ。
10. condition / body operator BPだけを変えてもIf CST hierarchy、ranges、recovery、diagnosticsがexact一致する。
11. missing condition / body / colon、wrong indent、malformed later arm、duplicate elseをrecovery table通り固定する。
12. all recoveryで`Missing` zero-width、`Error` non-empty、node / diagnostic一対一、node balance、
    `green.to_string() == source`を満たす。
13. candidate probe中sink call 0、accepted keywordのemission一回、all scope framesのbalanced popを満たす。

HIR gateは別sliceで次を満たす。

1. condition / body / block statement chainをcanonical associatorへ一度だけ渡し、surface CSTへtreeを書き戻さない。
2. source-order arm list、optional else、inline / indented / bare shape、ranges、recoveryをconditional HIRへ保持する。
3. recovered armをpanic / hangなしでdeterministic error HIRへlowerし、parser diagnosticsを複製しない。
4. branch type / effect統一だけをtype inferenceへ渡し、syntax classificationを再実行しない。

### Explicit future scope

本追補は次を設計または実装しない。

- `if` / `elsif` / `else`のbrace body。ordinary primaryの`BracedStatementBlockExpression`とは共有せず、
  専用expression-list grammarが完成した後に`IfArm` / `ElseArm`直下のalternativeとして別sliceで追加する。
  Yulang2ではこれはstatement blockではなくexpression-list `BraceGroup`だった
  (`yulang2-oracle@a58eefc3:spec/2026-06-06-syntax-design.md:1047-1073`)。
- `IndentedStatementBlock`内のdeclaration / full statement family。current expression-statement subsetの拡張は
  canonical `Statement` grammarが所有する。
- `case` / `catch`のcase-like arm / guard grammar。Yulang2でも`parse_if_expr`はshared case-like machineryを
  呼ばず、共有したのはlow-level inline / indent helperだけだった
  (`yulang2-oracle@a58eefc3:crates/parser/src/expr/control.rs:365-519,521-571`)。
- `for`、`sub` / lambda、declaration body、pattern / type annotationなど他のcolon-owner family。
- conditional HIR、short-circuit / effect semantics、branch result typing、exhaustiveness。これらはsyntax addendumの
  ownerではない。

generic colon-application追補のfuture-scope listにあった`if` / `else` slotは本追補が具体化する。
他のcolon familyは引き続きそれぞれのowner addendumを必要とし、一個のshared `ColonClause`へ統合しない。

### Closed decisions and review focus

本追補のimplementation directionをblockするopen questionはない。次を確定する。

- `if`はNUD-position `PrimaryExpression`であり、terminal tailではない。
- `elsif`は独立keyword、CSTではsubsequent sibling `IfArm`である。
- first sliceはcolon inline / indented bodyとbare `else expr`を含み、brace bodyだけをdeferする。
- indented bodyはmultiple statementを持てるexisting `IndentedStatementBlock`そのものである。
- conditionはcurrent-depth colon / future brace boundaryをstopでownerへ返す。
- arm continuationはhorizontalまたはnewline `indent >= if_base_indent` + exact keywordである。
- arm colonはdirect childであり、`ColonApplicationTail`とinline comma-list semanticsを再利用しない。
- condition / body associationはpre-HIR associator、conditional hierarchy loweringはHIR、branch typingはinferenceが
  それぞれ所有する。

Claude reviewでは、特にowner-specific block terminator hookがnested `if`を誤停止しないこと、incoming stop setを
condition / body scopeが失わないこと、same-position recovery aggregationが既存mandatory-slot contractと一致することを
確認対象にする。これらはconcrete helper signature / diagnostic display wordingの調整余地であり、上のgrammar arity、
CST hierarchy、layout inequality、phase boundaryをopenに戻さない。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定、ユーザ承認済み
（2026-08-22、NUD-primary `if` / `elsif` / `else` expression grammar追補案）。

## 追補案: NUD-primary brace-delimited statement-block expression

Status: Claude review / exact wordingのfinal sign-off待ち。

Date: 2026-08-22。

### Decision summary

Yulang3のordinary expression positionに現れる`{ ... }`は、NUD-positionの
`PrimaryExpression`としてparseする。中身はzero-or-moreのcanonical `Statement`であり、dynamic operatorを
precedence-shaped treeへしない点も、colon-introduced `IndentedStatementBlock`内のstatementと同じである。
completed operandへ付く`ColonApplicationTail` / `TerminalOuterContinuation`ではなく、
`ParenthesizedExpression` / `IfExpression`と並ぶ一個のprimary valueである。

CST node kindは`SyntaxKind::BracedStatementBlockExpression`とする。Yulang2の`BraceGroup`はordinary primary、
declaration body、if / elsif / elseのexpression-list body、projection-record tail、rule body、use-spec list、
string interpolationなど構造の異なるownerへ再利用されていたため、その名前をYulang3へ移植しない。
`BracedStatementBlockExpression`は**ordinary primary expressionだけ**の名前であり、future declaration bodyや
if-bodyへ共有しない。inner statement-sequence engineを共有しても、outer CST node authorityは各constructの
addendumが個別に決める。

valid separatorはcomma、semicolon、current statementを終了させるphysical newlineの三種である。empty `{}`と、
matching `}`直前のtrailing comma / semicolon / implicit-newline separatorをvalidにする。これは
`IndentedStatementBlock`よりseparator setとempty ruleが広いが、statement parse、recovery、progress guarantee、
separator emissionを別実装にしない。closed policyを受け取るshared statement-sequence coreへ既存indent loopを
factorし、brace ownerはmatching close / separator policyだけを提供する。

`{x: 1}`をrecord literalとしてspecial-caseしない。これは一個の`Statement`を持つ
`BracedStatementBlockExpression`であり、そのstatementのflat `OperatorChain`がordinary
`ColonApplicationTail`で終わるだけである。empty record、record field、block valueなどのsemantic interpretationを
見てparserがnode kindを変えない。

### Fresh historical verification: exact Yulang2 statement-block rule

Yulang2でordinary brace primaryはNUD `OpenBrace`から`parse_brace_stmt_block`へdispatchされた
(`yulang2-oracle@a58eefc3:crates/parser/src/expr/core.rs:102-115`)。そのparserは一個の
`BraceStmtBlockMachine`で`parse_statement`を反復した
(`crates/parser/src/stmt/block.rs:14-18,54-69,156-185`)。

separatorについて、fresh source verificationは次を示す。

1. normal statement parseはlocal stopへ`Comma`を追加し、returned `Comma`または`Semicolon`を
   `Separator` nodeとしてacceptする
   (`crates/parser/src/stmt/block.rs:54-69,77-98`)。
2. statementが`TriviaInfo::Newline`でreturnした場合、source tokenを合成しないempty `Separator` nodeをemitして
   implicit newline separatorにする
   (`crates/parser/src/stmt/block.rs:82-89`)。
3. specもbrace statement blockのseparatorをcomma、semicolon、newlineの三種として列挙する
   (`yulang2-oracle@a58eefc3:spec/2026-06-06-syntax-design.md:182-193`)。
4. `{x: 1, y: 2}` fixtureでは二個のstatement-like `Expr`の間のcommaがouter `Separator`であり、first
   `ApplyColon`のargument commaではない
   (`yulang2-oracle@a58eefc3:crates/parser/tests/expr_grammar.rs:1093-1124`)。
5. semicolonとimplicit newlineのactual statement-block shapeはdeclaration body fixtureでも固定されている
   (`crates/parser/tests/stmt_grammar.rs:819-863`)。同じ`parse_brace_stmt_block` entrypointがordinary primaryと
   declaration bodyから呼ばれるため、separator machineのevidenceとして有効である。

empty / trailing ruleは`StopListMachine` controlから確定できる。各iterationの最初に次non-trivia tokenが
`BraceR`ならitem parseを行わずcloseを返すため、first iterationの`{}`はvalid empty blockになる
(`crates/parser/src/stmt/block.rs:18-33`)。statement後のcomma / semicolonはseparatorとしてcommitして次iterationへ
進み、そこで`BraceR`を直接acceptするためtrailing explicit separatorもvalidである
(`stmt/block.rs:77-98`; `crates/parser/src/parse/mod.rs:146-175`)。newline returnも先にimplicit `Separator`をemitして
同じnext-iteration close pathへ入るため、trailing implicit newlineもvalidである。separator後に架空のempty
statementや`Missing(statement)`を作らない。

したがって「statement-block formはnewline / semicolonだけでcommaを受理しない」という要約は誤りである。
commaはhistorical primary statement-block自身のvalid separatorであり、Yulang3でも維持する。

同じhistorical machineは`..expr`を`ExprSpread`として読むbrace-local special branchも持っていた
(`crates/parser/src/stmt/block.rs:35-52`)。ただし本追補のrequested productionとcurrent Yulang3
`Statement` authorityは`{ statement* }`であり、fixed spread itemはまだ設計されていない。最初のsliceへ
`BraceSpreadItem`を暗黙追加せずfuture scopeへ分離する。dynamic prefix operatorとして書ける`..expr`があっても、
それはordinary expression statementであってparser-selected spread roleではない。colon-application追補にあった
historical spread fixtureのpremature gateは、本追補がこの範囲だけsupersedeする。

### Scope and non-unification boundary

本追補が所有するsurface positionは次だけである。

```text
Value :=
    PrimaryExpression
  | NullfixUse

PrimaryExpression :=
    IdentifierExpression
  | IntegerLiteral
  | ParenthesizedExpression
  | IfExpression
  | BracedStatementBlockExpression
  | future primary forms
```

`BracedStatementBlockExpression`はoperand-required NUD siteでrecognizeする。prefix useの後、parenthesized element、
colon application argument、if condition / body、indented statement、future call / ML argumentなど、ordinary
primaryを置ける全位置に現れ得る。matching `}`後はcompleted primaryとしてouter flat `OperatorChain`へ戻り、
suffix / infix / fixed structural continuationを通常どおり続ける。

次のhistorical `BraceGroup` ownerとはnode kindもgrammar entrypointも共有しない。

- if / elsif / else brace bodyとprojection-record tailが使った`ExprListMachine`。これはstatementを許さない
  expression listであり、spreadを含む別item grammarだった
  (`yulang2-oracle@a58eefc3:crates/parser/src/expr/group.rs:13-27,48-118`,
  `expr/control.rs:459-478,484-510`)。
- `rule { ... }`のrule-body-specific parser
  (`yulang2-oracle@a58eefc3:crates/parser/src/expr/rule.rs:30-66`)。
- `use ... { ... }`のuse-spec parser
  (`yulang2-oracle@a58eefc3:crates/parser/src/stmt/use_decl.rs:464`)。
- `%{...}` interpolationのvirtual statement block
  (`yulang2-oracle@a58eefc3:crates/parser/src/string/parse.rs:172-179`,
  `crates/parser/src/stmt/block.rs:219-239`)。
- `catch`固有の`CatchBlock`。`case`にはbrace form自体がない。

declaration bodyはhistorically同じ`parse_brace_stmt_block` functionを呼んだが、Yulang3のouter CSTをここでは
決めない。`for` / `mod` / `act` / `role` / `type`などのdeclaration grammarが追加されるとき、shared inner
statement-sequence coreを利用してよいが、`BracedStatementBlockExpression` nodeをdeclaration childとして
流用してはならない
(`yulang2-oracle@a58eefc3:crates/parser/src/stmt/for_stmt.rs:63`,
`mod_decl.rs:64`, `act_decl.rs:70`, `role_decl.rs:67-105`, `type_decl.rs:196-262`)。

### Valid grammar

`G*`はnewlineを含み得るmaximal lossless trivia run、`G0`はphysical newlineを含まないmaximal trivia runである。
`Gnl`は一個以上のphysical newlineを含み、completed statementがordinary expression-continuation ruleによって
returnしたmaximal trivia runである。raw scannerがdeeper continuation lineを先にstatementへ分割する意味ではない。

```text
BracedStatementBlockExpression :=
    LBrace OpeningTrivia
    [
        Statement
        { BraceStatementSeparator Statement }
        [ BraceStatementSeparator ]
    ]
    ClosingTrivia RBrace

BraceStatementSeparator :=
    G0 Comma G*
  | G0 Semicolon G*
  | Gnl

OpeningTrivia := G*
ClosingTrivia := G0
```

BNFの`OpeningTrivia`はfirst statementまたはmatching closeの前にあるためseparatorではない。
statementを一個以上commitした後の`Gnl`だけがimplicit `BlockStatementSeparator`になる。explicit comma /
semicolon branchが後続newlineを含むtriviaを所有した場合、そのnewlineへsecond implicit separatorを重ねない。

valid formを次で固定する。

| source form | statement count | separator shape |
| --- | ---: | --- |
| `{}` / `{   }` / `{\n}` | 0 | none。opening / closing triviaだけ |
| `{x}` | 1 | none |
| `{x,y}` | 2 | comma separator |
| `{x;y}` | 2 | semicolon separator |
| `{x\ny}` | 2 | implicit newline separator |
| `{x,}` | 1 | valid trailing comma separator |
| `{x;}` | 1 | valid trailing semicolon separator |
| `{x\n}` | 1 | valid trailing implicit newline separator |

separatorはstatement間にexactly one必要であり、上のoptional trailing position以外のempty itemをvalidにしない。
`{x,,y}`や`{x,;}`は複数のvalid empty itemではなくmandatory statement-slot recoveryになる。

newlineはdelimiter内なら常にstatement separatorという意味ではない。各`Statement`内の`OperatorChain`がactive
statement baselineより深いcontinuation lineを受理できる場合、そのnewlineはstatement child内に残る。
current statementを終了させてblock ownerへreturnしたcurrent-depth newlineだけを`Gnl`としてcommitする。
matching `}`自身はindentに依存せずbrace ownerが認識する。

### NUD recognition, delimiter scope, and stop ownership

sink-free NUD judgeへ`NudRecognition::BracedStatementBlock { open }`を追加する。fixed punctuation scannerが
current positionのlone `{`を`LBrace`としてrecognizeしたときacceptし、accepted後にcutしてtotal continuationへ
入る。probe rejection時はinput / `ParseLocal`をrollbackし、Rowan sinkへ何も書かない。

brace continuationは次のlocal scopeをpushする。

```text
Delimiter::Brace
StopSet {
    Comma,
    Semicolon,
    RightBrace,
}
ml_arg = false
inline = owner-appropriate bracketed mode
```

このstop frameはincoming outer stopへ単純unionしない。outer if ownerの`Colon` / `Elsif` / `Else`、outer comma、
outer closeなどをbrace内へ漏らさず、matching brace ownerがcurrent delimiter depthのseparator / closeを所有する。
scope exit時にoriginal stop / delimiter / `ml_arg` / `inline` stateをexact restoreする。

`StopKind::Comma`は`{x: 1, y: 2}`に不可欠である。first statementのcolon tailはincoming comma stopを見て一argument
`1`だけをparseし、commaをbrace sequenceへ返す。`StopKind::Semicolon`をstop vocabularyへ追加し、future operator /
ML application scannerがsemicolonをstatement内へ吸収しないようownerを型付けする。`StopKind::RightBrace`はmatching
closeをstatement recoveryから保護する。

string、comment、heredoc、interpolation、rule literal、Yumark、nested delimiter内のcomma / semicolon / newline /
braceはactive lexical-region / delimiter stackが先に所有し、outer brace separatorやcloseへ誤分類しない。

### One shared statement-sequence core

brace-specific statement loopをcopyしない。一方、current `parse_indented_statement_block_with_options`をそのまま
braceから呼ぶこともしない。indent trigger、dedent、non-empty recoveryを名前とcontrolに含むfunctionはbrace ownerの
authorityではないためである。

AST pathとdirect-CST pathのそれぞれで、existing loopから次のshared coreを抽出する。

```rust
enum StatementSequencePolicy {
    Indented {
        block_indent: usize,
        companion_stop: Option<IndentedBlockCompanionStop>,
        owner: StatementRecoveryOwner,
    },
    BracedPrimary {
        close: Delimiter::Brace,
        allow_empty: true,
        allow_trailing_separator: true,
        owner: StatementRecoveryOwner::BracedStatementBlockExpression,
    },
}

struct ParsedStatementSequence<'source> {
    statements: Vec<Recovered<Statement<'source>>>,
}
```

これはpublic abstractionやopen traitではなく、現時点の二ownerを列挙するclosed policyである。shared coreが所有する
責務は次である。

1. canonical `Statement` candidate probe / parse / direct commit。
2. `Recovered<Statement>` collectionとzero-progress guard。
3. maximal invalid episodeの`Error`、missing mandatory statementの`Missing`、same-slot retry。
4. policy-specific separator recognition後の`BlockStatementSeparator` emission。
5. separator後にstatement、valid trailing boundary、またはrecoveryのどれへ進むかという共通state transition。
6. owner-specific recovery roleを受け取り、同じalgorithmから異なるdiagnostic identityをcommitすること。

outer wrapperが所有する責務は次である。

| owner | outer-only responsibility |
| --- | --- |
| `IndentedStatementBlock` | strict indent trigger、block baseline、dedent、if companion stop、non-empty body contract |
| `BracedStatementBlockExpression` | `LBrace` / `RBrace`、empty validity、comma enablement、all trailing separators、closing-delimiter recovery |

separator policyはhard-coded unionにしない。indented ownerはnewline / semicolonだけ、braced-primary ownerはnewline /
semicolon / commaを渡す。comma追加によってindent blockがcomma-separated statement blockへ変わってはならない。
if companion-stop hookはIndented policyにだけ存在し、brace内のordinary `else` / `elsif` wordをouter ifへ返さない。

current helper `commit_indented_block_statement` / `block_statement_error_retry`、AST側statement parse、
`BlockStatementSeparator` emissionをshared responsibilityへrename / factorする。raw statement parser、recovery scanner、
diagnostic creationをbrace用に複製しない。outer node emissionとclosing recoveryだけをbrace continuationへ新設する。

### CST shape and byte ownership

normal two-statement record-looking sourceは次のsurface shapeを持つ。

```text
OperatorChain
  BracedStatementBlockExpression
    LBrace "{"
    Statement
      OperatorChain
        IdentifierExpression "x"
        ColonApplicationTail
          Colon ":"
          Whitespace " "
          OperatorChain
            IntegerLiteral "1"
    BlockStatementSeparator
      Comma ","
      Whitespace " "
    Statement
      OperatorChain
        IdentifierExpression "y"
        ColonApplicationTail
          Colon ":"
          Whitespace " "
          OperatorChain
            IntegerLiteral "2"
    RBrace "}"
```

empty formは次である。

```text
OperatorChain
  BracedStatementBlockExpression
    LBrace "{"
    G*
    RBrace "}"
```

zero statement caseへ`Statement`、`BlockStatementSeparator`、`Missing`を合成しない。newline-only separator nodeは
literal separator tokenを持たず、sourceの`TriviaRun`だけをchildに持つ。comma / semicolon separator nodeは
separator直前の`G0`、literal token、次statement / closeまでのtriviaをsource orderで所有する。

`BracedStatementBlockExpression.range`は`LBrace.start`からmatched `RBrace.end`までである。missing closeでは
insertion pointまでをrangeにし、outer close / next owner safe pointを含めない。nested statement / colon tail /
operator useのrangeをouter blockがsemantic childとして再計算しない。全byteを一回だけemitし、
`green.to_string() == source`を維持する。

`SyntaxKind::BraceGroup`、`RecordLiteral`、`RecordField`、generic `DelimitedBlock`は追加しない。required vocabularyは
次だけである。

```text
SyntaxKind::BracedStatementBlockExpression
SyntaxKind::Statement                  // existing
SyntaxKind::BlockStatementSeparator    // existing; add comma branch
SyntaxKind::LBrace                     // existing
SyntaxKind::RBrace                     // existing
```

### Parser-side AST shape

surface ASTはexisting `Statement`をそのまま保持する。

```rust
pub(crate) enum PrimaryExpression<'source> {
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Parenthesized { /* existing fields */ },
    If(IfExpression<'source>),
    BracedStatementBlock(BracedStatementBlockExpression<'source>),
}

pub(crate) struct BracedStatementBlockExpression<'source> {
    open: Range<usize>,
    // Empty is valid. Incomplete entries correspond one-to-one with CST recovery.
    statements: Vec<Recovered<Statement<'source>>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}
```

comma / semicolon / newline spellingとtrailing positionのlossless authorityはCSTであり、semantic ASTへseparator listを
duplicateしない。formatterやrefactoringがliteral separatorを必要とする場合はCST childを使う。
`close: Recovered<Range<usize>>`はmatched rangeまたはalready-committed missing slotをtyped surface projectionへ
伝える。concrete existing `Recovered<T>`に不足があればequivalentな`DelimiterSlot`へ分けてよい。

各`Statement.expression`はflat `OperatorChain`のままである。pre-HIR associatorがstatementごとにoperator useを
associateし、その後syntax-to-HIR loweringがneutral braced statement sequenceを作る。parser-side ASTも
statement contents、statement count、separator spelling、inferred value typeを見てrecord-specific variantへ変えない。

### `{x: 1}` and semantic interpretation boundary

`{x: 1}`のparseは次のcompositionだけで完結する。

1. `{`が`BracedStatementBlockExpression` NUDを開始する。
2. shared sequence coreが一個の`Statement`を開始する。
3. statementの`OperatorChain`が`IdentifierExpression("x")`を読み、lone colonをterminal
   `ColonApplicationTail`として読む。
4. brace ownerの`StopKind::Comma` / `RightBrace`によりcolon RHSは`1`で終了する。
5. matching `}`がblockを閉じる。

field name、record type、callee arity、brace全体のexpected typeをparserは読まない。`{}`、`{x}`、`{x: 1}`、
`{f: x, y}`はstatement count / literal separator / child operator-chain shapeだけが異なり、outer node kindは常に
`BracedStatementBlockExpression`である。

後段がbraced statement sequenceをblock value、empty record、record-like aggregate、argument sugarなどへinterpretする
規則はfuture HIR / inference designが所有する。何を選んでもsurface CSTを`RecordLiteral`へrename / reshapeせず、
colon tailを`RecordField`へ置換しない。

### Recognition / commit control flow

direct parserのcontrolを次で固定する。

```text
at an operand-required NUD site:
    sink-free probe a fixed LBrace
    if absent: reject and rollback
    accept BracedStatementBlock and cut
    start BracedStatementBlockExpression
    emit LBrace
    push brace delimiter / local stop / ml_arg scopes
    consume and emit opening trivia

    if matching RBrace is current:
        emit RBrace; this is the valid empty form
    else:
        run shared statement-sequence core under BracedPrimary policy
        after each statement:
            if matching RBrace: finish the sequence
            if comma / semicolon / returned newline separator:
                emit one BlockStatementSeparator
                if matching RBrace follows: accept it as valid trailing separator
                otherwise parse or recover the next mandatory Statement
            if another Statement candidate follows without a separator:
                emit one zero-width Missing(separator), then retry that Statement
            otherwise recover one invalid episode to separator / close / next candidate
        commit or recover the mandatory RBrace

    pop every brace-local scope
    finish BracedStatementBlockExpression
    return one completed PrimaryExpression to the enclosing OperandSlot
```

matching close / empty / separator candidate probeはsink-freeである。accepted `{`後はcutし、missing closeやmalformed
statementがあってもouter NUD choiceへrollbackしない。AST-only and direct-CST pathsは同じ boundary / separator /
statement-start recognizerとsame policyを使う。

### Mandatory-slot and closing recovery

新しいrecovery primitiveを作らない。typed vocabularyへbrace ownerだけを追加する。

```text
GrammarRole::BracedStatementBlock(
    BracedStatementBlockRole::{Statement, Separator}
)

GrammarRole::ClosingDelimiter {
    owner: ConstructRole::BracedStatementBlockExpression,
    delimiter: Delimiter::Brace,
}

ExpectedSyntax::Statement
ExpectedSyntax::StatementSeparator
ExpectedSyntax::Punctuation(Close(Delimiter::Brace))
```

`ExpectedSyntax::StatementSeparator`はcomma / semicolon / implicit newlineのtyped expectationを表示層へ渡す
vocabulary extensionであり、recovery mechanismではない。existing `Missing` / `Error`、committed record、
`DiagnosticId`、one node = one diagnostic contractを使う。

代表caseを次で固定する。

| source situation | recovery / ownership |
| --- | --- |
| `{}` / `{ G* }` | valid empty。recoveryなし |
| `{` + EOF | empty bodyはvalidなのでclose用zero-width `Missing('}')`一件だけ。statement `Missing`を作らない |
| `{x` + EOF | statementを保持し、EOFへclose用`Missing('}')`一件 |
| `{x,` + EOF | commaはvalid trailing separator。statement `Missing`を作らずclose用`Missing('}')`一件 |
| `{x,}` / `{x;}` / `{x\n}` | valid trailing separator + normal close。recoveryなし |
| `{x y}`で`y`がseparate statement candidateとして返る | `y`直前へseparator用zero-width `Missing`一件を置き、`y`をnext statementとしてretryする。valid ML applicationなら分割しない |
| `{x,,y}` | first comma後のmandatory statement slotをsecond comma位置でrecoverする。empty statementをvalidにしない |
| `{x,@ y}` | invalid runを一個のnon-empty `Error`にし、same statement slotを`y`からretryする |
| `{x]}` | mismatched `]`をclosing-delimiter roleの一個のnon-empty `Error`にし、matching `}`の探索を続ける |
| `{x` followed by outer/root safe point | boundaryをconsumeせずzero-width close `Missing`を置き、brace nodeを閉じる |
| malformed statement followed by comma / semicolon / returned newline | boundaryをconsumeせずstatement-local `Error` / `Missing`をcommitし、separator loopを続ける |

matching close、separator、outer safe point、EOFはinvalid statement recoveryがconsumeしない。invalid byteを一byteずつ
`Error`へ分割せず、次shared NUD candidateまたはowner boundaryまでのmaximal non-empty episodeにする。
separator直後にmatching `}`があるcaseはgrammar上valid trailing separatorなので、mandatory statement helperを
呼ぶ前にcloseをprobeする。

mismatched `)` / `]`はexisting closing-delimiter ruleどおりactual delimiter evidenceを持つ`Error`としてconsumeし、
同じbrace close slotを続行する。EOF / owner safe pointではmatching braceを合成tokenとして作らず、zero-width
`Missing` nodeだけを置く。all recovery pathでdelimiter / stop / `ml_arg` / inline scopeを一度だけpopする。

associator / HIR loweringは`Recovered<Statement>`とmissing closeをpanic / hangなしでdeterministic error HIRへlowerし、
parser diagnosticを複製しない。

### Existing architecture principlesとの整合

- **NUD-primary placement:** `{`はoperand-required siteでprimaryを開始する。terminal continuation、dynamic operator、
  if brace-body alternativeへroutingしない。
- **single block authority:** canonical Statement parse、recovery、progress、separator state transitionをshared
  statement-sequence coreへ一度だけ置く。indent / brace ownerはtrigger、boundary、allowed separatorsだけを所有する。
- **rollback discipline:** `{` candidate、matching close、separator、statement startをsink-freeにprobeする。open accept後は
  cutし、closing recoveryまでtotal continuationにする。
- **direct CST / no event buffer:** openからclose / missing-closeまでforward-onlyにemitし、completed childをwrap /
  replayしない。source-wide bufferを作らない。
- **precedence-neutral chain:** each statementはflat `OperatorChain`であり、brace parserはnumeric BPを読まない。
  BP-only changeでbrace CST hierarchy、separator、recoveryを変えない。
- **immutable operator table / oracle judge:** statement chainはcanonical table / fixity-role judgeを使う。brace punctuationと
  statement separatorsをdynamic operator tableへ登録しない。
- **stop / delimiter ownership:** local `{Comma, Semicolon, RightBrace}` stopと`Delimiter::Brace`をpushし、outer
  condition / list / close stopをsuspendする。scope stateをin-place mutationして漏らさない。
- **colon composition:** brace-owned commaがgeneric colon tailのinline argument loopを止める。
  `{x: 1, y: 2}`にrecord-field parserやcolon-specific brace exceptionを作らない。
- **lexical-region-aware scanning:** nested literal / comment / interpolation / delimiter内のbrace / separatorをouter
  statement blockへ誤分類しない。
- **mandatory-slot recovery:** zero-width `Missing`、non-empty `Error`、owner safe point unconsumed、one committed node =
  one diagnosticを既存ruleどおり適用する。empty / trailing separatorにrecoveryを作らない。
- **phase boundary:** syntax-to-HIR associatorがstatement chainをassociateする。record / block interpretationやtypeを
  CST shapeへ逆流させない。

### Implementation boundary and required gates

最初の`yu-syntax` implementation sliceは次を含む。

1. `LBrace` NUD recognitionと`PrimaryExpression::BracedStatementBlock`。
2. `SyntaxKind::BracedStatementBlockExpression`とexisting `Statement` / `BlockStatementSeparator` children。
3. local brace delimiter / stop scopeとnew `StopKind::Semicolon`。
4. shared closed-policy statement-sequence coreへのexisting indent loop factoring。
5. brace policyのcomma / semicolon / implicit-newline separators、empty、all trailing separators。
6. typed statement / separator / closing recovery、AST/direct parity、lossless CST fixture。

declaration grammar、if expression-list body、projection record、spread、rule/use/interpolation grammar、HIR semantic
interpretationを同じchangeへ混ぜない。

`yu-syntax` gateを次で固定する。

1. `{}`、`{ }`、`{\n}`がzero `Statement`のvalid `BracedStatementBlockExpression`になる。
2. `{x}`がone `Statement > OperatorChain`を持つ。
3. `{x,y}`、`{x;y}`、`{x\ny}`がtwo statementsとそれぞれcomma / semicolon / newline
   `BlockStatementSeparator`を持つ。
4. `{x,}`、`{x;}`、`{x\n}`がvalid trailing separatorで、`Missing(statement)`を持たない。
5. deeper continuation newlineはcurrent statementに残り、returned current-depth newlineだけがseparatorになる。
6. `{x: 1, y: 2}`でcommaはbrace owner、各colon tailはone inline argument、dedicated record nodeは0である。
7. prefix / suffix / infixの周囲にbrace primaryを置いてもone `Primary` itemとしてouter flat chain orderを保つ。
8. operator BPだけを変えてもgreen CST、surface AST、ranges、recovery、diagnosticsがexact一致する。
9. `{` EOF、statement後EOF、trailing separator後EOF、missing separator、repeated separator、invalid statement、
   mismatched closeをrecovery table通り固定する。
10. nested braces / parentheses / strings / comments内のseparator / closeをouter braceがconsumeしない。
11. all recoveryで`Missing` zero-width、`Error` non-empty、node / diagnostic一対一、balanced scopes / nodes、
    `green.to_string() == source`を満たす。
12. AST-only / direct-CSTのstatement count / ranges / close recoveryが一致し、probe中sink callは0である。
13. existing colon / if indented-block fixturesがshared-core factoring後もbyte-for-byte同じCST / diagnosticsを保つ。
14. historical fixed `ExprSpread` fixtureはこのsliceのacceptance gateに入れず、parser-selected spread CSTを追加しない。

HIR gateは別sliceで次を満たす。

1. each recovered statement chainをcanonical associatorへ一度だけ渡し、surface CSTへtreeを書き戻さない。
2. empty / statement order / ranges / recoveryをneutral braced-block HIRへ保持する。
3. record-like interpretationを追加してもgeneric colon applicationとsurface block CSTを保持する。
4. malformed / unclosed blockをdeterministic error HIRへlowerし、parser diagnosticsを複製しない。

### Explicit future scope

本追補は次を設計しない。

- if / elsif / else brace body。これはstatement blockではなく、comma / semicolon-separated expression listとspreadを
  持つ別grammarであり、`IfArm` / `ElseArm` owner addendumが別node kindを決める。
- projection-record tail `a.{x: y}`。historically上と同じ`ExprListMachine`を使ったが、fixed structural tailの
  target / item / spread ownershipを専用addendumで決める。
- declaration bodyのbrace form。inner shared statement-sequence coreはreuse可能だが、各declaration ownerの
  outer CST node / allowed statement family / recoveryは別addendumが所有する。
- primary blockのfixed `..expr` spread item。Yulang2には存在したが、`Statement`ではないbrace-local item role、
  lowering、recoveryを別途設計するまで追加しない。
- `rule { ... }`のrule-body grammar。
- `use ... { ... }`のuse-spec / import-list grammar。
- `%{...}` string interpolationのvirtual blockとinterpolation close ownership。
- `catch`の`CatchBlock`。`case`にはbrace formを追加しない。
- declaration / pattern / type / Yumarkなど、literal braceを使うその他grammar family。
- block value、empty record、record aggregate、argument sugarなどのHIR / inference interpretation。

historical outer node spellingがすべて`BraceGroup`だったことは、Yulang3でこれらを一nodeへ統合する根拠にしない。
共有してよいのはcanonical scanner / statement-sequence / delimiter recoveryのうち実際に同じ責務だけである。

### Closed decisions and review focus

本追補のimplementation directionをblockするopen questionはない。次を確定する。

- outer CST nameはprimary-only `BracedStatementBlockExpression`である。
- grammarはzero-or-more `Statement`、separatorはcomma / semicolon / returned physical newlineである。
- `{}`とcomma / semicolon / newline trailing separatorはvalidである。
- brace and indent ownersはclosed-policy shared statement-sequence coreを使い、loop / recoveryをduplicateしない。
- brace policyだけがcomma、empty、matching close、all trailing separatorsを有効にする。
- `{x: 1}`はordinary Statement + OperatorChain + ColonApplicationTailでありrecord CSTを持たない。
- historical fixed spread、if expression-list、declaration / rule / use / interpolation bracesは本nodeのownerではない。
- operator associationはpre-HIR、block / record semanticsはlater HIR / inferenceが所有する。

Claude reviewでは、特にexplicit separator後のtriviaとimplicit newlineを二重separatorにしないこと、empty / trailing
separatorをmandatory statement recoveryより先に判定すること、brace-local stop frameがouter if / parenthesized stopを
正しくsuspend / restoreすること、shared-core factoringがexisting indented-block recovery identityを変えないことを
確認対象にする。これらのhelper signatureは調整してよいが、node name、valid separator set、empty / trailing rule、
scope boundaryをopenに戻さない。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定、ユーザ承認済み
（2026-08-22、NUD-primary brace-delimited statement-block expression追補案）。

## 追補案: first-slice pattern grammar

Status: Claude review / exact wordingのfinal sign-off待ち。

Separator-scope status: superseded。`ParenthesizedPattern`のcomma-only grammar / recovery / gatesだけは、末尾の
「layout-aware comma-or-newline delimited sequence」追補へ置き換える。他のprimary / fixed tail / CST / AST決定は維持する。

Date: 2026-08-22。

### Decision summary

Yulang3のpattern grammarを、expression `OperatorChain`とは独立したgrammar familyとして追加する。first sliceは
次のsurface formだけを所有する。

- ordinary identifier / sigil identifier primary。
- decimal integer primary。
- triviaを挟まない`:` + identifierから成るsymbol primary。
- emptyを含むcomma-only parenthesized pattern list。
- fixed keyword `as`によるalias tail。
- fixed token `|`によるalternation tail。

pattern parserはdynamic `OperatorTable`、expression NUD / LED judge、`OperatorChain`、`BpVec`を呼ばない。
patternには宣言またはimport可能なnumeric binding powerがなく、tail precedenceはlanguage grammarに固定される。
ただしprimaryとtailを一個の巨大なad-hoc loopへ混ぜず、pattern専用のsink-free NUD / LED recognitionと
`PatternPrecedence`を持つindependent Pratt familyにする。CSTはleft operandを後からwrapせず、一個の`Pattern`
nodeへhead primaryとsource-order tail nodeをforward-onlyにemitする。recursive operandを持つalternation tailだけが
RHS `Pattern` childを持つ。

この追補はpatternをconsumeするcase / catch arm、binding declaration、function parameterを設計しない。
`parse_pattern` / `parse_direct_pattern`をstandalone fixtureから実行可能にしてgrammar単体を完成させ、各consumerは
自分のaddendumでstop set、delimiter、layout、mandatory slot、outer CST ownershipを追加する。

### Re-verified Yulang2 grammar

Yulang2はexpression parserとは別に`parse_pattern_bp` / `parse_tail_bp`を持つPratt parserだった
(`yulang2-oracle@a58eefc3:crates/parser/src/pat/parse.rs:15-29,44-121,123-268`)。fixed precedence enumは
低い順に`Or`、`As`、`TypeAnn`、`ApplyML`である
(`crates/parser/src/pat/parse.rs:114-121`)。`.field`、`::ident`、no-space callはminimum-precedence guardを持たず、
すべてのrecursive thresholdで認識されるmaximally-tight postfix tailだった
(`crates/parser/src/pat/parse.rs:144-171,233-258`)。したがってfull orderingは次である。

```text
lowest    alternation `|`
           alias `as ident`
           type annotation `: type`
           whitespace ML application
tightest   `.field` / `::ident` / no-space `(pattern, ...)` postfix sequence
```

`|`のRHSは`parse_pattern_bp(Prec::Or, ...)`で再帰するため、`A | B | C`はhistorically right-associated
RHS shapeになる。`as`はpattern全体ではなくnormal `Ident`一個をmandatory RHSに取る
(`crates/parser/src/pat/parse.rs:172-231`)。fixture `A | B as c: Int`はalternation RHS内に`PatAs`と
`TypeAnn`が入ることを示す
(`yulang2-oracle@a58eefc3:crates/parser/tests/pat_grammar.rs:280-304`)。

NUD primaryはnumber、sigil identifier、contextual ordinary identifier、symbol、colon-start form、string / rule、
parenthesized list、list、recordだった
(`crates/parser/src/pat/scan.rs:15-26,61-99,146-174`;
`crates/parser/src/pat/parse.rs:49-108`)。pattern scannerはsigil identifierをordinary wordより先にprobeするため、
`_bar`は`SigilIdent`、bare `_`はsigil scanが完了せずordinary `Ident`になる
(`yulang2-oracle@a58eefc3:crates/parser/src/scan/mod.rs:74-89,110-115,257-260`;
`spec/2026-06-06-syntax-design.md:74-91`;
`crates/parser/tests/pat_grammar.rs:314-325`)。専用wildcard CST nodeはなかった。

contiguous `:foo`はNUD positionで`scan_symbol(..., allow_start = true)`がcolon punctuationより先に
`:` + `ident`を一tokenの`Symbol`としてconsumeする。colonとwordの間にtriviaがある場合、このcomposite scanは
失敗し、単独`Colon`が`PolyVariantStart` routeへ入る
(`yulang2-oracle@a58eefc3:crates/parser/src/scan/mod.rs:140-150`;
`crates/parser/src/pat/scan.rs:73-95,146-155`)。specの記述だけから大文字 / 小文字で分岐すると読んではならず、
actual scanner boundaryは**contiguous compositeかsingle colonか**である。`:leaf x` fixtureはcontiguous symbolが
その後ML argumentを取れたことを示す
(`yulang2-oracle@a58eefc3:crates/parser/tests/pat_grammar.rs:569-583`)。

record patternはcomma / implicit-newline delimited mixed-item grammarだった。itemは`.. pattern`または
`PatField`であり、field headはspecの簡略形`ident`より実装が広い`Ident | SigilIdent`である。実装上のexact
field grammarは次になる
(`yulang2-oracle@a58eefc3:crates/parser/src/pat/parse.rs:296-315,411-508`;
`spec/2026-06-06-syntax-design.md:1532-1551`)。

```text
HistoricalPatRecord :=
    LBrace
    [
        (HistoricalPatField | DotDot Pattern)
        { (Comma | implicit-newline) (HistoricalPatField | DotDot Pattern) }
        [ Comma | implicit-newline ]
    ]
    RBrace

HistoricalPatField :=
    (Identifier | SigilIdentifier)
    [ Colon Pattern [ Equals Expression ]
    | Equals Expression
    ]
```

colon field parsingは`Equals`をpattern stopとしてpushし、optional defaultをexpression parserでparseする。bare
`Equals`も直接expression parserへ切り替える
(`crates/parser/src/pat/parse.rs:471-503`)。fixtures cover sigil shorthand、rename/subpattern、colon + default、
bare default、head/tail spread
(`yulang2-oracle@a58eefc3:crates/parser/tests/pat_grammar.rs:124-276,425-483`)。

以上はsibling investigationのprimary / tail / record summaryを確認する。ただし、postfix三種は独立した
numeric precedence levelsではなくunguarded tight tailsであること、record field headはsigil identifierも許すこと、
symbol / colon-startのactual scanner distinctionはadjacencyであることを補正する。

### Current dependency audit and first-slice boundary

current `yu-syntax`には`IdentifierExpression`、`IntegerLiteral`、`ParenthesizedExpression`、`IfExpression`、
`BracedStatementBlockExpression`とflat dynamic `OperatorChain`があるが、pattern grammar entrypoint / AST / CST nodeは
ない (`crates/yu-syntax/src/grammar/mod.rs`; `crates/yu-syntax/src/syntax_kind.rs:1-82`;
`crates/yu-syntax/src/grammar/expression.rs:135-145,229-252`)。`GrammarRole::Pattern` / `PatternRole`はtyped recovery
vocabularyのplaceholderであり、pattern parserの存在を意味しない
(`crates/yu-syntax/src/session.rs:475-487,574-576`)。

`LBracket` / `RBracket` token scanningと`Delimiter::Bracket`は存在するが、list literal / list patternのitem grammar、
separator recovery、AST / CST ownerは存在しない。opaque lexical-region scannerにstring / rule modeがあっても、
lossless string / rule literal CSTをbuildするgrammarは存在しない。`TypeRole` placeholderはあるがtype-expression parserは
存在しない。これらを「scanner tokenがあるからdependencyが成立済み」と扱わない。

first sliceのin / outを次で固定する。

| form | first slice | rationale |
| --- | --- | --- |
| ordinary / sigil identifier | include | independent primaryとして成立する。binding / constructor / wildcard意味は後段へ送る |
| bare `_` | include as ordinary identifier | dedicated wildcard nodeは作らず、source spellingだけを保持する |
| decimal integer | include | existing integer scanning ruleをgrammar-neutral primitiveとして共有できる |
| contiguous `:foo` symbol | include | existing fixed colon + word scannerから構成でき、pattern NUD ownershipを明示できる |
| parenthesized pattern list | include | existing parenthesis delimiter / recoveryを利用でき、groupingとtuple arityをuniformに保持できる |
| `as ident` | include | fixed tailでmissing dependencyがなく、pattern binding syntaxの最小核になる |
| `| pattern` | include | fixed tailでmissing dependencyがなく、future case / catchに必要なcore compositionである |
| list pattern / spread | defer | bracket tokenだけではitem / spread / comma / close recovery contractが決まらない |
| record pattern / spread / default | defer | statement blockとは別ownerで、mixed pattern / expression field grammarを専用設計する必要がある |
| `: type` annotation | hard defer | type-expression grammarが存在しない |
| string / rule literal pattern | hard defer | literal body CST grammarが存在しない |
| `.field` / `::ident` / no-space call / ML apply | defer | fixed call / ML application infrastructureとconstructor payload boundaryが未設計である |
| non-integer number pattern | defer | current literal grammarはdecimal integerだけで、fraction / exponent surfaceをまだ所有しない |
| spaced colon-start / poly-variant-like pattern | defer | outer colon stopとのownershipとsemantic roleをconsumer-independentにまだ確定できない |

record patternに`BracedStatementBlockExpression`を流用しない。共有候補は`Delimiter::Brace`、closing recovery、trivia、
comma probeだけであり、`StatementSequencePolicy`はrecord field / spread itemをparseするauthorityではない。
record addendumは専用outer nodeとmixed item machineを決める。

constructor clusterのうち`.field` / `::ident`だけをcheap tailとして先行追加する案も採用しない。path / field / call /
ML applicationはconstructor nameとpayload extentを一緒に形づくる。call / ML grammarがない段階で一部だけを固定すると、
後続addendumがtail ordering、no-space boundary、parenthesized payload interpretationを既成事実として背負うためである。

### Grammar

`G*`はnewlineを含み得るmaximal lossless trivia run、`G+`はword tokenを分離するnon-empty trivia runである。
`Colon!Identifier`の`!`は二tokenの間にtriviaもbyte gapもないことを表す。`Pattern@P`はminimum fixed precedence
`P`でのrecursive callを表す。

```text
Pattern := Pattern@Lowest

Pattern@P := PatternPrimary { PatternTail(P) }

PatternTail(P) :=
    G* PatternAliasTail        if P <= Alias
  | G* PatternAlternationTail  if P <= Alternation

PatternAliasTail :=
    AsKw G+ Identifier

PatternAlternationTail :=
    Pipe G* Pattern@Alternation

PatternPrimary :=
    IdentifierPattern
  | IntegerPattern
  | SymbolPattern
  | ParenthesizedPattern

IdentifierPattern :=
    Identifier
  | SigilIdentifier

IntegerPattern := Integer

SymbolPattern := Colon!Identifier

ParenthesizedPattern :=
    LParen G*
    [
        Pattern@Lowest G*
        { Comma G* Pattern@Lowest G* }
        [ Comma G* ]
    ]
    RParen
```

first-slice fixed precedenceは次だけである。

```text
enum PatternPrecedence {
    Lowest = 0,
    Alternation = 1,
    Alias = 2,
}
```

alternation RHSを`Pattern@Alternation`で読むため、`A | B | C`は`A | (B | C)`になる。aliasはalternationより
tightであり、`A | B as c`のaliasはRHS `B`に属する。`A as x | B`ではalias tailをcommitしてからouter
alternation tailを読む。`as`はtail positionだけでcontextual keywordになり、pattern-required NUD positionのbare
`as` spellingはordinary `IdentifierPattern`である。

tail直前の`G*`はtail candidateがacceptされたときだけcommitし、`Pattern`直下のtriviaとしてemitする。
candidateがrejectされた場合はcaller-owned trailing triviaとして返す。`PatternAliasTail` /
`PatternAlternationTail` nodeのrangeとchildrenはliteral `AsKw` / `Pipe`から始まり、先行triviaを取り込まない。
alias前のtriviaは必須ではない。`)as x`や`1as x`のようにpreceding tokenが終わった位置からmaximal word scannerが
exact `as`を読める場合もtailになる。`Aas`は一個のidentifierなのでalias tailへ分割しない。

pipeはpattern-local scannerがexact一文字`|`としてprobeし、`SyntaxKind::Pipe`をemitする。shared
`PunctuationKind`へpipeを追加せず、expression positionの`|`は引き続きdynamic `Operator` spellingである。
pattern sourceの`||`はdynamic operator一個ではなくfixed pipe二個であり、mandatory RHS recoveryを通る。
`as`もshared lexerのunconditional keywordではなく、pattern LED judgeがword textをtail positionでだけclassifyする。
symbol name内の`:as`はordinary `Identifier` childであり`AsKw`にならない。

parenthesized patternはelement countやtrailing commaによってouter node kindを変えない。`()`, `(a)`, `(a,)`,
`(a,b)`, `(a,b,)`はすべて`ParenthesizedPattern`である。zero / grouping / one-tuple / tuple interpretationはfuture
pattern loweringが行う。first sliceのseparatorはcommaだけである。Yulang2のgeneric delimited-list machineは
current-depth implicit newlineもseparatorにした
(`yulang2-oracle@a58eefc3:crates/parser/src/parse/mod.rs:21-23,35-77`;
`crates/parser/tests/pat_grammar.rs:57-77`)が、Yulang3 first sliceへは移植しない。newlineを含むtriviaは保持するが、
次elementとの間にcommaがなければmissing-separator recoveryになる。semicolonもvalid separatorではない。

### Symbol and colon ownership

`SymbolPattern`をsingle combined `Symbol` tokenにしない。CSTはexisting `Colon` tokenと`Identifier` tokenを別々に
保持し、`SyntaxKind::SymbolPattern` parentがadjacent composite roleを表す。これによりfixed punctuation scannerの
token authorityを変更せず、colon application / future type annotationとparent nodeで区別できる。

pattern NUD judgeでは次のpriorityを固定する。

1. current positionから`Colon`と直後の`Identifier`をsink-freeにcomposite probeする。
2. compositeが成立すれば、consumerのactive `StopKind::Colon`があっても一個の`SymbolPattern`としてacceptする。
3. compositeが成立せずactive `StopKind::Colon`があれば、colonをconsumeせずpattern ownerへreturnする。
4. compositeが成立せずcolonがreservedでなければ、malformed symbol primaryとしてcolonをaccept / cutし、adjacent
   identifier slotをrecoverする。

この順序によりfuture arm source `:foo: body`ではfirst `:foo`がpattern、second `:`がarm ownerになる。一方、
missing patternの`: body`ではspaced colonがowner boundaryとして残る。pattern parserはexpression
`recognize_colon_application_tail`を呼ばず、completed pattern後のcolonをcolon applicationへ変換しない。

`scan_pattern_name`はsigil compositeをordinary `scan_word`より先にprobeする。Unicode identifier bodyの規則を
copyせず、shared word-body primitiveを抽出して使う。`$foo`、`&foo`、`'foo`、`_bar`、`__`は
`SigilIdentifier`、bare `_`は`Identifier`になる。CST node名は`IdentifierPattern`のままであり、name resolution前に
binding / constructorを決めない。`_`を`WildcardPattern`へ変えない。wildcard扱いが必要ならHIR pattern loweringが
textとresolved contextから決める。

### CST vocabulary and shape

first sliceで追加するnode / token vocabularyは次である。

```text
SyntaxKind::Pattern
SyntaxKind::IdentifierPattern
SyntaxKind::IntegerPattern
SyntaxKind::SymbolPattern
SyntaxKind::ParenthesizedPattern
SyntaxKind::PatternAliasTail
SyntaxKind::PatternAlternationTail
SyntaxKind::SigilIdentifier
SyntaxKind::Pipe
```

`Identifier`、`Integer`、`Colon`、`Comma`、`LParen`、`RParen`、`AsKw`、trivia、`Missing`、`Error`はexisting kindを
使う。`PatternApplication`、`ConstructorPattern`、`WildcardPattern`、`TuplePattern`、`UnitPattern`、`Symbol` combined
tokenは追加しない。

`A | B as c`のCSTは次になる。

```text
Pattern
  IdentifierPattern
    Identifier "A"
  Whitespace " "
  PatternAlternationTail
    Pipe "|"
    Whitespace " "
    Pattern
      IdentifierPattern
        Identifier "B"
      Whitespace " "
      PatternAliasTail
        AsKw "as"
        Whitespace " "
        Identifier "c"
```

`(:foo, _bar,)`は次になる。

```text
Pattern
  ParenthesizedPattern
    LParen "("
    Pattern
      SymbolPattern
        Colon ":"
        Identifier "foo"
    Comma ","
    Whitespace " "
    Pattern
      IdentifierPattern
        SigilIdentifier "_bar"
    Comma ","
    RParen ")"
```

outer `Pattern`はhead primaryとsource-order tailを持つ。alias tailはalias targetだけ、alternation tailはliteral pipeと
recursive RHS `Pattern`だけを所有する。left primaryをtail nodeのchildへmove / wrapせず、checkpoint rewindやevent
bufferを使わない。全source byteを一度だけemitし、`green.to_string() == source`を維持する。

### Parser-side AST shape

```rust
pub(crate) struct Pattern<'source> {
    head: Recovered<PatternPrimary<'source>>,
    tails: Vec<PatternTail<'source>>,
    range: Range<usize>,
}

pub(crate) enum PatternPrimary<'source> {
    Identifier(PatternNameSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Symbol(SymbolPattern<'source>),
    Parenthesized(ParenthesizedPattern<'source>),
}

pub(crate) struct PatternNameSpan<'source> {
    text: &'source str,
    range: Range<usize>,
    lexical_kind: PatternNameKind,
}

pub(crate) enum PatternNameKind {
    Ordinary,
    Sigil,
}

pub(crate) struct SymbolPattern<'source> {
    colon: Range<usize>,
    name: Recovered<WordSpan<'source>>,
    range: Range<usize>,
}

pub(crate) struct ParenthesizedPattern<'source> {
    open: Range<usize>,
    elements: Vec<Recovered<Pattern<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

pub(crate) enum PatternTail<'source> {
    Alias(PatternAliasTail<'source>),
    Alternation(PatternAlternationTail<'source>),
}

pub(crate) struct PatternAliasTail<'source> {
    keyword: WordSpan<'source>,
    // Historical grammar permits only an ordinary identifier here.
    binding: Recovered<WordSpan<'source>>,
    range: Range<usize>,
}

pub(crate) struct PatternAlternationTail<'source> {
    pipe: Range<usize>,
    rhs: Recovered<Box<Pattern<'source>>>,
    range: Range<usize>,
}
```

`IntegerLiteral`はexpression AST variantをpatternへ埋め込むという意味ではなく、decimal integerのtext / rangeを
表すgrammar-neutral value typeへ移すか共有する。pattern moduleがexpression moduleのprivate parserへ逆依存しない。
separator spellingはCST authorityであり、ASTはterminal commaだけをsemantic disambiguation用に保持する。

ASTもidentifier spellingからbinding、constructor、wildcardを決めない。alias targetだけは`as` grammarが要求する
binding slotというsyntax roleを持つが、そのname resolution / duplicate-binding validationはlater loweringが所有する。

### Entry points and recognition / commit control

pattern moduleは次のentrypointを持つ。

```rust
pub(crate) fn parse_pattern<'source, E>(i: SynIn<'_, 'source, '_, E>)
    -> Option<Pattern<'source>>;

pub(crate) fn parse_direct_pattern<'parse, 'source, 'local, E, O>(
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedPattern<O::Checkpoint>>;

fn parse_pattern_bp(..., minimum: PatternPrecedence, ...);
```

`parse_pattern`は`parse_expression_with_operators`に対応するpattern-family entrypointだが、`OperatorTable` argumentを
取らない。first sliceではconsumerから呼ばず、standalone parser fixtureがroot / caller-provided stop setの両方を
testする。future consumerはleading triviaをemitした後にdirect entrypointを呼び、自分のstop / delimiter scopeを
push / popする。

control flowを次で固定する。

```text
parse_pattern_bp(minimum):
    start Pattern
    sink-free recognize PatternPrimary at an operand-required position
    if accepted:
        cut and commit exactly one primary node
    otherwise:
        recover one mandatory primary slot

    loop:
        apply layout / active-stop boundary before tail judgement
        sink-free recognize a pattern-specific tail

        Alias when minimum <= Alias:
            accept and cut
            emit PatternAliasTail + AsKw
            commit or recover one ordinary Identifier binding

        Alternation when minimum <= Alternation:
            accept and cut
            emit PatternAlternationTail + Pipe
            parse or recover Pattern@Alternation as mandatory RHS

        rejected tail or higher-threshold tail:
            leave it unconsumed and finish this Pattern

    finish Pattern
```

`PatternNudRecognition`はordinary/sigil name、integer、symbol、parenthesizedだけ、`PatternLedRecognition`はalias /
alternationだけを持つ。expression `NudRecognition` / `LedRecognition`へpattern variantを混ぜない。candidate probeは
input / `ParseLocal`をrollbackし、sink / recovery recordへ書かない。primaryまたはtail spellingをacceptした後はcutし、
mandatory child recoveryまでtotal continuationにする。

parenthesized continuationは`Delimiter::Parenthesis`とlocal
`StopSet { Comma, RightParenthesis }`をpushし、incoming outer stopをdelimiter depthの外へsuspendする。elementごとに
`Pattern@Lowest`を呼ぶ。close / comma / next-primary candidateをsink-freeにprobeし、all exit pathでdelimiter / stop /
layout stateをexact restoreする。

### Recovery contract

新しいrecovery mechanismを作らず、typed role vocabularyを具体化する。

```text
PatternRole::{
    Primary,
    SymbolName,
    AliasBinding,
    AlternationRhs,
    ParenthesizedElement,
    ParenthesizedSeparator,
}

ConstructRole::ParenthesizedPattern
ExpectedSyntax::Pattern
ExpectedSyntax::Identifier
ExpectedSyntax::Punctuation(Comma)
ExpectedSyntax::Punctuation(Close(Parenthesis))
```

zero-width `Missing`、maximal non-empty `Error`、one committed recovery node = one diagnostic、owner safe point
unconsumedを既存contractどおり使う。代表caseを次で固定する。

| source situation | recovery / ownership |
| --- | --- |
| empty standalone pattern input | `Pattern > Missing(Primary)`一件。EOFをconsumeしない |
| `@ x` | `@`を一個のnon-empty primary `Error`にし、same slotを`x`からretryする |
| `A as` + EOF | alias tailと`AsKw`を保持し、EOFへzero-width `Missing(AliasBinding)`一件 |
| `A as $x` | sigil runをalias-binding slotのnon-empty `Error`にする。ordinary identifierだけをvalidにする |
| `A |` + EOF | alternation tailとpipeを保持し、nested RHS `Pattern > Missing(Primary)`一件 |
| `A | | B` | second pipe位置へRHS primary `Missing`一件を置き、そのpipeをnested alternation tailとしてconsumeして`B`へ進む |
| `:` + EOF without colon stop | malformed `SymbolPattern`を保持し、colon endへ`Missing(SymbolName)`一件 |
| `: foo` without colon stop | valid symbolにしない。colon + missing adjacent nameを保持し、`foo`をtrailing / caller-owned recoveryへ残す |
| `: body` with active colon stop | pattern primaryをmissingとして記録し、colonとfollowing sourceをconsumerへ返す |
| `:foo: body` with active colon stop | contiguous `:foo`をsymbolとしてconsumeし、second colonをconsumerへ返す |
| `()` | valid zero-element parenthesized pattern。recoveryなし |
| `(a,)` | valid one element + trailing comma。recoveryなし |
| `(,a)` | first comma位置へ`Missing(ParenthesizedElement)`一件を置き、commaを保持して`a`へ進む |
| `(a b)` | `b`直前へ`Missing(ParenthesizedSeparator)`一件を置き、`b`をnext elementとしてretryする |
| `(a` + EOF | elementを保持し、EOFへclose用zero-width `Missing(')')`一件 |
| `(a]` | `]`をclosing-delimiter evidence付きnon-empty `Error`にし、matching `)`探索またはmissing closeへ進む |

`A as`、`A |`、accepted `(`、unreserved malformed `:`は別NUD / tail alternativeへrollbackしない。alias binding、
comma、matching close、active outer stop、EOFはinvalid-run recoveryがconsumeしない。同じbyteへ複数helperが
duplicate diagnosticを作らず、standalone rootのtrailing input recoveryとpattern-local mandatory recoveryを
`GrammarRole`で区別する。

first sliceにtype annotationがないため、standalone `x: Int`のcolonはvalid pattern tailではない。callerが
`StopKind::Colon`をreserveしていればcolonを返し、reserveしていなければstandalone trailing-input recoveryが扱う。
pattern parserがcolon RHSをexpressionまたはtypeとして推測してはならない。

### Existing architecture principlesとの整合

- **independent grammar authority:** pattern NUD / LEDとfixed precedenceはpattern moduleだけが所有する。
  expression `OperatorChain`へpattern-specific itemを追加しない。
- **precedence-neutral dynamic operators:** headerのnumeric BP変更でpattern CST / AST / diagnosticsは変わらない。
  patternのfixed orderingはdeclared operator dataではなくliteral grammar ruleである。
- **no `BpVec`:** `BpVec` / associatorはdynamic expression chain専用であり、three-value `PatternPrecedence`へ流用しない。
- **immutable operator table:** pattern entrypointはtableを受け取らない。pattern内の`|`をoperator declarationで
  shadow / rebindしない。
- **oracle judge separation:** expression oracle judge tableは使わない。patternはsmall fixed
  `PatternNudRecognition` / `PatternLedRecognition` tableを持つ。
- **rollback discipline:** sigil/name、symbol composite、parenthesis、`as`、pipeをsink-freeにprobeし、accept後だけcut / emitする。
- **direct CST:** outer `Pattern`を先にstartし、primary、tail、recursive RHSをsource orderにemitする。left wrapping、
  completed-child replay、source-wide event bufferを要求しない。
- **lexical-region awareness:** future literal / comment / nested delimiter内のcolon / pipe / commaをouter pattern tokenへ
  誤分類しない。current embedded-mode stackをscanner authorityとして維持する。
- **stop ownership:** contiguous symbol compositeだけがNUD positionでcolon stopより優先され、single colonはownerへ返る。
  parenthesized local stopsはscope exit時にexact restoreする。
- **mandatory-slot recovery:** accepted syntaxのrequired childを`Missing` / `Error`でtotalに閉じ、parser diagnosticをlater
  pattern loweringが複製しない。
- **semantic deferral:** identifier / `_` / uppercase spellingを見てbinding、wildcard、constructorをCSTで選ばない。
  parenthesized arityのunit / grouping / tuple interpretationもloweringへ送る。

### Standalone boundary and non-consumer status

本追補のimplementationが完了しても、source rootのstatement parser、`my` declaration、function parameter、case / catch
armからpattern entrypointを呼ばない。fixture harnessだけが`parse_pattern` / `parse_direct_pattern`を直接実行する。

consumer wiringは単なるfunction call追加ではない。各ownerは少なくとも次を自分のaddendumで決める必要がある。

- pattern前後のkeyword / delimiter / colon / arrow / guard stop。
- current base indentとarm / parameter continuation rule。
- missing patternがowner delimiterをconsumeしないrecovery boundary。
- outer CST nodeとpattern child arity。
- pattern loweringへ渡すscrutinee / binding scope。

このため、本追補のtest fixtureにcase / catch風wrapper sourceを入れてconsumer grammarを先取りしない。

### Implementation boundary and required gates

first `yu-syntax` pattern sliceは次を含む。

1. new `grammar/pattern.rs` entrypoint、AST-only / direct-CST parity、standalone fixture harness。
2. `PatternPrecedence::{Lowest, Alternation, Alias}`とpattern-only NUD / LED recognition。
3. pattern-specific ordinary / sigil name scanner。shared Unicode word bodyをcopyせずreuseする。
4. grammar-neutral decimal integer literal scanner / valueのreuse。
5. contiguous symbol compositeとactive colon-stop priority。
6. comma-only uniform `ParenthesizedPattern`、empty / trailing comma、closing recovery。
7. alias / alternation tailsとtyped mandatory-slot recovery。
8. required `SyntaxKind` / `GrammarRole` / `ExpectedSyntax` vocabulary。

implementation gateを次で固定する。

1. `x`、`_`が`IdentifierPattern > Identifier`、`_bar`、`$x`、`&x`、`'x`が
   `IdentifierPattern > SigilIdentifier`になる。`WildcardPattern`は0件である。
2. `0`、`42`が`IntegerPattern > Integer`になり、expression `OperatorChain` nodeを持たない。
3. `:foo`が`SymbolPattern(Colon, Identifier)`になり、combined `Symbol` tokenと`ColonApplicationTail`は0件である。
4. active colon stop下の`:foo: body`はfirst compositeだけをconsumeし、second colonを返す。`: body`はfirst colonを返す。
5. `()`、`(a)`、`(a,)`、`(a,b)`、`(a,b,)`がone uniform `ParenthesizedPattern` kindとexact element count /
   trailing-comma markerを持つ。
6. `(a\nb)`はimplicit newline separatorとしてvalidにせず、missing comma recoveryになる。
7. `A as x`、`A as x as y`がsource-order alias tailsを持ち、alias RHSはordinary identifierだけを受理する。
8. `A | B as c`、`A as x | B`、`A | B | C`がfixed precedence / right-recursive RHS shapeを満たす。
9. operator headerの`|` spelling / fixity / BPを変えてもpattern CST、AST、ranges、recovery、diagnosticsがexact一致する。
10. EOF primary、unknown primary、missing alias binding、missing alternation RHS、leading/repeated comma、missing separator、
    missing/mismatched closeをrecovery tableどおり固定する。
11. all probesでsink call 0、accepted primary / tail emission一回、all delimiter / stop scopes balanced、
    `green.to_string() == source`を満たす。
12. AST-only / direct-CST pathのprimary kind、tail order、element count、ranges、recoveryが一致する。
13. `[a]`、`{a}`、`"a"`、`x: T`、`A::B`、`A.field`、`Some(x)`、`Some x`をexcluded formとして
    accidental valid first-slice patternへ取り込まない。
14. existing expression / colon / if / braced-block testsのCST / diagnosticをpattern vocabulary追加前後で維持する。
15. production statement / declaration entrypointからpattern parserへのcall siteは0件である。

### Explicit future scope

本追補は次を設計または実装しない。

- case / catch grammar、arm、guard、body、companion continuation、scrutinee ownership。
- `my` / other binding declaration、function / lambda parameter、loop binderなどpattern consumer wiring。
- list pattern `[pattern | ..pattern, ...]`、bracket item / spread / separator / closing recovery。
- record pattern、sigil shorthand field、`name: pattern (= expr)?`、`name = expr`、`..pattern`。
- pattern type annotation `: Type`と全type-expression grammar。
- normal quote rule pattern、explicit rule literal、heredoc string pattern、`rule { ... }` pattern。
- field projection `.field`、qualified path `::ident`、no-space constructor call、whitespace ML application。
- constructor resolution、payload arity、parenthesized payload expansion、scrutinee type constraint。
- decimal integer以外のfraction / exponent / other numeric literal pattern。
- spaced single-colon `PolyVariantStart` formとpoly-variant pattern semantics。
- implicit-newline parenthesized separatorとsemicolon-separated parenthesized pattern。
- wildcard semantics、duplicate binding validation、or-pattern binding-set equality、alias scope、exhaustiveness。
- pattern HIR / typed pattern lowering。first sliceはsurface AST / CSTまでである。

future tail addendumはfixed order `Alternation < Alias < TypeAnnotation < MlApplication < tight postfix`を再検証し、
`PatternPrecedence`へ必要なlevelだけを追加する。dynamic expression BPや`OperatorChain`へ移行しない。record / list
addendumはdelimiter scannerを共有してよいが、`BracedStatementBlockExpression` / `StatementSequencePolicy`をpattern
containerとしてreuseしない。

### Closed decisions and review focus

本追補のimplementation directionをblockするopen questionはない。次を確定する。

- first sliceはidentifier / sigil、integer、contiguous symbol、comma-only parens、alias、alternationである。
- `_`はordinary identifierであり、`_bar`はsigil identifierである。
- patternはindependent fixed-precedence Pratt familyであり、expression operator machineryを使わない。
- alternationはaliasよりlooseで、same-precedence RHS recursionはright-associated shapeを作る。
- symbolはtwo tokens under one `SymbolPattern` nodeであり、adjacencyとNUD positionでcolon ownershipを決める。
- parenthesized patternはelement count / trailing commaに依存せずone node kindを使う。
- pattern parserはstandaloneで完成させ、consumerへまだwireしない。
- missing dependenciesとconstructor / record shape decisionsをfirst sliceへstubで入れない。

Claude reviewでは、特に`_bar`をordinary `scan_word`が先取りしないscanner order、active colon stopとcontiguous
symbol compositeのpriority、`A | | B`のsame-position recovery、parenthesized newlineをvalid separatorへ昇格しないこと、
future type / ML / postfix levelを追加できるPratt threshold、standalone trailing recoveryとcaller stopの分離を確認対象に
する。helper名やAST range carrierはcurrent source型に合わせて調整してよいが、scope、CST vocabulary、precedence、
colon ownership、consumer非接続をopenに戻さない。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定、ユーザ承認済み
（2026-08-22、first-slice pattern grammar追補案）。

## 追補案: NUD-primary `case` / `catch` expression grammar

Status: Claude review / exact wordingのfinal sign-off待ち。

Date: 2026-08-22。

### Decision summary

Yulang3のfirst `case` / `catch` sliceを、standalone pattern grammarの最初のconsumerとして追加する。両者は
`IfExpression`と同じNUD-position `PrimaryExpression`であり、dynamic operator chainの
`TerminalOuterContinuation`ではない。したがって`case` / `catch` expression全体が一個の`OperandSlot::Value`となり、
その外側へprefix / infix / suffix useをsource orderのまま接続できる。

first sliceはnormal expression formの`case`と`catch`を同時に所有し、次を含む。

- optional apostrophe-sigil label。
- mandatory scrutinee `OperatorChain`。
- colon-inline arm sequenceとcolon-indented arm block。
- `case`のcomma-separated inline multiple arms。
- `catch`のinline exactly-one arm、indented multiple arms、専用brace arm block。
- arm-local `if` / `where` guard。
- `catch` armのoptional second full `Pattern`（handler pattern）。
- inlineまたはdeeper-indented statement blockを取るmandatory arrow body。

`case`と`catch`を別sliceへ分けない。outer node名と許可surfaceは異なるが、keyword / label / scrutinee / block、
pattern / guard / arrow / bodyというcommit skeleton、fixed arm boundary、layout判定、recovery authorityを共有する。
片方だけを先行すると、もう片方の既知の差分を無視したboolean-driven helperが先に事実化するためである。実装は
任意のboolean組合せを持つconfigではなく、closed `CaseLikeFamily::{Case, Catch}`からfamily固有policyとnode kindを
導出する。

このsliceでarmが受理できるpatternは、commit `4ec436cc`のstandalone first slice、すなわちidentifier / sigil
identifier、integer、contiguous symbol、comma-only parenthesized pattern、`as` alias、`|` alternationだけである。
list / record / type annotation / string・rule / constructor call・ML application patternをcase側でstub実装しない。

### Re-verified Yulang2 grammar and deliberate Yulang3 boundary

Yulang2では`CaseLikeConfig`がexpression / block / arm / guard node kindと、handler、inline-list、brace-blockの許可を
parameterizeし、一個の`parse_case_like_expr` / `parse_arm`を共有していた
(`yulang2-oracle@a58eefc3:crates/parser/src/expr/control.rs:523-531,573-630,814-939`)。actual configは
`case = { handler: false, inline-list: true, brace: false }`、
`catch = { handler: true, inline-list: false, brace: true }`だった
(`crates/parser/src/expr/control.rs:549-570`)。optional labelはapostropheで始まる`SigilIdent`一個であり、
scrutineeの前に直接emitされた
(`crates/parser/src/expr/control.rs:633-648`;
`crates/parser/tests/expr_grammar.rs:1618-1655`)。

scrutinee parserは両familyで`Colon`をlocal stopにし、brace blockを所有する`catch`だけ`BraceL`もstopにした。
`case x { ... }`のbraceはcase block introducerではなくscrutinee側へ残す、という差は実装とspecの両方に明記される
(`crates/parser/src/expr/control.rs:584-620`;
`spec/2026-06-06-syntax-design.md:1181-1184`)。Yulang3もこの非対称を維持する。

colon後のYulang2 layoutは、deeper newlineなら複数armのindent machine、inlineなら`case`だけcomma list、`catch`は
一armだけだった。catchだけは専用brace arm listも持った
(`crates/parser/src/expr/control.rs:689-812`;
`spec/2026-06-06-syntax-design.md:1181-1215`)。catch braceはgeneric statement blockではなく、
`CatchBlock`が`BraceL` / arm / separator / `BraceR`を直接所有する。Yulang3の
`BracedStatementBlockExpression`へrouteしない。

arm parserはpatternへ`Arrow` / `If` / `Where`、catch first patternだけ`Comma`をlocal stopとして与え、catchの
comma後もidentifier限定ではなく二個目のfull `Pattern`を呼んでいた。guardは`if`または`where`の後をnormal
expressionとして読み、`Arrow`で止めた
(`crates/parser/src/expr/control.rs:823-915`)。guard fixtureとhandler fixtureもこのshapeを固定する
(`crates/parser/tests/expr_grammar.rs:1865-1910,2143-2200`;
`crates/parser/tests/stmt_grammar.rs:2906-2914`)。Yulang3もhandlerをnameへ狭めず、current first-sliceで表現可能な
full `Pattern`とする。

arrow後のbodyはcase-like専用block parserではなく、generic colon applicationとif/elseも使った同じ
`parse_inline_or_indent`へ渡された。plain inlineは一expression、physical newline後のindentがcurrent arm lineより
deepならshared statement blockだった
(`crates/parser/src/expr/control.rs:22-35,917-926`)。したがってYulang3のindented arm bodyも
single-expression special nodeではなくexisting `IndentedStatementBlock`である。Yulang2はbody直後のoptional `;`を
arm自身の末尾でconsumeした (`crates/parser/src/expr/control.rs:928-935`)。この`;`はarm-list separatorではない、という
ownershipも維持する。

historical fixturesはcase inline / indented、guard、label、catch handlerをcoverする
(`crates/parser/tests/expr_grammar.rs:1788-1910,1618-1655,2143-2200`)。tag時点にcatch brace fixtureはないため、
そのformのhistorical evidenceはimplementationとspecでありtest evidenceではない、と区別する。

Yulang3はYulang2のevent shapeを無条件に復元しない。expression bodyはprecedence-shaped treeではなくflat
`OperatorChain`であり、patternはcommit `4ec436cc`のfixed-precedence surface CSTである。またarm sequenceは
statement sequenceではない。この追補が共有するのはverified surface boundaryとlayout primitiveであり、旧parserの
backtracking / event protocolではない。

### Architectural placement: two NUD primaries

expression NUD recognitionへ次を追加する。

```rust
enum NudRecognition<'source> {
    // existing variants ...
    Case {
        keyword: WordSpan<'source>,
        base_indent: usize,
    },
    Catch {
        keyword: WordSpan<'source>,
        base_indent: usize,
    },
}
```

`case` / `catch`はmaximal word scanのexact textが一致するときだけcontextual keywordになる。`casefold`、`catcher`は
ordinary identifierである。probe orderはfixed structural primaryをdynamic prefix / nullfix operatorより先に置く
existing `if` precedentに合わせ、accept前はsink-free、accept後にcutしてそれぞれ`CaseExpression` /
`CatchExpression`をcommitする。

```text
PrimaryExpression += CaseExpression | CatchExpression

CaseExpression  := CaseKw  CaseLikeHead CaseBlock
CatchExpression := CatchKw CaseLikeHead CatchBlock

CaseLikeHead := G* [ CaseLikeLabel G* ] Scrutinee G0*
CaseLikeLabel := Apostrophe!Identifier
Scrutinee := OperatorChain
```

`CaseLikeLabel`の`!`はapostropheとidentifier bodyの間にtriviaもbyte gapもないことを表す。scannerは一個のmaximal
apostrophe-sigil spellingを`SigilIdentifier` tokenとしてemitする。labelとscrutineeの間にgrammar上のmandatory triviaは
置かない。ordinary wordが続く場合はmaximal sigil scan自身がseparatorを要求し、`case 'go(4): ...`のように次primaryが
punctuationから始まる場合はadjacentでもboundaryが成立する。labelがない`case(`も同じword-boundary ruleで成立する。
optional probeがapostrophe-sigil compositeをacceptしなければbyteをconsumeしない。

`case` / `catch`全体は`PrimaryExpression`なのでparenthesized element、if body、colon-application argument、braced
statement block内のexpression statementとして使える。逆にouter expressionのlone colonは、case-like nodeのcommitが
完了してcontrolが`OperatorChain`へ戻った後にだけ`ColonApplicationTail`候補になり得る。case / catch内部のblock
introducer colonはouter tailではない。

### First-slice grammar

`G*`はnewlineを含み得るmaximal lossless trivia run、`G0*`はcurrent inline regionから出ないtrivia runである。
`LineBreak(indent)`はopaque lexical region外のphysical newlineとその後のindentを表す。`ArmIndent`はcolonを含む
case-like introducer lineよりstrictly deepな、最初のarmのindentである。`BodyIndent`はarrowのあるarm lineより
strictly deepである。

```text
CaseExpression :=
    CaseKw G* [ CaseLabel G* ] CaseScrutinee G0* CaseBlock

CatchExpression :=
    CatchKw G* [ CatchLabel G* ] CatchScrutinee G0* CatchBlock

CaseLabel  := Apostrophe!Identifier
CatchLabel := Apostrophe!Identifier

CaseScrutinee  := OperatorChain  // local stop: Colon
CatchScrutinee := OperatorChain  // local stops: Colon, LBrace

CaseBlock :=
    Colon (
        CaseInlineArmSequence
      | CaseIndentedArmSequence
    )

CatchBlock :=
    Colon (
        CatchInlineArmSequence
      | CatchIndentedArmSequence
    )
  | LBrace G* CatchBracedArmSequence G* RBrace

CaseInlineArmSequence :=
    G0* CaseArm { G0* Comma G0* CaseArm } [ G0* Comma ]

CatchInlineArmSequence :=
    G0* CatchArm

CaseIndentedArmSequence :=
    LineBreak(ArmIndent > case-base-indent)
    CaseArm
    { ArmSeparator CaseArm }
    [ G0* Comma ]

CatchIndentedArmSequence :=
    LineBreak(ArmIndent > catch-base-indent)
    CatchArm
    { ArmSeparator CatchArm }
    [ G0* Comma ]

CatchBracedArmSequence :=
    CatchArm
    { CatchBracedArmSeparator CatchArm }
    [ G0* Comma ]

CatchBracedArmSeparator :=
    G0* Comma G*
  | PhysicalNewlineAtCurrentBraceDepth

ArmSeparator :=
    PhysicalNewline(next-indent = ArmIndent)
  | G0* Comma G*

CaseArm :=
    Pattern [ ArmGuard ] ArmArrow ArmBody [ Semicolon ]

CatchArm :=
    Pattern [ G0* Comma G0* Pattern ] [ ArmGuard ] ArmArrow ArmBody [ Semicolon ]

ArmGuard :=
    G0* (IfKw | WhereKw) G0* GuardExpression

GuardExpression := OperatorChain  // local stop: Arrow

ArmArrow := G0* Arrow

ArmBody :=
    InlineArmBody
  | IndentedArmBody

InlineArmBody := G0* OperatorChain

IndentedArmBody :=
    LineBreak(BodyIndent > arm-line-indent)
    IndentedStatementBlock
```

すべてのblock formは少なくとも一armを要求する。`catch x {}`はempty valid valueではなく、`CatchBlock`内のmandatory
`CatchArm`を`Missing` recoveryする。これはYulang2 brace loopがcloseを見つける前にdegenerate arm parseへ入れたかどうかを
surface validityの根拠にしない、Yulang3の明示的なnon-empty contractである。

commaを所有する三policy、すなわちcase inline、case/catch indented、catch braceはnatural boundary直前の一個の
trailing commaをvalid source markerとして保持する。comma後に同じregionのpattern NUD candidateがあれば次armを読む。
boundaryならtrailing separator、candidateでもboundaryでもなければmandatory next-arm recoveryへ入る。catch inlineは
arm-list commaを一切所有しない。したがってcatch inline arm body内のgeneric colon applicationは、自身のinline argument
commaを通常どおり所有できる。

このtrailing-comma ruleはYulang3でlist policyをuniformにする明示的な決定である。Yulang2 case-inline loopもcomma直後が
physical newlineなら次armを要求せず終了した
(`yulang2-oracle@a58eefc3:crates/parser/src/expr/control.rs:706-724`)が、EOF / dedent / brace closeを横断する一個の
明文化されたcontractではなかった。Yulang3は各policyのnatural boundaryを先に判定し、CSTへliteral commaを残す。

semicolonは`CaseArm` / `CatchArm`のoptional terminal tokenであり、`CaseArmSeparator` /
`CatchArmSeparator` nodeへ入れない。inline caseでsemicolonをconsumeしたarmはそのinline sequenceを終了する。
indented / braced regionでは後続layoutまたはcommaが次armを開始できるが、semicolon単独をarm separatorとして扱わない。
Yulang2はsemicolon consume後に`Either::Left`をouter loopへ返したため、ownerによってはそのまま次armへ進める余地が
あった。このcontrol-flow side effectはYulang3へ移植しない。next-arm validityはclosed sequence policyだけが決め、
semicolonの有無から暗黙に導出しない。

### Scrutinee, pattern, guard, and arrow boundaries

case-like ownerはscrutinee parse直前にcaller stop frameをpushする。

```text
case  scrutinee stops  = outer stops + Colon
catch scrutinee stops  = outer stops + Colon + LeftBrace
```

fixed compositeをdynamic continuationより先に判定する。`StopKind::Colon`によりblock introducerは
`ColonApplicationTail`へ入らない。`catch`の`StopKind::LeftBrace`によりbraceは
`BracedStatementBlockExpression` NUDやfuture ML argumentへ入らず`CatchBlock`が所有する。`case`はLeftBrace stopを
pushしない。current first sliceにML applicationがまだなく`case x { ... }`全体をhistorical形でparseできない場合でも、
case grammarがbraceを先取りしてはならない。future fixed tail / ML addendumがscrutinee側を拡張できるboundaryを保つ。

arm first patternのstop frameは次である。

```text
case  first-pattern stops  = outer + Arrow + ArmGuardIf + ArmGuardWhere
catch first-pattern stops  = outer + Arrow + ArmGuardIf + ArmGuardWhere + Comma
catch handler-pattern stops = outer + Arrow + ArmGuardIf + ArmGuardWhere
guard-expression stops      = outer + Arrow
```

`ArmGuardIf` / `ArmGuardWhere`はword spellingのcontextual stop roleであり、global lexer keywordではない。completed
pattern直後のmaximal wordがexact `if` / `where`のときだけarm ownerがguardを開始する。`if`はここでは
`IfExpression` NUDではない。guard nodeの中へ`IfKw`または`WhereKw`をemitし、その後のnormal `OperatorChain`だけを
`Arrow`まで読む。delimiter / opaque lexical regionへ入ればouter arrow stopはsuspendされる。

current `StopKind`には`Arrow` / guard-word stopがなく、pattern mandatory-primary recoveryも`) ] } , ;`とactive colon
だけをpreserveする
(`crates/yu-syntax/src/session.rs:342-370`;
`crates/yu-syntax/src/grammar/pattern.rs:357-383,414-456`)。implementation sliceは
`StopKind::Arrow`、`StopKind::ArmGuardIf`、`StopKind::ArmGuardWhere`を追加し、expressionとpatternのrecognition / recoveryが
これらをconsumeしないよう拡張する。`Comma`は既存stopを使う。名前をplain `If` / `Where`にせずarm-local roleを表すのは、
future consumerが同じword spellingへ別boundary semanticsを与えてもstop authorityを混ぜないためである。

`->`はscanner-layerでは現在dynamic-operator territoryである
(`crates/yu-syntax/src/scan/punctuation.rs:54-58,159-166`)。arm grammarはshared fixed punctuation setへ無条件追加せず、
arm boundaryでだけmaximal operator-shaped tokenをsink-freeにscanし、textがexact `->`なら`SyntaxKind::Arrow`として
acceptする。`->>`を`->` + `>`へsplitしない。operator declarationに`->`が存在するか、そのbinding powerが何かは
arm separatorの認識へ影響しない。nested delimiter内またはguard / bodyのordinary expression regionでは、active arm
stopがsuspendされる限り`->`は通常のdynamic operator spellingであり得る。

pattern parserはcommit `4ec436cc`で`parse_pattern`と`parse_direct_pattern`をstandalone公開し、まだconsumerを持たない
(`crates/yu-syntax/src/grammar/pattern.rs:148-173`)。この追補は「consumerへwireしない」という前slice固有gateだけを
supersedeする。patternのindependent fixed-precedence family、surface shape、colon-composite priorityは変更しない。
とくにactive colon stop下でもcontiguous `:foo` compositeを先にrecognizeするため、arm source `:foo -> body`をsymbol
patternとして読める。

### Arm body layout and shared body authority

arrowをconsumeした時点で、そのarrowがあるphysical lineのindentを`arm-line-indent`としてcaptureする。直後のmaximal
triviaにphysical newlineがなければinline body、newlineがありnext line indentが`arm-line-indent`よりstrictly deepなら
indented body、same / shallowerならmissing bodyかつ次arm / outer boundaryである。この判定はcolon applicationと
if/elseが使うcurrent `recognize_post_colon_body_layout`
(`crates/yu-syntax/src/grammar/expression.rs:807-833`)と同じprimitiveである。

primitiveはcolonをinspectせず、すでにintroducer tokenをconsumeした後のtriviaとbase indentだけを見る。case/catch
sliceではこれを`recognize_introduced_body_layout`（または同等のneutral name）へrenameし、colon application、if/else
colon body、case/catch arrow bodyから共有する。owner-specific wrapperは共有しない。

- colon application wrapperはinline comma argument listまたはindented statement blockを所有する。
- if/else wrapperはinline one expressionまたはcompanion-aware indented statement blockを所有する。
- case/catch arm wrapperはinline one `OperatorChain`またはdefault-policy `IndentedStatementBlock`を所有する。

case/catchのindented arm bodyはexisting statement-loop coreと`StatementSequencePolicy::Indented`をそのまま使う
(`crates/yu-syntax/src/grammar/expression.rs:1170-1259`)。`IfExpression`の`elsif` / `else` companion-stop optionは使わない。
arm-listの次armはbody blockからのdedentでownerへ返り、arm-sequence policyが読む。body内statementのnewline /
semicolonとarm間newline / commaは別authorityである。

inline bodyへ与えるstopはarm-sequence policyが決める。

| owner | inline body local stops | rationale |
| --- | --- | --- |
| case inline | `Comma` + `Semicolon` + natural line boundary | commaは次case arm、semicolonはcurrent arm terminalを開始する |
| catch inline | `Semicolon` + natural line boundary | inline catchは一arm。commaをbody側から奪わない |
| case/catch indented arm | `Comma` + `Semicolon` + arm-indent boundary | explicit comma、arm terminal、dedent/newlineをbodyから守る |
| catch brace | `Comma` + `Semicolon` + `RightBrace` + current-depth newline | brace separator / arm terminal / closeをbodyから守る |

bodyはinlineでもexactly one `OperatorChain`であり、generic colon application's `InlineExprList`をarm grammarが複製しない。
`a -> f: x, y`のcomma ownershipは上表のouter arm policyに従う。複数colon argumentを一arm body内へ確実に入れたい場合は
parenthesizeするかindented bodyを使う。parserはbodyの意味、guard truth、pattern coverageを判定しない。
indented body内部のsemicolonはexisting statement sequenceが所有する。arm-terminal semicolonは、そのblockがdedentで
完了してarm ownerへ戻った後の同一arm regionに現れるtokenだけである。

### Dedicated arm-sequence core

armは`Statement`ではない。pattern、optional handler、optional guard、fixed arrow、bodyを持つため、
`StatementSequencePolicy`や`Statement` nodeへ通さない。一方、このsliceにはすでにcase inline、shared indented、catch
inline-single、catch braceという複数のconcrete ownerがあるため、layoutごとにloopをcopyせず、closed arm-sequence
policyを一個導入する。

```rust
enum CaseLikeFamily {
    Case,
    Catch,
}

enum ArmSequencePolicy {
    CaseInline,
    CatchInlineSingle,
    Indented {
        family: CaseLikeFamily,
        base_indent: usize,
        arm_indent: usize,
    },
    CatchBraced,
}
```

`CaseLikeFamily`はnode kind、scrutinee stops、handler許可、block introducer許可をclosed methodで返す。
`ArmSequencePolicy`はseparator recognition、terminal boundary、body stop、trailing-comma ownershipだけを返す。
arm parser自体はfamilyを受けてCase/Catch nodeとoptional handler slotを選ぶ。`allow_handler_name` /
`allow_inline_list` / `allow_brace_block`の独立booleanを公開せず、存在しない組合せを表現不能にする。

sequence coreはsource-orderに次を行う。

```text
parse_arm_sequence(policy):
    recognize policy-owned empty/terminal boundary
    recover mandatory first arm if boundary is immediate

    loop:
        parse exactly one family arm
        if policy terminal boundary:
            finish
        if explicit comma:
            emit family-specific ArmSeparator
            if terminal boundary:
                record trailing comma and finish
            parse next arm
        else if indented policy and next arm starts at arm-indent after newline:
            retain newline as lossless trivia and parse next arm
        else if CatchBraced and a current-depth newline is followed by another arm:
            retain newline as lossless trivia and parse next arm
        else if next Pattern NUD candidate exists in the same region:
            emit Missing separator and retry one arm
        else:
            finish or recover to the nearest policy safe point
```

newline-only separation does not require a synthetic separator token; physical newline trivia remains in source order between arm nodes。
explicit comma is wrapped in`SyntaxKind::CaseArmSeparator`または`SyntaxKind::CatchArmSeparator`。catch handler comma is
direct child of`CatchArm`でありseparator nodeではない。same spellingのroleをparent shapeで区別する。

### CST vocabulary and direct shape

first sliceは次を追加する。

```text
SyntaxKind::CaseExpression
SyntaxKind::CatchExpression
SyntaxKind::CaseLabel
SyntaxKind::CatchLabel
SyntaxKind::CaseScrutinee
SyntaxKind::CatchScrutinee
SyntaxKind::CaseBlock
SyntaxKind::CatchBlock
SyntaxKind::CaseArm
SyntaxKind::CatchArm
SyntaxKind::CaseGuard
SyntaxKind::CatchGuard
SyntaxKind::CaseArmSeparator
SyntaxKind::CatchArmSeparator

SyntaxKind::CaseKw
SyntaxKind::CatchKw
SyntaxKind::WhereKw
SyntaxKind::Arrow
```

`IfKw`、`SigilIdentifier`、`Colon`、`Comma`、`Semicolon`、`LBrace`、`RBrace`、`Pattern`、`OperatorChain`、
`IndentedStatementBlock`、trivia、`Missing`、`Error`はexisting kindを使う。`CaseLikeExpression`、generic `Arm`、generic
`Guard`、`ColonApplicationTail`、`BracedStatementBlockExpression`をcase/catch nodeの代用にしない。

`case 'go x: 1 if ok -> yes, _ -> no`のoutlineは次になる。

```text
CaseExpression
  CaseKw "case"
  Whitespace " "
  CaseLabel
    SigilIdentifier "'go"
  Whitespace " "
  CaseScrutinee
    OperatorChain
      IdentifierExpression "x"
  CaseBlock
    Colon ":"
    Whitespace " "
    CaseArm
      Pattern
        IntegerPattern "1"
      Whitespace " "
      CaseGuard
        IfKw "if"
        Whitespace " "
        OperatorChain
          IdentifierExpression "ok"
      Whitespace " "
      Arrow "->"
      Whitespace " "
      OperatorChain
        IdentifierExpression "yes"
    CaseArmSeparator
      Comma ","
    Whitespace " "
    CaseArm
      Pattern
        IdentifierPattern "_"
      Whitespace " "
      Arrow "->"
      Whitespace " "
      OperatorChain
        IdentifierExpression "no"
```

`catch action { err, handler -> recover; }`では`CatchBlock`がbracesを直接所有し、first pattern、handler comma、second
`Pattern`、arrow、body、semicolonは一個の`CatchArm`のdirect source-order childrenになる。innerに
`BracedStatementBlockExpression`、`Statement`、`ColonApplicationTail`を作らない。

guard `OperatorChain`もbody `OperatorChain`もprecedence-neutralである。declared/imported numeric binding powerだけが変わっても
このCST hierarchyは変わらない。later associator / HIR loweringがscrutinee、guard、bodyの各chainを独立にassociateする。
pattern associationはpattern grammarのfixed surface ruleが所有し、dynamic expression associatorへ送らない。

### Parser-side AST shape

parser-side projectionはfamily差をvisible typeへ残し、shared helperの都合だけで一個のboolean-rich public structへ潰さない。

```rust
pub(crate) enum PrimaryExpression<'source> {
    // existing variants ...
    Case(CaseExpression<'source>),
    Catch(CatchExpression<'source>),
}

pub(crate) struct CaseExpression<'source> {
    keyword: WordSpan<'source>,
    label: Option<CaseLikeLabel<'source>>,
    scrutinee: Recovered<Box<OperatorChain<'source>>>,
    block: Recovered<CaseBlock<'source>>,
    base_indent: usize,
    range: Range<usize>,
}

pub(crate) struct CatchExpression<'source> {
    keyword: WordSpan<'source>,
    label: Option<CaseLikeLabel<'source>>,
    scrutinee: Recovered<Box<OperatorChain<'source>>>,
    block: Recovered<CatchBlock<'source>>,
    base_indent: usize,
    range: Range<usize>,
}

pub(crate) struct CaseLikeLabel<'source> {
    text: &'source str,
    range: Range<usize>,
}

pub(crate) struct CaseBlock<'source> {
    colon: Recovered<Range<usize>>,
    arms: Recovered<ArmSequence<CaseArm<'source>>>,
    layout: ColonArmLayout,
    range: Range<usize>,
}

pub(crate) enum CatchBlock<'source> {
    Colon {
        colon: Recovered<Range<usize>>,
        arms: Recovered<ArmSequence<CatchArm<'source>>>,
        layout: ColonArmLayout,
        range: Range<usize>,
    },
    Braced {
        open: Range<usize>,
        arms: Recovered<ArmSequence<CatchArm<'source>>>,
        close: Recovered<Range<usize>>,
        range: Range<usize>,
    },
}

pub(crate) enum ColonArmLayout {
    Inline,
    Indented {
        base_indent: usize,
        arm_indent: usize,
    },
}

pub(crate) struct ArmSequence<A> {
    arms: Vec<Recovered<A>>,
    trailing_comma: Option<Range<usize>>,
}

pub(crate) struct CaseArm<'source> {
    pattern: Recovered<Pattern<'source>>,
    guard: Option<Recovered<CaseGuard<'source>>>,
    arrow: Recovered<Range<usize>>,
    body: Recovered<ArmBody<'source>>,
    terminator: Option<Range<usize>>,
    range: Range<usize>,
}

pub(crate) struct CatchArm<'source> {
    pattern: Recovered<Pattern<'source>>,
    handler: Option<Recovered<Pattern<'source>>>,
    guard: Option<Recovered<CatchGuard<'source>>>,
    arrow: Recovered<Range<usize>>,
    body: Recovered<ArmBody<'source>>,
    terminator: Option<Range<usize>>,
    range: Range<usize>,
}

pub(crate) struct CaseGuard<'source> {
    keyword: ArmGuardKeyword<'source>,
    condition: Recovered<Box<OperatorChain<'source>>>,
    range: Range<usize>,
}

pub(crate) struct CatchGuard<'source> {
    keyword: ArmGuardKeyword<'source>,
    condition: Recovered<Box<OperatorChain<'source>>>,
    range: Range<usize>,
}

pub(crate) enum ArmGuardKeyword<'source> {
    If(WordSpan<'source>),
    Where(WordSpan<'source>),
}

pub(crate) enum ArmBody<'source> {
    Inline(Box<OperatorChain<'source>>),
    Indented(IndentedStatementBlock<'source>),
}
```

separator tokenの全列はlossless CSTがauthorityであり、ASTはassociation / loweringとrecoveryに必要なarm order、layout、
terminal comma、semicolon rangeだけを持つ。`Recovered`のexact carrierはcurrent sourceの型へ合わせてよいが、missing
pattern / guard expression / arrow / body / closeを別slotとして識別できなければならない。

### Recognition / commit control flow

direct pathを次で固定する。

```text
commit_case_like_expression(family, keyword, base_indent):
    start family Expression node
    emit family keyword

    probe optional apostrophe-sigil label
    if accepted:
        commit family Label node; maximal sigil scanning defines the following scrutinee boundary

    push family scrutinee stop frame
    start family Scrutinee node
    commit one mandatory OperatorChain or Missing
    finish Scrutinee and pop stop frame

    probe family-owned block introducer
    if `:`:
        start family Block; emit Colon
        classify inline / deeper-indented / wrong-indent
        commit mandatory arm sequence under matching policy
        finish Block
    else if family is Catch and `{`:
        start CatchBlock; emit LBrace; push Brace delimiter/right-brace stop
        commit mandatory CatchBraced arm sequence
        recover/emit RBrace; pop scope; finish CatchBlock
    else:
        emit one Missing block-introducer/body cause without consuming outer boundary

    finish family Expression node
```

一armのcontrol flowは次である。

```text
commit_arm(family, sequence_policy):
    start family Arm node

    push first-pattern stops
    commit mandatory direct Pattern
    pop stops

    if family is Catch and comma follows before guard/arrow:
        emit handler Comma directly
        push handler-pattern stops
        commit mandatory direct Pattern
        pop stops

    if contextual `if` or `where` follows:
        start family Guard node; emit keyword
        push Arrow stop
        commit mandatory OperatorChain or Missing
        pop stop; finish Guard

    commit mandatory exact Arrow or Missing
    classify post-arrow inline / deeper-indented / wrong-indent
    commit mandatory OperatorChain or IndentedStatementBlock, or Missing
    consume optional arm-terminal Semicolon

    finish family Arm node
```

probeはtriviaもsinkもcommitせず、acceptされたcandidateのleading triviaだけをownerへemitする。label、guard、arrow、comma、
brace closeのprobe failureでrollback後sink outputが残ってはならない。pattern / expression entrypointはactive stop frameを
readするが、caller frameをpopしない。

### Recovery contract

新しいrecovery primitiveは導入しない。existing cut、mandatory slot、`Missing`、non-empty `Error`、delimiter / lexical-region
safe pointを次のroleへ適用する。

| failure | committed CST | preserved boundary / retry |
| --- | --- | --- |
| keyword後にscrutineeがない | family Scrutinee内に`Missing(Expression)` | `:`、catch `{`、outer close / newline / EOFをconsumeしない |
| block introducerがない | family Block slotに一個の`Missing` | outer delimiter / newline / EOFへreturnする |
| `:`後がsame-or-shallower newline | Block内に`Missing(Arm)` | triviaと次outer constructをconsumeしない |
| first patternがない | Arm内Pattern slotに`Missing(Pattern)` | handler comma、guard keyword、arrow、block close / arm boundaryを守る |
| catch handler comma後にpatternがない | second Pattern slotに`Missing(Pattern)` | guard / arrowを守る |
| guard keyword後にexpressionがない | Guard内に`Missing(Expression)` | exact arrowを守り、同じarmを継続する |
| arrowがないがbody NUD candidateがある | `Missing(Arrow)`をinsert | same positionからbodyをcommitする |
| arrowとbodyが同じboundary原因でともにない | root-cause diagnostic一個と必要なslot marker | comma / dedent / right brace / EOFをconsumeしない |
| post-arrow newlineがsame-or-shallower | `Missing(Expression)` | 次armまたはouter ownerへnewlineを返す |
| arm間commaがなく次patternが始まる | family ArmSeparator位置に`Missing(Comma)` | same positionから次armを一度だけretryする |
| comma後がmalformed | non-empty `Error`後にmandatory Arm retry | comma / close / dedent / EOF safe pointまでだけ進む |
| catch braceが閉じない | CatchBlock内に`Missing(RBrace)` | caller-owned delimiter / lexical boundaryを越えない |

mandatory armはpattern、optional handler、optional guard、arrow、bodyという内部slotを保ったdegenerate nodeを作る。
parserはpattern recovery diagnosticをcase owner側で重複発行しない。association / HIR loweringは`Missing` / `Error`を含む
scrutinee、guard、body chainとarmをdeterministically一回lowerできなければならず、parser diagnosticを再発行しない。

recovery scanはopaque string / comment / interpolation region内部の`->`、comma、brace、`if`、`where`をsafe pointとして
誤認しない。active delimiter stackとlexical modeが最優先である。同じsource positionで同じmandatory arm / arrow / bodyを
retryせず、successまたはnon-empty recovery consumptionのどちらかで必ずprogressする。

### Existing architecture principlesとの整合

- **Precedence-neutral surface CST**: scrutinee、guard、bodyはflat `OperatorChain`であり、binding powerはcase/catch
  parseへ入らない。arrowだけはarm ownerのfixed boundaryである。
- **Immutable operator table**: tableは各nested `OperatorChain`のoperator spelling / fixity capability recognitionにだけ
  read-onlyで使う。case/catch node shape、arm count、arrow ownership、layoutを変えない。
- **BpVec / BindingPower**: yu-syntax側のcase/catch control flowでは使わない。later associatorが三種のnested chainを
  associateするときだけ使う。
- **Oracle judge table**: expression NUD tableへ`case` / `catch` primary candidateを追加する。pattern primary / tail、
  case-like label、guard、arrow、arm separatorは各grammar ownerのfixed judgeでありdynamic operator oracleへ混ぜない。
- **Rollback discipline**: keyword / label / introducer / guard / arrow / separator / closeはsink-free probe、accept後cut、
  forward-only direct emitで処理する。started nodeやdiagnosticをrollbackしない。
- **Lexical-region-aware scanning**: stop / separator / recoveryはcurrent delimiter depthとopaque lexical modeでだけ有効にする。
- **Single body-layout authority**: introducer後triviaのinline / deeper-indent / wrong-indent分類を一個のneutral helperへ寄せ、
  colon application、if、case/catchでcopyしない。owner-specific RHS arityとcompanion stopは各wrapperが持つ。
- **Sequence authority**: statement sequenceとarm sequenceは別coreである。前者は`Statement`、後者はPattern / Guard /
  Arrow / Bodyをparseし、policy type以外のcross-callを持たない。
- **Surface / interpretation boundary**: parserはlabelの制御効果、patternのbinding / constructor / wildcard意味、handlerの
  callable性、guard truth、exhaustiveness、catch semanticsを判定しない。HIR lowering以降が所有する。

binding-power-only editはcase/catchを含むsurface CSTをinvalidateしない。association / HIRだけをinvalidateする。
operator spelling / fixity-capability editはnested chain recognitionへ影響し得るためparse invalidation対象である。このsplitは
precedence-neutral operator-chain追補と`docs/yulang3-architecture.md`のincremental invalidation contractに従う。

### Implementation boundary and required gates

implementation sliceは少なくとも次を行う。

1. `SyntaxKind`へfamily-specific expression / label / scrutinee / block / arm / guard / separatorとkeyword / arrow kindを追加する。
2. expression NUD judgeへexact contextual `case` / `catch`を追加し、AST pathとdirect-CST pathを同じrecognition resultへ
   接続する。
3. apostrophe-sigil label scannerをUnicode word-body primitiveから構成し、pattern private scannerのbody ruleをcopyしない。
4. `StopKind`とexpression / pattern mandatory recoveryをarrow / arm-guard boundaryへ拡張する。
5. maximal operator-shaped tokenからexact `->`だけをarm-local fixed tokenとしてrecognizeする。
6. `CaseLikeFamily`とclosed `ArmSequencePolicy`を追加し、statement sequenceと分離したshared arm loopを実装する。
7. current post-colon layout classifierをintroducer-neutral name / authorityへ移し、既存三callerを壊さずarrow bodyから共有する。
8. arm bodyのindented routeをexisting default-policy `IndentedStatementBlock`へ接続する。
9. AST/direct parity、lossless source、typed recovery diagnosticをfixtureで固定する。

required testsは次を含む。

- `case x: 1 -> a, 2 -> b`のinline multiple armsとoptional trailing comma。
- `case x:\n  1 -> a\n  _ -> b`のindented newline arms、explicit comma variant、dedent termination。
- `case 'go 4: 0 -> zero, n -> n`のlabel / scrutinee boundary。
- `n if cond -> yes`と`n where cond -> yes`のfamily guard node、guard内flat `OperatorChain`。
- current pattern subsetのsymbol、parenthesized、alias、alternationがarm arrow / guard stopを越えないこと。
- `catch action: err, handler -> recover`のinline exactly-one armとfull second Pattern。
- catch indented multiple armsと、comma / current-depth newlineの両方で区切る
  `catch action { err -> recover, _ -> fallback }`のdirect `CatchBlock` braces。
- case scrutineeはLeftBrace stopを持たず、catch scrutineeだけがbraceをblock introducerとしてreserveすること。
- inline / deeper-indented arrow body、body内multiple statements、same-indent missing-body recovery。
- missing scrutinee / pattern / handler / guard expression / arrow / body / brace close、missing arm commaのlossless recovery。
- `->>`をarrowへsplitしないこと、operator tableにおける`->`の有無やBP変更がarm CST shapeを変えないこと。
- nested delimiter / opaque lexical region内のcolon / brace / comma / arrow / guard wordをouter stopにしないこと。
- `green.to_string() == source`、AST/direct structural parity、header/full diagnostic identity。

current pattern grammarのhistorical standalone testsは残す。case/catch integration testsはpublic standalone pattern entrypointを
迂回して別pattern implementationを作らず、同じ`parse_direct_pattern`をactive stop frame下で呼ぶ。

### Explicit future scope

次はこの追補へ含めない。

- `\case` / `\catch` lambda form。backslash-lambda primaryとparameter / capture boundaryを専用addendumで設計する。
- list / record / spread / type-annotation / string・rule / field / path / no-space constructor / ML application pattern。
  pattern grammar自身のfuture sliceで追加し、case/catchは自動的に同じentrypointから受け取る。
- historical `Ok v` / `Err e`のようなconstructor application patternをcase側だけで特別認識すること。
- exhaustiveness、unreachable arm、duplicate binding、guard typing、handler validation、label semantics、exception routing。
  HIR lowering / type and effect analysisの責務である。
- other colon-owning constructs (`for`、`sub`、declaration body等)との抽象化。shared low-level layout primitive以外を
  case-like grammarへ統合しない。

`case` brace arm blockはfuture scopeではなく**invalid by design**である。case scrutinee側のbrace primary / future ML argument
ownershipを保つ。catch colon-inline multiple armもfuture scopeではなく**invalid by design**であり、multiple armsは
indented formまたはcatch-owned bracesを使う。

### Closed decisions and review focus

この追補で閉じるdecisionは次である。

- `case`と`catch`は同一sliceのtwo NUD primariesであり、`ColonApplicationTail`ではない。
- label、both guards、catch handler、catch brace blockをfirst sliceに含める。
- patternはcommit `4ec436cc`のsame standalone parserをconsumeし、current subsetを越えるformをstubしない。
- case scrutineeはColonだけ、catch scrutineeはColon + LeftBraceをreserveする。
- catch handlerはfull second Patternでありidentifier-only validationをparserへ入れない。
- guard `if`はIfExpressionではなくarm-local introducerである。
- arrow後のindented bodyはexisting `IndentedStatementBlock`、arm listはdedicated arm-sequence coreである。
- catch bracesはdirect `CatchBlock`であり`BracedStatementBlockExpression`ではない。
- exact arrowはarm-local fixed boundaryでありnumeric BPから独立する。
- all block formsはmandatory non-empty arm sequence、comma-owning list formsはexplicit trailing commaを保持する。
- semicolonはarm terminalでありarm-list separatorではない。

Claude reviewでは、特にcurrent pattern recoveryがarrow / guard boundaryを守る拡張、caseとcatchのbrace-stop非対称、
catch inline bodyのcommaをarm listが奪わないこと、arrow lineを基準にしたdeeper body indent、statement sequenceとarm
sequenceの分離、`->>` maximal scan、catch brace close recovery、trailing commaとsemicolonのownershipを確認対象にする。
helper名、private AST carrier、typed diagnostic enumの具体名はcurrent sourceへ合わせて調整してよいが、上のsurface
grammar、family差、CST ownership、phase boundaryをopenに戻さない。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定、ユーザ承認済み
（2026-08-22、NUD-primary `case` / `catch` expression grammar追補案）。

## 追補案: comma-delimited `ListPattern`とspread item grammar

Status: Claude review / exact wordingのfinal sign-off待ち。

Separator-scope status: superseded。comma-only grammar / recovery / gatesだけは、末尾の
「layout-aware comma-or-newline delimited sequence」追補へ置き換える。spread / CST / AST / semantic deferralは維持する。

Date: 2026-08-22。

### Decision summary

already-implemented fixed-precedence pattern grammarへ、NUD-position primary `ListPattern`を追加する。

```text
ListPattern :=
    LBracket G*
    [ ListPatternItem G* { Comma G* ListPatternItem G* } [ Comma G* ] ]
    RBracket

ListPatternItem := Pattern | ListPatternSpreadItem
ListPatternSpreadItem := DotDot G* Pattern
```

このsliceは次を確定する。

- `[]`はvalid zero-item list patternである。
- separatorはcommaだけである。physical newlineはlossless triviaとして保持するがimplicit separatorにしない。
- terminal commaをvalidとし、そのrangeをASTにも保持する。
- spread marker `..`のRHSはidentifier-only rest nameではなくfull recursive `Pattern`である。
- spread itemのpositionとmultiplicityをparserで制限しない。first / middle / last、複数spreadを同じsurface shapeで受理する。
- ordinary itemはdirect child `Pattern`、spreadだけは`ListPatternSpreadItem(DotDot, Pattern)` wrapperを持つ。
- `[` / `]`、comma、trivia、spread spellingをsource orderのまま一度だけemitする。

spreadの個数・位置・型的な意味はsyntax recognitionではない。future pattern HIR lowering / validationがlanguage-level制約を
必要と判断した場合も、parserはliteral sourceを同じ`ListPattern` shapeで保持し、later phaseがdiagnosticを出す。

本追補はfirst-slice pattern addendumの「list pattern / spreadをdeferする」というscope gateだけをsupersedeする。
identifier / integer / symbol / parenthesized primary、alias / alternation precedence、case/catch consumer boundaryは変更しない。
case/catchはsame `parse_direct_pattern`を呼ぶため、別wiringなしでlist patternをarmへ受け入れる。

### Re-verified Yulang2 surface and implementation

Yulang2 specのexact productionは次だった
(`yulang2-oracle@a58eefc3:spec/2026-06-06-syntax-design.md:1519-1530`)。

```text
pat_list =
  "[" ((pattern | ".." pattern) ("," (pattern | ".." pattern))* ","?)? "]"
```

pattern NUD dispatchは`OpenBracket`を`parse_pat_list_group`へ送り、一個の`PatList`を開始した
(`yulang2-oracle@a58eefc3:crates/parser/src/pat/parse.rs:100-103,307-315`)。list item machineは各item先頭で
`DotDot`を独立にprobeし、成立すれば`PatSpread`を開始してfull `parse_pattern`をRHSへ呼んだ。ordinary itemも同じ
comma / closing stop下でfull patternだった
(`crates/parser/src/pat/parse.rs:355-408`)。

このloopはspread count、既出spread、item indexを保持しない。したがってYulang2 parser上はspreadがfirst / middle / lastの
どこにあってもよく、複数spreadもparse-time validだった。これはsemantic rationaleが明文化された結果ではなく、
item-local recognitionの帰結である。本追補はhistorical permissivenessを無批判にsemantic ruleへ昇格するのではなく、
**surface parserがcross-item semantic validationを所有しない**というYulang3のphase boundaryとして明示的に採用する。

explicit separator predicateは`Comma`だけだった
(`crates/parser/src/pat/parse.rs:365-372`)。ただしunderlying `DelimitedListMachine`はcurrent base indent以下のphysical
newlineをempty `Separator`として受理した
(`yulang2-oracle@a58eefc3:crates/parser/src/parse/mod.rs:21-23,35-67`)。よってhistorical implementation languageは
specのcomma grammarより広かった。list pattern固有fixtureにimplicit-newline separator coverageはない。

emptyとtrailing commaはdedicated branchではなく、item probeが`BracketR`をStopとして返しgeneric machineがcloseを
consumeすることで成立した。open直後のcloseとcomma後のcloseは同じpathである
(`crates/parser/src/pat/parse.rs:370-397`;
`crates/parser/src/parse/mod.rs:35-67`)。

唯一のlist-pattern fixture `[head, ..middle, tail]`は次のCSTを固定する。

```text
PatList(
  BracketL,
  Pattern(head),
  Separator(Comma),
  PatSpread(DotDot, Pattern(middle)),
  Separator(Comma),
  Pattern(tail),
  BracketR,
)
```

evidenceは`yulang2-oracle@a58eefc3:crates/parser/tests/pat_grammar.rs:201-230`である。tagのtest suiteには
list patternのmissing close、missing spread RHS、missing separator、malformed item fixtureがない。したがってrecoveryは
historical test oracleを推測せず、Yulang3のtyped mandatory-slot contractから定義する。

### Current Yulang3 baseline and extension point

commit `72c93d5a`時点の`PatternPrimary`は`Identifier`、`Integer`、`Symbol`、`Parenthesized`だけであり、
`PatternNudRecognition` / `recognize_pattern_nud`もopen parenthesisまでしかdelimited primaryを認識しない
(`crates/yu-syntax/src/grammar/pattern.rs:62-68,399-440`)。`parse_pattern` / `parse_direct_pattern`、fixed
`PatternPrecedence`、parenthesized comma / close recoveryは実装済みである。

case/catch-driven fixesはactive `Arrow` / `ArmGuardIf` / `ArmGuardWhere`をpattern NUDとinvalid-run recoveryのsafe pointにし、
`parse_direct_pattern`をactual arm consumerへ接続した
(`crates/yu-syntax/src/grammar/pattern.rs:357-452,985-1019`;
`crates/yu-syntax/src/grammar/expression.rs:907-929,2502-2508`;
`crates/yu-syntax/src/session.rs:357-373`)。list primaryはこのsame entrypointをrecursiveに拡張し、case/catch側へparallel
parserを作らない。

scanner / session vocabularyには`Delimiter::Bracket`、`StopKind::RightBracket`、`LBracket` / `RBracket` scanとCST tokenが
すでにある (`crates/yu-syntax/src/session.rs:357-380`;
`crates/yu-syntax/src/scan/punctuation.rs:67-74`;
`crates/yu-syntax/src/syntax_kind.rs:94-100`)。ただしgrammar owner、item sequence、spread marker、typed list recoveryはない。
tokenが存在することをlist grammar実装済みとは数えない。

`pattern.rs`先頭の「production consumerがない」というmodule commentはcase/catch実装後の現状と一致しない
(`crates/yu-syntax/src/grammar/pattern.rs:1-6`)。本callではsourceを変更しないが、future implementation sliceはlist追加と
同時にcommentを「standalone entrypointを持ち、case/catchからもconsumeされるindependent grammar family」へ更新する。

### Separator scope: comma-only

Yulang3 `ListPattern`はcomma-onlyとする。semicolonもimplicit physical newlineもvalid separatorではない。

approved first-slice pattern addendumは`ParenthesizedPattern`について、Yulang2 generic machineのimplicit-newline behaviorを
移植せず、newlineをtriviaとして保持しつつnext element前へmissing comma recoveryを置く、と確定した
(`notes/design/2026-08-20-yu-syntax-chasa-architecture.md:6841-6849,7177`)。list patternは同じpattern grammar familyの
同じcomma-delimited recursive element listであり、ここだけhistorical implementation leakageを復活させる理由がない。

結果を次で固定する。

| source | result |
| --- | --- |
| `[]` | valid empty list |
| `[a]` | valid one ordinary item |
| `[a,]` | valid one item + trailing comma |
| `[a,\n b]` | valid two items。newlineはcomma後trivia |
| `[a\n b]` | two items + zero-width missing comma before `b` |
| `[a; b]` | semicolonはnon-empty separator `Error`。valid separatorではない |

newlineを禁止byteにしない。commentsを含む`G*`としてCSTへ残し、commaの有無だけをsurface validityに使う。
future language decisionでlayout-separated pattern containerが必要になった場合は、そのcontainer ownerのaddendumで
明示的に導入する。generic bracket scopeが暗黙に全pattern listへlayout separatorを与えてはならない。

### Spread item and semantic boundary

`ListPatternSpreadItem`はliteral `..`とmandatory full `Pattern@Lowest`を所有する。

```text
ListPatternSpreadItem := DotDot G* Pattern@Lowest
```

full recursive RHSを選ぶ理由は三つある。

1. Yulang2 actual parserとspecの両方がfull patternを要求する。
2. `..tail as rest`、`..(:tag | other)`、`..[head, ..tail]`をexisting pattern grammarのcompositionとして表せる。
3. parserがidentifier spellingをrest bindingへ固定すると、binding / wildcard / constructor判断をHIR前へ引き戻す。

spread RHSのextentはlist ownerのlocal `Comma` / `RightBracket` stopまでである。したがって`[..a | b, c]`ではspread RHSは
alternationを含む`Pattern(a | b)`、second list itemは`c`である。`..`とRHSの間のtriviaはoptionalで、`..tail`と
`.. tail`を同じnode shapeで保持する。

position / multiplicityはunrestricted surface grammarとする。

```text
[..head, middle]
[head, ..middle, tail]
[head, ..tail]
[..left, middle, ..right]
```

いずれもparser-validである。parserはspread countを数えず、一個目と二個目でnode kindやrecovery pathを変えない。
「最大一個」「tail positionだけ」等を将来採用する場合、それはlist destructuring semanticsを所有するpattern lowering /
validation ruleとして全`ListPatternSpreadItem`列を一度検査する。CSTを二種類へ分けたり、second spreadをgeneric `Error`へ
変換したりしない。

これはinvalid syntaxを無条件にsemantic phaseへ送る一般規則ではない。missing comma、missing spread RHS、missing closeは
grammar errorとしてparserがrecoverする。一方、source上明示されたvalid item formの組合せに対するcardinality constraintは
later validationである、という境界である。

### Grammar and precedence integration

`G*`はnewlineを含み得るmaximal lossless trivia run、`Pattern@P`はexisting fixed minimum precedence callである。

```text
PatternPrimary += ListPattern

ListPattern :=
    LBracket G*
    [
        ListPatternItem G*
        { Comma G* ListPatternItem G* }
        [ Comma G* ]
    ]
    RBracket

ListPatternItem :=
    Pattern@Lowest
  | ListPatternSpreadItem

ListPatternSpreadItem :=
    DotDot G* Pattern@Lowest
```

item-required positionではspread markerをordinary pattern NUDより先にcomposite probeする。`..`が成立しなければbyteを
consumeせずexisting `PatternNudRecognition`へfallbackする。spreadはnew precedence tailではなくlist-primary内部のitem
prefixである。`PatternPrecedence::{Lowest, Alternation, Alias}`と`PatternLedRecognition`を変更しない。

matching `]`後はouter `Pattern`のexisting LED loopへ戻る。したがって`[a] as xs | []`はhead
`ListPattern`、alias tail、alternation tailという既存source-order shapeになる。list nodeがouter pattern tailを所有しない。

### `..` lexical ownership

current fixed punctuation scannerはbracketsを既にscanする一方、`..` / `...`をdynamic-operator territoryへ残している
(`crates/yu-syntax/src/scan/punctuation.rs:39-58,67-82`)。list pattern parserは`OperatorTable`を受け取らないため、
spread markerをdynamic operator declarationへ問い合わせない。

implementationはdeclaration-independentなmaximal operator-shaped spelling probeをreuse / extractし、list-item-required
positionでcandidate textがexact `..`のときだけ`DotDot`としてacceptする。`...`、`..+`等のlonger operator-shaped
spellingを`..` + remainderへsplitしない。probeはsink-freeで、reject時にinput / line stateをexact rollbackする。

このexactnessはadjacent RHSを禁止しない。`..tail`ではmaximal operator-shaped spellingが`..`で終わり、following
identifier `tail`がRHS NUDになる。`...tail`はspreadではなくmalformed itemとしてrecoveryされる。operator headerで
`..`のfixity / BPを宣言または変更してもlist-pattern CST / AST / diagnosticは変わらない。

`SyntaxKind::DotDot`はaccepted list spread markerのfixed grammar roleである。expression positionの同じspellingは
引き続きdynamic `Operator` tokenであり、shared `PunctuationKind`へunconditional `DotDot`を追加しない。

### Delimiter and stop scope

accepted `LBracket`でcutした後、list ownerは次をpushする。

```text
delimiter = Delimiter::Bracket
local stops = { StopKind::Comma, StopKind::RightBracket }
```

このlocal frameはincoming case/catch `Arrow` / `ArmGuardIf` / `ArmGuardWhere` / handler `Comma`、outer paren close等を
bracket depthの外へsuspendする。list内部のcommaはlist ownerが所有し、matching `]`後にouter stop frameをexact restoreする。
たとえば`catch x: [head, ..tail], handler -> body`ではfirst commaはlist separator、`]`後のcommaだけがcatch handler
separatorである。

all exit paths、すなわちempty close、normal close、trailing comma close、missing item、malformed item、missing closeで
delimiter / stop stackを一回ずつpopする。recursive list RHSは新しいbracket frameをnestし、inner closeがouter closeを
consumeしない。

list item candidateは次のpriorityで判定する。

1. matching `RightBracket` pendingならempty / terminal boundary。itemを開始しない。
2. exact `DotDot` pendingならspread item。
3. existing `pattern_nud_candidate`ならordinary item。
4. comma pendingならmandatory item missing boundary。
5. それ以外はnon-empty item / separator recovery。

incoming outer stopはnormal item parse中はsuspendするが、missing-close recoveryのescape boundaryとしてsnapshotを保持する。
matching `]`を得る前にcurrent-depth caller-owned arrow / guard / outer close / EOFへ達した場合、zero-width missing `]`をemitして
outer boundaryをconsumeせずscopeをrestoreする。opaque lexical region内の同じspellingはescape boundaryにしない。

### CST vocabulary and shape

本sliceで追加するkindは次だけである。

```text
SyntaxKind::ListPattern
SyntaxKind::ListPatternSpreadItem
SyntaxKind::DotDot
```

`Pattern`、`IdentifierPattern`、`ParenthesizedPattern`、`LBracket`、`RBracket`、`Comma`、trivia、`Missing`、`Error`は
existing kindを使う。`PatList` / `PatSpread` abbreviation、`RestPattern`、`ListPatternItem` wrapper、generic `Separator` nodeは
追加しない。

ordinary itemはdirect `Pattern` childである。spread itemだけはmarkerとRHSのownershipを表す
`ListPatternSpreadItem`を持つ。commaはapproved `ParenthesizedPattern`と同様にraw `Comma` tokenとして`ListPattern`直下へ
emitし、synthetic separator nodeへ包まない。

`[head, ..middle, tail]`のCSTは次になる。

```text
Pattern
  ListPattern
    LBracket "["
    Pattern
      IdentifierPattern
        Identifier "head"
    Comma ","
    Whitespace " "
    ListPatternSpreadItem
      DotDot ".."
      Pattern
        IdentifierPattern
          Identifier "middle"
    Comma ","
    Whitespace " "
    Pattern
      IdentifierPattern
        Identifier "tail"
    RBracket "]"
```

`[..left, ..right,]`もouter kindを変えない。

```text
Pattern
  ListPattern
    LBracket "["
    ListPatternSpreadItem
      DotDot ".."
      Pattern
        IdentifierPattern
          Identifier "left"
    Comma ","
    Whitespace " "
    ListPatternSpreadItem
      DotDot ".."
      Pattern
        IdentifierPattern
          Identifier "right"
    Comma ","
    RBracket "]"
```

zero / one / many item、ordinary / spread ordering、trailing comma、spread countによって`ListPattern`以外のouter nodeを
選ばない。全source byteを一度だけemitし、`green.to_string() == source`を維持する。

### Parser-side AST shape

existing `PatternPrimary`へ一variantを追加する。

```rust
pub(crate) enum PatternPrimary<'source> {
    Identifier(PatternNameSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Symbol(SymbolPattern<'source>),
    Parenthesized(ParenthesizedPattern<'source>),
    List(ListPattern<'source>),
}

pub(crate) struct ListPattern<'source> {
    open: Range<usize>,
    items: Vec<Recovered<ListPatternItem<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

pub(crate) enum ListPatternItem<'source> {
    Pattern(Pattern<'source>),
    Spread(ListPatternSpreadItem<'source>),
}

pub(crate) struct ListPatternSpreadItem<'source> {
    marker: Range<usize>,
    rhs: Recovered<Box<Pattern<'source>>>,
    range: Range<usize>,
}
```

`items`のsource orderはCSTと一致する。missing item after commaは`Recovered::Incomplete`、accepted spread + missing RHSは
`Recovered::Complete(ListPatternItem::Spread { rhs: Recovered::Incomplete, ... })`で区別する。後者はliteral `..`が存在する
というsyntax factを失わない。exact recovery carrierはcurrent codeへ合わせてよいが、この区別を潰してはならない。

ASTはall comma tokenをduplicateしない。semantic validationに必要なitem order / spread marker role / trailing commaとclose
recoveryだけを保持し、lossless spellingはCSTをauthorityとする。`ListPatternItem::Spread`をidentifier rest bindingへlowerする
判断はparser-side ASTで行わない。

### Shared comma-delimited pattern mechanics

`ParenthesizedPattern`と`ListPattern`は、empty detection、comma commit、trailing comma、missing separator same-position retry、
matching close、scope restorationという二個目のconcrete userを持つ。これらのmechanicsはcopyせず、closed internal policyへ
factorする。

```rust
enum PatternDelimitedPolicy {
    Parenthesized,
    List,
}
```

policyが所有するのはdelimiter、opening / closing token kind、construct role、item / separator recovery role、item-candidate /
item-commit callbackだけである。`ParenthesizedPattern`はordinary `Pattern`だけ、`ListPattern`はordinary / spread sumをparseする。
public ASTをgeneric `DelimitedPattern<T>`へ変えず、outer CST nodeとsemantic projectionはdistinctのままにする。

Status: この段落のfuture record-field predictionだけは後続の`RecordPattern`追補によりsupersededされた。record grammarが
concrete third userになったため、delimiter / comma / close / retry mechanicsは`PatternDelimitedPolicy::Record`へ共有する。
field / spread / embedded-default item grammarは引き続きrecord owner固有である。

expression argument list、statement sequence、case/catch arm sequenceをこのhelperへ通さない。separator spellingがcommaでも、
item grammar、layout、close recovery ownerが異なるためである。

### Recognition / commit control flow

AST pathとdirect-CST pathで同じsink-free NUD recognitionを共有する。

```text
recognize_pattern_nud:
    existing arm-stop / symbol priority
    exact name / integer / parenthesis probes
    if fixed `[` opening is accepted:
        return PatternNudRecognition::List { open }

commit_list_pattern(open):
    start ListPattern; emit LBracket; push bracket scope
    emit maximal leading trivia

    if matching RBracket pending:
        emit close; pop scope; finish valid empty list
        return

    loop:
        commit one mandatory ListPatternItem
        emit following trivia

        if comma pending:
            emit raw Comma and following trivia
            if matching RBracket pending:
                record trailing comma; emit close; pop scope; finish
                return
            continue with one mandatory item

        if matching RBracket pending:
            emit close; pop scope; finish
            return

        if exact DotDot or Pattern NUD candidate pending:
            emit zero-width Missing(ListSeparator)
            retry next item at the same position
            continue

        recover one non-empty separator/close episode
        if item candidate found:
            retry next item
        else:
            recover/insert close; pop scope; finish
```

mandatory item continuationは次である。

```text
commit_list_item:
    if exact DotDot pending:
        start ListPatternSpreadItem; emit DotDot; cut
        emit trivia
        commit Pattern@Lowest with role ListSpreadRhs
        finish spread item
    else:
        commit Pattern@Lowest with role ListItem
```

accepted `[` / `..`後はalternativeへrollbackしない。direct `Pattern` nodeはexisting
`parse_direct_pattern_bp(PatternPrecedence::Lowest, role, ...)`がemitする。list wrapperがpattern recovery diagnosticを
重複発行しない。

### Typed recovery contract

typed vocabularyへ次を追加する。

```text
PatternRole::{
    ListItem,
    ListSpreadRhs,
    ListSeparator,
}

ConstructRole::ListPattern

ExpectedSyntax::Pattern
ExpectedSyntax::Punctuation(Comma)
ExpectedSyntax::Punctuation(Close(Bracket))
```

new recovery primitiveは不要である。zero-width `Missing`、maximal non-empty `Error`、one committed recovery node = one
diagnostic、same-position retry、delimiter / lexical safe pointをexisting parenthesized / case-arm contractどおり使う。

| source situation | required recovery / CST ownership |
| --- | --- |
| `[]` | valid empty `ListPattern`。Missingなし |
| `[a,]` | valid one item + raw trailing `Comma`。Missingなし |
| `[,a]` | first comma位置に`Pattern > Missing(ListItem)`、commaを保持し`a`をnext itemとしてparse |
| `[a,,b]` | second comma位置にmissing item一件。両commaを保持し`b`へ進む |
| `[a b]` | current no-ML-application sliceでは`b`直前へzero-width `Missing(ListSeparator)`、same positionからordinary itemをretry |
| `[a ..b]` | `..`直前へzero-width `Missing(ListSeparator)`、same positionからspread itemをretry |
| `[a; b]` | `;`をnon-empty `Error(ListSeparator)`、expected commaとし、`b`をsame sequenceのnext itemとしてretry |
| `[a, @ b]` | `@`をnon-empty `Error(ListItem)`にし、same mandatory item slotを`b`からretry |
| `[..tail]` | complete spread item。RHSはfull `Pattern(tail)` |
| `[..]` | `DotDot`を保持したspread node内にzero-width `Pattern > Missing(ListSpreadRhs)`、`]`をconsumeしない |
| `[..,a]` | comma位置でmissing spread RHS一件。そのcommaをlist separatorとして保持し`a`へ進む |
| `[..@tail]` | `@`をspread RHSのnon-empty `Error`にし、same RHS slotを`tail`からretry |
| `[...,a]` | `...`を`DotDot`へsplitせずnon-empty malformed item `Error`。comma後の`a`へ進む |
| `[a` + EOF | itemを保持し、EOFへzero-width `Missing(RBracket)`一件 |
| `[a)` | `)`をclosing-delimiter evidence付きnon-empty `Error`にし、matching `]`探索またはmissing closeへ進む |
| case arm内`[a -> body` | outer Arrowをconsumeせずzero-width missing `]`を置き、scope restore後arm ownerへ返す |

leading / repeated commaはempty / trailing判定と区別する。trailing commaがvalidなのは少なくとも一個のcommitted itemの後で、
comma後にmatching closeがpendingな場合だけである。open直後のcommaはmissing first item、二comma目はmissing intervening itemを
表す。

invalid-run recoveryはmatching `]`、comma、exact spread marker、ordinary Pattern NUD candidate、captured outer safe point、EOFを
consumeしない。non-empty Errorをemitした場合だけsame mandatory slotをretryする。同じpositionへMissing separatorを二度
置かず、retryはitem commitまたはnon-empty recovery consumptionで必ずprogressする。

future ML-application pattern tailが追加されれば、whitespace-separated primary candidateをcurrent itemのtailとしてconsumeする
caseが増え得る。その場合もlist loopが先にshapeを推測せず、**full Pattern parserが返した位置**でだけseparatorを判定する。
上表の`[a b]`はcurrent sliceのgateであり、future ML grammarを禁止する恒久的lexical splitではない。

matching close recoveryはnested delimiter / opaque string・comment・interpolation region内の`]`をouter closeにしない。
mismatched current-depth `)` / `}`はunexpected closing evidenceとしてnon-empty Errorにできるが、captured caller boundaryを
越えてmatching closeを探さない。all recovery recordは`GrammarRole::Pattern`または
`GrammarRole::ClosingDelimiter { owner: ListPattern, ... }`を持ち、root trailing diagnosticと混同しない。

### Existing architecture principlesとの整合

- **syntax-as-written CST:** item count、spread count / position、trailing commaによってouter nodeを変えない。literal spreadだけを
  source-local wrapperで示す。
- **independent pattern authority:** list primary / spread item / fixed comma scopeはpattern moduleが所有する。expression
  `OperatorChain`やdynamic NUD / LEDへ追加しない。
- **fixed precedence:** spread RHSはexisting `Pattern@Lowest`であり、新しいprecedence levelや`BpVec`を要求しない。
- **immutable operator table:** list entrypointはtableを受け取らず、`..` declaration / BP変更から独立する。
- **oracle judge separation:** `[` primaryとitem-required `..`はsmall pattern NUD/item judgeへ追加し、expression operator oracleへ
  混ぜない。
- **rollback discipline:** bracket / exact spread / comma / close / next-item candidateはsink-free probe、accept後cut、forward-only
  emitとする。started nodeやdiagnosticをrollbackしない。
- **lexical-region awareness:** delimiter stackがnested bracket / paren / brace、opaque region、outer case stopsを分離する。
- **mandatory-slot recovery:** accepted spreadはmissing RHSでも`ListPatternSpreadItem`を閉じる。missing separatorはsame-position
  item retry、malformed episodeはnon-empty Errorでprogressする。
- **semantic deferral:** identifier / wildcard / constructor判断に加え、spread cardinality / position / capture semanticsをlater
  pattern lowering / validationへ送る。
- **consumer stability:** case/catchは同じpattern entrypointを呼ぶだけで、list内部commaをhandler / arm separatorとして
  誤認しない。consumer-specific codeへlist special caseを足さない。

### Implementation boundary and required gates

implementation sliceは`crates/yu-syntax/src/grammar/pattern.rs`を中心に次を行う。

1. AST / NUD recognitionへ`ListPattern`とspread itemを追加する。
2. `SyntaxKind::{ListPattern, ListPatternSpreadItem, DotDot}`とrowan conversionを追加する。
3. `PatternRole::{ListItem, ListSpreadRhs, ListSeparator}`、`ConstructRole::ListPattern`を追加する。
4. `Delimiter::Bracket` / `StopKind::RightBracket`を初めてproduction pattern scopeへ接続する。
5. operator table非依存のexact maximal `..` probeを追加またはgrammar-neutral lexical primitiveから抽出する。
6. parenthesized / listでcomma / close mechanicsをclosed internal policyとして共有し、item grammarはowner別に保つ。
7. AST-only / direct-CST path、typed diagnostics、scope restorationをfixtureで固定する。

required gatesは次である。

1. `[]`、`[a]`、`[a,]`、`[a,b]`、`[a,b,]`がuniform `ListPattern`とexact item count / trailing markerを持つ。
2. `[head, ..middle, tail]`がordinary / spread / ordinary source-order shapeになる。
3. `[..a, b, ..c]`が二spreadをsurface-validに保持し、second spreadをErrorへ変えない。
4. `[..a | b, c]`のspread RHSがalternationを含むfull Patternである。
5. `[a,\n b]`はvalid、`[a\n b]`はmissing comma一件、`[a; b]`はseparator Errorになる。
6. leading / repeated comma、missing separator before ordinary / spread、malformed itemがtableどおりsame-position retryする。
7. missing / malformed spread RHSがDotDot nodeを保持し、comma / closeをconsumeしない。
8. missing / mismatched close、outer arm arrow escape、nested bracketsでall delimiter / stop framesがbalancedになる。
9. `...` / `..+`をspreadへprefix-splitしない。`..tail` / `.. tail`はvalidである。
10. operator headerの`..` spelling / fixity / BP変更でlist pattern CST / AST / diagnosticsが変わらない。
11. `case xs: [head, ..tail] -> head`と`catch x: [a,b], handler -> body`でbracket-local comma ownershipを保つ。
12. all probesでsink call 0、accepted node emission一回、`green.to_string() == source`、AST/direct parityを満たす。
13. existing parenthesized pattern、case/catch、expression/operator testsのshape / diagnosticsを維持する。

### Explicit future scope

本追補は次を設計しない。

- record pattern、field shorthand、`name: pattern (= expression)?`、`name = expression`、record spread。
- pattern type annotationとtype-expression grammar。
- string / rule literal pattern。
- field / path / no-space constructor call / ML application pattern tail。
- wildcard / constructor resolution、or-pattern binding-set equality、list element typing。
- spreadのruntime matching algorithm、capture representation、zero / one / many element allocation semantics。
- semantic ruleとしてのspread count / position制限。必要ならpattern HIR / validation addendumが所有する。
- expression list literal。same bracketsを使ってもexpression grammar familyの別primaryである。
- implicit-newlineまたはsemicolon-separated pattern list。futureに必要ならseparator-scope addendumで明示的に決める。

record spreadとlist spreadはliteral `.. Pattern`を共有し得るが、outer item grammarとsemantic roleが異なる。本sliceの
`ListPatternSpreadItem`をfuture record CST nodeへ流用するかはrecord addendumが判断し、ここではgeneric
`PatternSpread`へ早期統合しない。

### Closed decisions and review focus

本追補でimplementationをblockするopen questionはない。次を確定する。

- list patternはcomma-only、empty / trailing comma validである。
- implicit newline / semicolonをvalid separatorにしない。
- spread RHSはfull recursive Patternである。
- parserはspread position / multiplicityを制限しない。
- ordinary itemはdirect Pattern、spreadは`ListPatternSpreadItem` wrapperである。
- exact `..`はlist-item-required contextのfixed syntaxで、dynamic operator tableから独立する。
- parenthesized / listはdelimiter mechanicsだけをclosed internal policyで共有し、public AST / CST ownerを統合しない。
- accepted bracket / spread後のmandatory-slot recoveryはtotalで、outer case/catch stopをconsumeしない。
- record / type / literal / constructor-tail patternを同時実装しない。

Claude reviewでは、特に`..tail`を許しつつ`...` / `..+`をprefix-splitしないlexical boundary、outer catch handler commaと
inner list commaのscope、spread RHS alternation extent、second spreadをparser Errorにしないphase boundary、newlineの
comma-only recovery、leading / repeated comma、missing spread RHSがcloseを守ること、missing-close時のouter arm stop escape、
parenthesized mechanics共有がtype-erased over-generalizationにならないことを確認対象にする。helper名、private range carrier、
typed diagnostic enumの具体名はcurrent sourceへ合わせて調整してよいが、surface grammar、CST shape、separator scope、
semantic deferralをopenに戻さない。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定、ユーザ承認済み
（2026-08-22、comma-delimited `ListPattern`とspread item grammar追補案）。

## 追補案: comma-or-newline-delimited `RecordPattern`とfield/default grammar

Status: Claude review / exact wordingのfinal sign-off待ち。

Date: 2026-08-22。

### Decision summary

already-implemented fixed-precedence pattern grammarへ、NUD-position primary `RecordPattern`を追加する。

```text
RecordPattern :=
    LBrace G*
    [ RecordPatternItem { RecordPatternSeparator RecordPatternItem } [ RecordPatternSeparator ] ]
    RBrace

RecordPatternSeparator := ExplicitCommaSeparator | ImplicitNewlineSeparator(record_base_indent)

RecordPatternItem := RecordPatternField | RecordPatternSpreadItem

RecordPatternField :=
    PatternFieldName
    [ G0 Colon G* Pattern@Lowest [ G0 Equals G* OperatorChain ]
    | G0 Equals G* OperatorChain
    ]

PatternFieldName := Identifier | SigilIdentifier
RecordPatternSpreadItem := DotDot G* Pattern@Lowest
```

`G*`はphysical newlineを含み得るmaximal lossless trivia、`G0`はphysical newlineを含まないmaximal triviaである。
field introducerの`:` / `=`はfield nameと同じphysical lineにある場合だけ、そのfieldへ属する。introducerをcommitした後の
mandatory nested pattern / default expressionはnewlineをまたいでよい。

このsliceは次を確定する。

- `{}`はvalid zero-item record patternである。
- separatorはliteral commaまたはlayout条件を満たすimplicit physical newlineである。semicolonは受理しない。
- terminal commaをvalidとし、そのrangeをASTにも保持する。
- field headはfull `Pattern`ではなくname-only `Identifier | SigilIdentifier`である。
- shorthand、colon nested-pattern、bare-defaultの三formを一個の`RecordPatternField` nodeで表す。
- colon formのRHSはtypeではなくfull recursive `Pattern`であり、optional `= OperatorChain`を持てる。
- bare `=` formとcolon formのdefault RHSはordinary precedence-neutral expression `OperatorChain`である。
- spread RHSはfull recursive `Pattern`であり、position / multiplicityをparserで制限しない。
- duplicate field name、spread cardinality / position、field binding/default semanticsはlater pattern HIR lowering / validationへ送る。

本追補はfirst-slice pattern addendumのrecord-pattern defer gateと、ListPattern追補の「future record-field sequenceをshared
delimited helperへ通さない」というprovisional statementをsupersedeする。concrete third userが成立したため、delimiter / comma /
close / retry mechanicsだけを`PatternDelimitedPolicy::Record`へ共有する。一方、field dispatch、embedded expression、AST / CST owner、
typed recovery roleはrecord固有のままにする。

### Re-verified Yulang2 grammar and evidence

Yulang2 specのproductionは次だった
(`yulang2-oracle@a58eefc3:spec/2026-06-06-syntax-design.md:1532-1551`)。

```text
pat_record =
  "{" ((pat_field | ".." pattern) ("," (pat_field | ".." pattern))* ","?)? "}"

pat_field =
  ident
  ident ":" pattern ("=" expr)?
  ident "=" expr
```

actual NUD dispatchはopen braceを`parse_pat_record_group`へ送り、一個の`PatRecord`を開始した
(`yulang2-oracle@a58eefc3:crates/parser/src/pat/parse.rs:296-305`)。record item machineは各item先頭で`DotDot`をprobeし、
spreadなら`PatSpread`内へfull `parse_pattern`を呼んだ。spread count / indexのstateはなく、first / middle / lastおよび
複数spreadをgrammarで区別しなかった (`crates/parser/src/pat/parse.rs:421-450`)。

ordinary fieldは`scan_pat_nud`のresultを受けた後、headが`Ident | SigilIdent`のatomであることを要求した。したがってspecの
`ident`よりactual implementationはsigil nameを含むが、integer、symbol、parenthesized pattern等のfull Pattern headは許さない
(`crates/parser/src/pat/parse.rs:451-464`)。sigil shorthand `{$x}` fixtureもこのshapeを固定する
(`yulang2-oracle@a58eefc3:crates/parser/tests/pat_grammar.rs:124-138`)。

name後のdispatchはtoken-by-tokenだった。trailing triviaがnewlineならshorthandを終了し、それ以外ではnext scanned tokenを
調べ、`Colon`ならfull nested pattern、`Equal`ならordinary expressionをparseした。colon branchだけはinner pattern stopへ
`Equal`を追加し、inner patternが返したexact `Equal`をoptional default introducerとしてconsumeした。その他のtokenはinvalid
だった (`crates/parser/src/pat/parse.rs:464-507`)。

このevidenceは`{width: local_width}`のcolonをgeneral pattern type annotationと読んではならないことを示す。actual CSTは
`PatField(Ident, Colon, Pattern)`であり、fixture名`pat_record_field_with_type_ann`もexpected treeでは`TypeAnn`を含まない
(`yulang2-oracle@a58eefc3:crates/parser/tests/pat_grammar.rs:234-276,425-453`)。bare / colon defaultはboth
`PatField(... Equal, Expr)`だった (`crates/parser/tests/pat_grammar.rs:255-276,456-483`)。

explicit separator predicateはcommaだけだった (`crates/parser/src/pat/parse.rs:421-428`)。ただしshared
`DelimitedListMachine`はcurrent base indent以下のphysical newlineをempty `Separator` nodeとして受理した
(`yulang2-oracle@a58eefc3:crates/parser/src/parse/mod.rs:21-23,35-67`)。recordにはlistと違い、このbehaviorを直接固定する
`{a\nb}` fixtureが存在する (`yulang2-oracle@a58eefc3:crates/parser/tests/pat_grammar.rs:102-121`)。

spread fixturesはhead `{ ..rest, width = 1 }`とtail `{ width = 1, ..rest }`、field fixturesはshorthand、sigil shorthand、
colon nested pattern、colon + default、bare defaultをcoverする
(`crates/parser/tests/pat_grammar.rs:124-198,234-276,425-483`)。empty、malformed head、missing RHS / close、duplicate name、
middle / multiple spread、mixed field-form recoveryのfixtureはない。Yulang3 recoveryはhistorical outputを推測せず、existing typed
mandatory-slot contractから定義する。

### Separator scope: shared comma-or-newline rule

`RecordPattern`は末尾の「layout-aware comma-or-newline delimited sequence」追補をそのまま使う。open brace直後のtriviaを
読んだ時点で`record_base_indent`をsnapshotし、item後のphysical newlineのfollowing-line indentがbase以下ならimplicit
separator、baseよりdeepならcurrent field / spread patternのcontinuation triviaとする。semicolonはvalid separatorではない。

これはYulang2のrecord-specific fixture `{a\nb}`を復元し、同じshared mechanismをparenthesized / list patternにも適用する決定である。
newlineはraw triviaとして一度だけ保持し、sourceにないcomma tokenやempty Separator nodeを合成しない。

| source | result |
| --- | --- |
| `{}` | valid empty record |
| `{a}` | valid shorthand field |
| `{a,}` | valid shorthand + trailing comma |
| `{a,\n b}` | valid two fields。newlineはcomma後trivia |
| `{\n  a\n  b\n}` | base 2で二shorthand field。二newline boundaryはいずれもvalid |
| `{a\nb}` at base 0 | equal-indent newlineで二shorthand field。Missingなし |
| `{a\n  b}` at base 0 | deeper newlineはseparatorでなくfield continuation。`b`をnext fieldへ昇格しない |
| `{a; b}` | semicolonはnon-empty separator `Error`。valid separatorではない |

explicit commaがあるboundaryではcommaをauthorityとし、その後ろのnewline triviaをsecond separatorへ数えない。qualifying newlineの
直後にcommaがある場合も一個のboundary clusterとしてcommaを優先し、empty item / duplicate boundaryを合成しない。

### Field head and three-way dispatch

`RecordPatternField`は一個のname-only headと、source punctuationで決まるoptional bodyを持つ。

```text
PatternFieldName := Identifier | SigilIdentifier

RecordPatternField :=
    PatternFieldName
    [ G0 Colon G* Pattern@Lowest [ G0 Equals G* OperatorChain ]
    | G0 Equals G* OperatorChain
    ]
```

field name scannerはexisting `scan_pattern_name`をreuseする。CSTでは`IdentifierPattern`へ包まず、literal
`Identifier | SigilIdentifier` tokenを`RecordPatternField`直下へemitする。ASTではexisting `PatternNameSpan`を使い、bare `_`は
ordinary name、`_bar` / `$x`等はsigil nameである。binding / constructor / wildcard意味をparserで決めない。

name後のrecognition priorityを次で固定する。

1. physical newlineを含まないtrivia `G0`とexact `Colon`をsink-free composite probeする。成立すればcolon formへcutする。
2. 同じ`G0`とexact `Equals`をprobeする。成立すればbare-default formへcutする。
3. matching comma / right brace、qualifying same-or-shallower newline、captured outer safe pointならshorthandとしてfieldを終了する。
4. deeper newlineはfield continuation triviaである。次tokenがvalid same-field suffixでなければfield-local recoveryを行い、next itemへ
   昇格しない。
5. same logical lineに次のrecord item candidateがあればshorthandを終了し、outer loopがmissing separatorをemitしてretryする。
6. その他はfield continuation / separatorのnon-empty `Error`としてrecoverし、next item candidateまたはcloseを守る。

probeがrejectした`G0`はfieldへcommitしない。shorthand後のtriviaとしてouter record nodeがemitする。line commentまたはblock
comment内newlineがqualifying boundaryなら、その後ろにある`:` / `=`もprior fieldへattachしない。一方、introducerをcommitした後の`G*`は
newlineを含めてmandatory RHSへ属し、`{x:\n  pattern}`と`{x =\n  expression}`を許す。

三formは一個の`SyntaxKind::RecordPatternField`を共有する。fieldというliteral grammar owner、name slot、duplicate-name validation
boundaryが同じであり、違いはsourceに`Colon` / `Equals`とRHSがあるかという内部shapeだけだからである。三node kindへ分けると
missing introducer / RHS recoveryがfield identityを変え、downstreamが同じfield sequenceをvariant node名から再構成することになる。

single wrapperはform差を消さない。ASTは`RecordPatternFieldForm::{Shorthand, Nested, Default}`でexact formを保持し、CSTはliteral
tokens / child nodeのpresenceで区別する。colon formを`PatternTypeAnnotationTail`へ流用せず、bare defaultをbinding statementへ
流用しない。

### Exact `=` ownership and embedded expression boundary

current `StopKind`には`Equal`がない一方、`SyntaxKind::Equals`と`PunctuationEvidence::Equals`は既にある。fixed punctuation scannerは
`=`をdynamic-operator territoryへ残している。本sliceは次を追加する。

```text
StopKind::Equal
```

record field-required positionではdeclaration-independentなmaximal operator-shaped spellingをprobeし、candidate textがexact
`=`のときだけfixed `Equals`としてacceptする。`==`、`=>`、`=+`等を`=` + remainderへsplitしない。operator headerで`=`の
fixity / BPが宣言されても、field introducer positionのexact `=` ownershipは変わらない。

colon formのnested patternにはlocal stops `{ Equal, Comma, RightBrace }`を与える。pattern NUD / LED / mandatory-primary recoveryは
exact `=` pendingをcaller-owned boundaryとして扱い、consumeしない。recursive parenthesized / list / record patternはown delimiter
scopeをpushしてouter `Equal` stopをsuspendし、matching close後にrestoreする。このため
`{outer: {x = 1} = fallback}`のinner equalsはinner record field、second equalsはouter field defaultになる。

accepted colon後、exact `=`がnested-pattern-required positionに来た場合はzero-width missing `Pattern`をemitした後、同じequalsを
optional default introducerとしてconsumeする。`=`自体はoptionalなので、colon + valid Patternの後にequalsがないことへdiagnosticを
出さない。equalsがliteralに存在してRHS expressionがない場合だけmissing default expressionを出す。

bare / colon defaultのRHS ownerはordinary expression grammarである。

```text
RecordPatternDefault := Equals G* OperatorChain
DefaultExpressionStops := { StopKind::Comma, StopKind::RightBrace }
```

AST pathは`parse_expression_with_operators`、direct-CST pathは`parse_direct_expression_with_operators`を呼ぶ。default RHSは
precedence-neutral flat `OperatorChain`のままであり、record parserがassociationしない。active comma stopにより
`{x = f: a, y}`のcommaはrecord separatorであり、colon applicationがinline argument listとして奪わない。commaをexpression内で
使う場合はparenthesized expression等のown delimiterを使う。

first-slice pattern entrypointは現在`OperatorTable`を受け取らないが、embedded expressionを正しくparseするにはcallerと同じ
immutable tableが必要である。implementation sliceでは`parse_pattern` / `parse_direct_pattern`とrecursive continuationsへ
`&OperatorTable`をthreadし、case/catchが既に持つtableを渡す。pattern NUD / LED、spread、field dispatchはtableを参照せず、
record default callbackだけがexpression parserへforwardする。standalone pattern fixturesもexplicit tableを用意する。

これはpattern precedenceをdynamic operatorへ変更するものではない。operator spelling / BP変更が影響できるのはliteral equals後の
`OperatorChain` subtreeだけで、`RecordPattern` / field / spread / delimiter shapeは変わらない。

### Spread scope and phase boundary

record spreadはListPatternと同じsurface contractを持つが、owner-specific nodeを使う。

```text
RecordPatternSpreadItem := DotDot G* Pattern@Lowest
```

- RHSはidentifier-only rest nameではなくfull recursive Patternである。
- exact maximal `..` probeをListPatternと共有し、`...` / `..+`をprefix-splitしない。
- first / middle / last、複数spreadをparser-validとする。
- parserはspread count、既出spread、field indexを保持しない。
- cardinality / position / capture semanticsはlater pattern HIR lowering / validationが一度検査する。

`RecordPatternSpreadItem`を`ListPatternSpreadItem`へ統合しない。同じmarker / RHS mechanicsをprivate callbackで共有できるが、record
field sequenceとlist element sequenceではlowering roleが異なる。source-local wrapperをowner-specificに保つことで、later phaseが
outer ancestorを再走査せずspread roleを得られる。

duplicate field nameもparserではrejectしない。`{a, a = 1, ..left, ..right}`はsurface-valid uniform sequenceであり、必要な
diagnosticはrecord-pattern validationが出す。

### Grammar and delimiter scope

full productionを次で固定する。

```text
PatternPrimary += RecordPattern

RecordPattern :=
    LBrace G*
    [
        RecordPatternItem
        { RecordPatternSeparator RecordPatternItem }
        [ RecordPatternSeparator ]
    ]
    RBrace

RecordPatternSeparator :=
    G* Comma G*
  | ImplicitNewlineSeparator(record_base_indent)

RecordPatternItem :=
    RecordPatternField
  | RecordPatternSpreadItem

RecordPatternField :=
    PatternFieldName
    [ G0 Colon G* Pattern@Lowest [ G0 Equals G* OperatorChain ]
    | G0 Equals G* OperatorChain
    ]

PatternFieldName := Identifier | SigilIdentifier
RecordPatternSpreadItem := DotDot G* Pattern@Lowest
```

accepted `LBrace`でcutした後、record ownerは次をpushする。

```text
delimiter = Delimiter::Brace
local stops = { StopKind::Comma, StopKind::RightBrace }
```

field colon RHSだけはこのsetへtemporary `StopKind::Equal`を加え、default expressionはouter two stopsへ戻す。incoming case/catch
Arrow / guard / handler comma、outer paren / bracket close等はbrace depthの外へsuspendするが、missing-close recovery用safe-point
snapshotとして保持する。matching `}`後にexact restoreする。

`{` / `}`はpattern entrypointでだけ`RecordPattern`を開始する。expression entrypointのsame bytesは引き続き
`BracedStatementBlockExpression`であり、そのstatement loop / `ColonApplicationTail` / CST nodeをrecord patternへ流用しない。
逆にrecord default RHS内の`{x: 1}`はexpression parserが読むため、`BracedStatementBlockExpression`になり得る。grammar familyは
entrypointとcurrent ownerで決まり、brace token単体でnode kindを共有しない。

### CST vocabulary and source-order shapes

本sliceで追加するkindは次である。

```text
SyntaxKind::RecordPattern
SyntaxKind::RecordPatternField
SyntaxKind::RecordPatternSpreadItem
```

`Pattern`、`Identifier`、`SigilIdentifier`、`Colon`、`Equals`、`DotDot`、`OperatorChain`、`LBrace`、`RBrace`、`Comma`、trivia、
`Missing`、`Error`はexisting kindを使う。`PatRecord` / `PatField` abbreviation、`RecordShorthandField`、
`RecordNestedPatternField`、`RecordDefaultField`、generic `PatternSpreadItem`、synthetic `Separator` nodeは追加しない。

`{a, width: local_width = 1, height = fallback, ..rest,}`は次のCST shapeになる。

```text
Pattern
  RecordPattern
    LBrace "{"
    RecordPatternField
      Identifier "a"
    Comma ","
    Whitespace " "
    RecordPatternField
      Identifier "width"
      Colon ":"
      Whitespace " "
      Pattern
        IdentifierPattern
          Identifier "local_width"
      Whitespace " "
      Equals "="
      Whitespace " "
      OperatorChain
        IntegerLiteral
          Integer "1"
    Comma ","
    Whitespace " "
    RecordPatternField
      Identifier "height"
      Whitespace " "
      Equals "="
      Whitespace " "
      OperatorChain
        IdentifierExpression
          Identifier "fallback"
    Comma ","
    Whitespace " "
    RecordPatternSpreadItem
      DotDot ".."
      Pattern
        IdentifierPattern
          Identifier "rest"
    Comma ","
    RBrace "}"
```

`{}`、`{a}`、`{a,}`、mixed form、one / many spreadのすべてがsame outer `RecordPattern` kindを持つ。all literal tokensとtriviaを
source orderで一度だけemitし、`green.to_string() == source`を維持する。

### Parser-side AST shape

existing `PatternPrimary`へ一variantを追加する。

```rust
pub(crate) enum PatternPrimary<'source> {
    Identifier(PatternNameSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Symbol(SymbolPattern<'source>),
    Parenthesized(ParenthesizedPattern<'source>),
    List(ListPattern<'source>),
    Record(RecordPattern<'source>),
}

pub(crate) struct RecordPattern<'source> {
    open: Range<usize>,
    items: Vec<Recovered<RecordPatternItem<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

pub(crate) enum RecordPatternItem<'source> {
    Field(RecordPatternField<'source>),
    Spread(RecordPatternSpreadItem<'source>),
}

pub(crate) struct RecordPatternField<'source> {
    name: PatternNameSpan<'source>,
    form: RecordPatternFieldForm<'source>,
    range: Range<usize>,
}

pub(crate) enum RecordPatternFieldForm<'source> {
    Shorthand,
    Nested {
        colon: Range<usize>,
        pattern: Recovered<Box<Pattern<'source>>>,
        default: Option<RecordPatternDefault<'source>>,
    },
    Default(RecordPatternDefault<'source>),
}

pub(crate) struct RecordPatternDefault<'source> {
    equals: Range<usize>,
    expression: Recovered<Box<OperatorChain<'source>>>,
    range: Range<usize>,
}

pub(crate) struct RecordPatternSpreadItem<'source> {
    marker: Range<usize>,
    rhs: Recovered<Box<Pattern<'source>>>,
    range: Range<usize>,
}
```

`RecordPatternField`はname probeがacceptedされた場合だけ開始するため、field内の`name`はalways completeである。malformed headは
outer `RecordPatternItem`の`Recovered::Incomplete`とdirect `Error`で表し、invalid tokenをfake name textへ変換しない。

colon / equals / spread markerがliteralに存在する場合、そのform node / enum variantをmissing RHSでも保持する。ASTはall comma /
triviaをduplicateせず、item order、field form、spread role、trailing comma、close recoveryを持つ。lossless spellingはCST authorityである。

### Shared delimited mechanics and record-specific callbacks

`PatternDelimitedPolicy`へthird variantを追加する。

```rust
enum PatternDelimitedPolicy {
    Parenthesized,
    List,
    Record,
}
```

`Record` policyは`Delimiter::Brace`、`StopKind::RightBrace`、`SyntaxKind::RBrace`、captured `base_indent`、
`ConstructRole::RecordPattern`、`PatternRole::RecordSeparator`を返す。shared
`parse_pattern_delimited_items_ast` / `commit_direct_pattern_delimited_items`はempty detection、raw comma emission、qualifying newline
classification、trailing explicit / implicit separator、missing separator same-position retry、close recovery、scope balanceだけを所有する。

record-specific callbackは次を所有する。

- item candidate priority: exact `..`、field-name candidate。
- spread wrapper kind / RHS role。
- name-only field head commit。
- same-line colon / equals composite probe。
- nested Patternのtemporary Equal stop。
- embedded OperatorChain parseとrecovery。
- malformed field continuationのsafe retry。

このboundaryならfield complexityをgeneric loopへ条件分岐として漏らさず、三containerのduplicate comma / close machineも作らない。
public ASTを`DelimitedPattern<T>`へ統合せず、expression argument、statement、case/catch arm、future record expression literalをhelperへ
通さない。

### Recognition / commit control flow

AST pathとdirect-CST pathはsame sink-free NUD / item / introducer probesを共有する。

```text
recognize_pattern_nud:
    existing arm / active fixed-stop priority
    symbol / name / integer / paren / bracket probes
    if fixed `{` opening is accepted:
        return PatternNudRecognition::Record { open }

commit_record_pattern(open):
    start RecordPattern; emit LBrace; push record scope
    emit maximal leading trivia

    if matching RBrace pending:
        emit close; pop scope; finish valid empty record
        return

    loop:
        commit one mandatory RecordPatternItem
        emit following trivia

        if explicit comma separator pending:
            emit trivia + raw Comma + following trivia
            if matching RBrace pending:
                record trailing comma; emit close; pop scope; finish
                return
            continue with one mandatory item

        if qualifying implicit newline separator pending:
            emit newline trivia once; do not emit Separator / Missing / token
            if matching RBrace pending:
                finish as valid trailing implicit separator
                emit close; pop scope; finish
                return
            continue with one mandatory item

        if deeper newline pending:
            return it to current item continuation / recovery; do not start next item

        if matching RBrace pending:
            emit close; pop scope; finish
            return

        if exact DotDot or field-name candidate pending:
            emit zero-width Missing(RecordSeparator)
            retry next item at same position
            continue

        recover one non-empty separator / continuation / close episode
        if item candidate found:
            retry next item
        else:
            recover/insert close; pop scope; finish
```

item commitは次である。

```text
commit_record_item:
    if exact DotDot pending:
        start RecordPatternSpreadItem; emit DotDot; cut
        emit trivia
        commit Pattern@Lowest with role RecordSpreadRhs
        finish spread item
        return

    if field-name pending:
        start RecordPatternField; emit Identifier or SigilIdentifier; cut

        probe G0 + exact Colon
        if accepted:
            emit G0 + Colon + G*
            push Equal stop
            commit mandatory Pattern@Lowest with role RecordNestedPattern
            pop Equal stop
            probe G0 + exact Equals
            if accepted:
                commit RecordPatternDefault
            finish field
            return

        probe G0 + exact Equals
        if accepted:
            commit RecordPatternDefault
            finish field
            return

        finish shorthand field without consuming rejected trivia
        return

    recover mandatory RecordItem slot
```

`commit RecordPatternDefault`は`Equals`とfollowing triviaをemitし、record comma / right-brace stops下でmandatory
`OperatorChain`を一個parseする。expression parserがNoneを返した場合はzero-width missing expressionをemitし、comma / qualifying
newline / close /
outer safe pointをconsumeしない。

accepted `{` / `..` / `:` / `=`後はalternativeへrollbackしない。probe中はsink call 0で、accepted trivia / tokenは一度だけemitする。
AST pathもsame stop push / pop orderとsame range boundaryを使う。

### Typed recovery contract

typed vocabularyへ次を追加する。

```text
PatternRole::{
    RecordItem,
    RecordFieldName,
    RecordNestedPattern,
    RecordDefaultExpression,
    RecordSpreadRhs,
    RecordSeparator,
}

ConstructRole::RecordPattern

ExpectedSyntax::Identifier
ExpectedSyntax::Pattern
ExpectedSyntax::Expression
ExpectedSyntax::Punctuation(Comma)
ExpectedSyntax::Punctuation(Equals)
ExpectedSyntax::Punctuation(Close(Brace))
ExpectedSyntax::DelimitedSequenceSeparator
```

new recovery primitiveは不要である。zero-width `Missing`、maximal non-empty `Error`、one committed recovery node = one diagnostic、
same-position retry、delimiter / lexical safe pointをexisting pattern container contractどおり使う。

| source situation | required recovery / CST ownership |
| --- | --- |
| `{}` | valid empty `RecordPattern`。Missingなし |
| `{a,}` | valid shorthand + raw trailing `Comma`。Missingなし |
| `{a, b: p, c = e, ..r}` | mixed field forms / spreadをsource orderでvalidに保持 |
| `{a\nb}` at base 0 | equal-indent newlineをvalid boundaryとして両fieldを保持。Missingなし |
| `{\n  a\n  b\n}` | captured base 2で二field + valid trailing implicit separator |
| `{a\n  b}` at base 0 | deeper newlineはcurrent field continuation。`b`をnext itemへsame-position retryしない |
| `{,a}` | comma位置にmissing `RecordItem`一件、commaを保持して`a`へ進む |
| `{a,,b}` | second comma位置にmissing item一件。両commaを保持し`b`へ進む |
| `{1, a}` | `1`をnon-empty `Error(RecordFieldName/RecordItem)`。full Pattern fieldへ昇格せずcomma後の`a`へ進む |
| `{@ a}` | `@`をnon-empty item `Error`、same mandatory slotを`a`からretry |
| `{a b}` | same-line `b`直前へzero-width missing delimited separator、両shorthandを保持 |
| `{a: p}` | complete colon nested-pattern field |
| `{a:}` | Colonを保持し、close位置へzero-width `Pattern > Missing(RecordNestedPattern)` |
| `{a:, b}` | comma位置へmissing nested Pattern一件。commaをrecord separatorとして保持 |
| `{a: = 1}` | colon form内にmissing nested Pattern、same exact Equalsをdefault introducerとしてconsume |
| `{a = value}` | complete bare-default field。RHSは`OperatorChain` |
| `{a =}` | Equalsを保持し、close位置へzero-width `OperatorChain > Missing(RecordDefaultExpression)` |
| `{a: p =}` | nested Patternを保持し、Equals後にmissing default expression |
| `{a: p}`でequalsなし | optional default absent。diagnosticなし |
| `{a\n: p}` with next indent `<= base` | newlineで`a` shorthand終了。Colonをprior fieldへattachせずnext-item Errorとして保持 |
| `{a\n  : p}` with next indent `> base` | deeper continuation内のinvalid field suffix。next itemを開始しない |
| `{..tail}` | complete record spread。RHSはfull Pattern |
| `{..}` | DotDotを保持したspread node内にmissing Pattern、`}`をconsumeしない |
| `{.., a}` | comma位置にmissing spread RHS一件、comma後の`a`へ進む |
| `{...a}` | `...`をDotDotへsplitせずnon-empty malformed item Error |
| `{..left, a, ..right}` | multiple / middle spreadをsurface-validに保持 |
| `{a, a}` | duplicate spellingもparser-valid。later validation owner |
| `{a` + EOF | fieldを保持し、EOFへzero-width `Missing(RBrace)`一件 |
| `{a]` | `]`をclosing-delimiter evidence付きnon-empty Errorにし、missing `}`へ進む |
| case arm内`{a -> body` | outer Arrowをconsumeせずmissing `}`を置き、scope restore後arm ownerへ返す |

malformed head / continuation recoveryはmatching `}`、comma、qualifying newline、exact spread、field-name candidate、exact caller-owned Equal、captured outer
safe point、EOFをconsumeしない。same positionへmissing separatorを二度emitせず、retryはitem commitまたはnon-empty Error consumptionで
必ずprogressする。

`==` / `=>` / `=+`はexact Equals boundaryではない。colon nested Patternのdefault markerにもfield bare-default introducerにも
prefix-splitせず、一個のmalformed continuation episodeとしてrecoverする。default expression内のsecond exact `=`はlocal
`StopKind::Equal`がactiveでないため、operator tableが許すならordinary dynamic operator useになり得る。

matching close recoveryはnested delimiter / opaque string・comment・interpolation region内の`}`をouter closeにしない。all exit
pathsでdelimiter / stop stackを一回ずつpopし、outer case/catch stopsとoperator table referenceをexact restoreする。wrapperはchild
parserが既に出したmandatory-slot diagnosticをduplicateしない。

### Existing architecture principlesとの整合

- **syntax-as-written CST:** field count / form、spread count / position、duplicate name、trailing commaでouter nodeを変えない。literal
  colon / equals / spreadだけをsource-local child shapeで示す。
- **independent pattern authority:** record primary、field dispatch、spread、fixed comma / brace scopeはpattern grammarが所有する。
  expression `BracedStatementBlockExpression` / `ColonApplicationTail`へdelegationしない。
- **embedded expression authority:** default RHSだけをordinary flat `OperatorChain` ownerへ渡す。record parserはdynamic operator useを
  recognize / associateしない。
- **fixed precedence:** nested / spread RHSはexisting `Pattern@Lowest`であり、新しいpattern precedence levelや`BpVec`を要求しない。
- **immutable operator table:** tableはdefault expression callbackへforwardするだけで、record field / spread recognitionには使わない。
- **oracle judge separation:** `{` primary、field-name、exact `..`、same-line `:` / `=`をsmall pattern / record item judgeへ追加し、
  expression operator oracleへ混ぜない。
- **rollback discipline:** open / close / comma / name / exact introducer / next-item candidateはsink-free probe、accept後cut、forward-only
  emitとする。rejected `G0`をemitしてからrollbackしない。
- **lexical-region awareness:** brace delimiterがnested pattern / embedded expression / opaque regionとouter case stopsを分離する。
- **mandatory-slot recovery:** accepted colon / equals / spreadはmissing RHSでもowner nodeを閉じる。missing separatorはsame-position retry、
  malformed episodeはnon-empty Errorでprogressする。
- **semantic deferral:** field-name meaning、duplicate name、default semantics、spread cardinality / position / captureをlater lowering /
  validationへ送る。
- **container consistency:** parenthesized / list / record patternはcomma-or-qualifying-newline、empty、trailing explicit / implicit separator
  validというsame surface policyを持つ。
- **CST family separation:** expression brace blockとrecord patternはscanner-level bracesだけを共有し、CST / AST / sequence authorityを
  共有しない。

### Implementation boundary and required gates

implementation sliceは`crates/yu-syntax/src/grammar/pattern.rs`を中心に次を行う。

1. AST / NUD recognitionへ`RecordPattern`、field、spread、default typesを追加する。
2. `SyntaxKind::{RecordPattern, RecordPatternField, RecordPatternSpreadItem}`とrowan conversionを追加する。
3. `PatternDelimitedPolicy::Record`、`ConstructRole::RecordPattern`、record-specific `PatternRole`を追加する。
4. pattern entrypoint / recursive continuationsへimmutable `&OperatorTable`をthreadし、case/catch callersとstandalone fixturesを更新する。
5. `StopKind::Equal`とexact maximal `=` probeを追加し、pattern boundary / recoveryへ接続する。
6. existing exact `..` probeをrecord spreadへreuseし、owner-specific CST wrapperをemitする。
7. shared delimited coreへRecord item candidate / commit / recovery callbackを追加し、field state machine自体はrecord-specificに保つ。
8. AST-only / direct-CST parity、typed diagnostics、all scope restorationをfixtureで固定する。

required gatesは次である。

1. `{}`、`{a}`、`{a,}`、`{a,b}`、`{a,b,}`がuniform `RecordPattern`とexact item count / trailing markerを持つ。
2. ordinary / sigil shorthandがdirect field-name tokenを持ち、`IdentifierPattern` wrapperを作らない。
3. colon nested pattern、colon + default、bare defaultがsame `RecordPatternField` kindとdistinct AST formを持つ。
4. `{width: local_width}`のRHSがPatternであり、type annotation nodeにならない。
5. default RHSがflat `OperatorChain`になり、declared operatorsをcallerのimmutable tableでrecognizeする。
6. `{a,\n b}`、equal-indent `{a\nb}`、multiline-base formはvalid、deeper newlineはcontinuation、`{a; b}`はseparator Errorになる。
7. qualifying `{a\n: p}`がcolonを`a`へattachせず、deeper newline suffixをfield-local recoveryし、`{a:\n p}`はvalid colon formになる。
8. missing field head / nested Pattern / default expression / spread RHSがliteral introducerとclose / commaを守る。
9. same-position retryがmissing separator before field / spread、leading / repeated comma、malformed itemを一件ずつrecoverする。
10. `[..]`相当のrecord spread、first / middle / last / multiple spreadをsurface-validに保持する。
11. `...` / `..+`、`==` / `=>` / `=+`をfixed markerへprefix-splitしない。
12. nested record/list/paren patternsがouter Equal / Comma / RightBrace stopをsuspend / restoreする。
13. missing / mismatched brace、outer arm Arrow / guard escape、opaque lexical regionsでscope stackがbalancedになる。
14. expression source `{x: 1}`は引き続き`BracedStatementBlockExpression`、pattern source `{x: p}`だけが`RecordPattern`になる。
15. all probesでsink call 0、accepted emission一回、`green.to_string() == source`、AST/direct parityを満たす。
16. existing parenthesized / list pattern、case/catch、expression block / colon application、operator testsを維持する。

### Explicit future scope

本追補は次を設計しない。

- general pattern type annotation `Pattern : Type`とtype-expression grammar。
- string / rule literal pattern。
- field / path / no-space constructor call / ML application pattern tail。
- record expression literal dedicated node。expression `{...}`はcurrent statement-block primaryのままである。
- record pattern fieldのtype interpretation。colon RHSは本sliceでは常にPatternである。
- field-name resolution、duplicate-field validation、default evaluation / omission semantics。
- spreadのruntime matching algorithm、capture representation、count / position制約。
- semicolon-separated record pattern。
- declaration body、if brace-body、catch brace-arm-list、rule / use / interpolation brace grammarとの統合。

future type annotation tailが追加されても、record field name直後のcolonはfield ownerが先にconsumeする。record nested Pattern内のcolonは
そのfuture pattern grammarに従い得るが、outer field colonとsame CST nodeへmergeしない。

### Closed decisions and review focus

本追補でimplementationをblockするopen questionはない。次を確定する。

- record patternはcomma-or-qualifying-newline、empty / trailing explicit / implicit separator validである。
- Yulang2のtested implicit-newline record separatorをshared Yulang3 mechanismとして復元する。
- field headはname-onlyで、三formは一個の`RecordPatternField` kindを共有する。
- colon RHSはfull Pattern、default RHSはflat OperatorChainである。
- field introducerはsame-line exact `:` / `=`、committed introducer後のRHSはnewlineをまたげる。
- colon nested Patternだけがtemporary exact `StopKind::Equal`を持つ。
- spread RHSはfull Patternで、position / multiplicityをparserで制限しない。
- record / list spreadはprivate mechanicsを共有してもowner-specific CST nodeを維持する。
- `PatternDelimitedPolicy::Record`はcontainer mechanicsだけを共有し、field parserをgenericizeしない。
- expression brace block / colon applicationとrecord-pattern grammarを統合しない。

Claude reviewでは、特にYulang2-compatible base-indent snapshot、name後boundary newlineとintroducer後newlineの非対称、exact equalsが
`==`等をsplitしないこと、missing colon Patternの位置にequalsがある場合のhandoff、nested delimiterがouter Equal stopをsuspendする
こと、default expression comma ownership、case/catch table threading、multiple spread / duplicate fieldのphase boundary、shared
delimited policyがrecord field stateを吸収しすぎないこと、expression `{x: 1}`とのCST separationを確認対象にする。helper名、private
recovery carrier、table contextの具体的な型名はcurrent sourceへ合わせて調整してよいが、surface grammar、CST shape、separator
scope、phase ownershipをopenに戻さない。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定、ユーザ承認済み
（2026-08-22、comma-or-newline-delimited `RecordPattern`とfield/default grammar追補案）。

## 追補案: layout-aware comma-or-newline delimited sequence authority

Status: Claude review / exact wordingのfinal sign-off待ち。

Date: 2026-08-22。

### Supersession scope

本追補は、次のapproved / implemented grammarにある**comma-only separator decisionだけ**をsupersedeする。

1. `ParenthesizedExpression`。
2. `ParenthesizedPattern`。
3. `ListPattern`。
4. `ColonApplicationTail::InlineColonArguments`。

同時に、まだuser-approvedでない直前の`RecordPattern`追補をcomma-or-newline ruleへin-place revisionした。

各constructのouter node、item grammar、AST element type、trailing comma marker、tuple / grouping interpretation、spread / field semantics、
operator-chain flatness、recovery vocabularyは変更しない。変更するのはseparator recognition、layout base、newline ownership、関連する
validity / recovery gatesだけである。

### Re-verified Yulang2 `DelimitedListMachine`

canonical implementationは`yulang2-oracle@a58eefc3:crates/parser/src/parse/mod.rs:9-79`にある。
`parse_delimited_list`はopen lexemeをemitした直後、そのopen tokenが既にscanしたtrailing triviaから`leading_info`を得て、次で
`base_indent`を一度だけsnapshotした (`:25-33`)。

```text
opening_info = open_lex.trailing_trivia_info()

base_indent =
    opening_info is Newline { indent } and indent > incoming_env_indent
        ? indent
        : incoming_env_indent
```

したがってbaseはfirst itemをparseした後に決まるのではない。openをacceptし、その直後のtriviaをscan済みにした時点で固定する。
inline openならincoming container / expression indent、open直後にdeeper-indented lineがあればそのfirst content lineのindentがbaseになる。

item parserが`Either::Left(TriviaInfo::Newline { indent, .. })`を返した場合、generic machineは`indent <= base_indent`ならimplicit
separatorをacceptした (`:21-23,41-49`)。strictly deeper `indent > base_indent`ならlistを継続せずcallerへtriviaを返した。
各item parserは一時的に`env.indent = base_indent`とし、expression tail自身も`newline indent <= env.indent`でcurrent itemを止めた
(`yulang2-oracle@a58eefc3:crates/parser/src/expr/group.rs:81-116`;
`crates/parser/src/expr/tail.rs:21-45`)。これによりdeeper newlineはitem grammarへ残り、equal / shallowerだけがcontainer boundaryへ
戻った。

implicit branchはsource tokenを持たないempty `Separator` nodeをemitした。explicit separator branchは
`Separator(Comma)`またはconstructが許す`Separator(Semicolon)`をemitした
(`yulang2-oracle@a58eefc3:crates/parser/src/parse/mod.rs:43-46,62-66`)。pattern paren `(A\nB)`とrecord `{a\nb}`のfixtureは
empty `Separator` shapeを直接固定する
(`yulang2-oracle@a58eefc3:crates/parser/tests/pat_grammar.rs:57-77,102-121`)。

explicit / implicitのpriorityは一個のcombined probeではなかった。item parserがliteral separatorを`Right(stop)`で返せばexplicit
branch、newline boundaryを`Left(info)`で返せばimplicit branchへ入った。comma直後のnewlineはcomma tokenのtrailing triviaとして
next itemへ渡るためsecond separatorにならない。newline後にcommaが来る場合はhistorically implicit branchの次iterationでcommaを
explicit separatorとして処理し得た。Yulang3は後述のboundary-cluster normalizationで、このsource episodeを一logical boundaryへ
正規化する。

`PatExprListMachine`、`PatListItemMachine`、`PatRecordFieldMachine`はexplicit `Comma`だけを列挙しながらsame generic implicit ruleを
継承した (`yulang2-oracle@a58eefc3:crates/parser/src/pat/parse.rs:328-408,421-450`)。expression `ExprListMachine`はexplicit
`Comma | Semicolon`だった (`crates/parser/src/expr/group.rs:72-116`)。本追補の五constructはsemicolonを復元せず、comma + generic
newline mechanismだけを採用する。

Yulang2 colon inline argument loopはgeneric machineを使わずincoming comma stopだけを見た
(`yulang2-oracle@a58eefc3:crates/parser/src/expr/tail.rs:304-349`)。colonへのnewline extensionはYulang2 codeの機械的復元ではなく、
user-confirmed Yulang3 unified mirroring ruleである。

### Unified Yulang3 rule

shared conceptを`LayoutDelimitedSequence`と呼ぶ。

```text
LayoutDelimitedSequence<Item, Close> :=
    Open OpeningTrivia
    [ Item { DelimitedSeparator Item } [ DelimitedSeparator ] ]
    Close

DelimitedSeparator :=
    ExplicitCommaBoundary
  | ImplicitNewlineBoundary(base_indent)

ImplicitNewlineBoundary(base_indent) :=
    maximal trivia run containing physical newline
    whose following-line indentation <= base_indent
```

semicolonはこのshared policyに含めない。brace statement block等、semicolonを持つsequenceはown policyを維持する。

#### Base-indent snapshot

delimiter ownerはopening tokenをaccept / cutした直後、first itemをparseする前に次を行う。

```text
incoming_base = current indentation baseline
opening_trivia = maximal trivia immediately following opener

base_indent =
    opening_trivia ends after a physical newline
    && following_line_indent > incoming_base
        ? following_line_indent
        : incoming_base
```

`ParenthesizedExpression` / `ParenthesizedPattern`は`(`、`ListPattern`は`[`、`RecordPattern`は`{`をopenerとする。
base snapshotはitem content、operator spelling、pattern tail、later recoveryから再計算しない。nested containerはown frameをpushし、closeで
popしてouter frameをrestoreする。

`InlineColonArguments`はdelimiterを持たないため、accepted `:`をopener-equivalentとする。ただしcolon直後にphysical newlineがあれば
existing inline-vs-indented classifierが先に走る。deeper newlineは`IndentedStatementBlock`、same / shallower newlineはmissing /
outer-boundary pathであり、inline listを開始しない。inline first argumentが始まった場合のlist baseはcolonを含むcurrent expression /
statement lineのincoming baseで固定し、first argument後のnewlineからunified separator ruleを適用する。

#### Boundary classification

completed itemが返したmaximal trailing triviaについて、ownerは次をsource orderで判定する。

1. current-depth explicit commaが同じinter-item episodeにあれば`ExplicitCommaBoundary`を選ぶ。
2. commaがなく、triviaがphysical newlineを含み、following-line indent `<= base_indent`なら
   `ImplicitNewlineBoundary`を選ぶ。
3. following-line indent `> base_indent`ならseparatorではない。triviaをcurrent item continuationへ返す。
4. newlineがなくnext item candidateが始まればmissing separator recoveryでsame-position retryする。

explicit commaの前後にqualifying newlineがあっても一logical boundaryである。commaをliteral authorityとし、newline triviaを一度だけ
保持する。Yulang2がnewline-before-commaを二iterationで扱い得た点は、Yulang3ではempty item / duplicate diagnosticを作らない
boundary clusterへnormalizeする。repeated literal commaは従来どおりmissing item recovery対象であり、このnormalizationに含めない。

ruleはexhaustiveである。physical newlineはcaptured baseとの比較により`<=` boundaryまたは`>` continuationのどちらかになる。
「boundaryでもcontinuationでもないnewline」というthird stateを作らない。opaque lexical region内のnewlineはtrivia classifierへ出ず、
separatorにならない。

#### CST / AST representation

Yulang3はYulang2のempty `Separator` nodeを移植しない。implicit boundaryのphysical newline / whitespace / commentはmaximal triviaとして
container直下へsource orderで一度だけemitし、sourceにないtoken、`Missing(Comma)`、zero-width `Separator` nodeを合成しない。

item nodeが一度閉じ、trivia後にnext item nodeが始まるCST hierarchyと、trivia末尾のfollowing-line indentがboundary factを完全に
表す。formatter / loweringがsource-absent nodeを必要とせず、`green.to_string() == source`を維持できる。explicit commaは従来どおり
raw `Comma` tokenをcontainer直下へemitする。

parser-side ASTのseparator listは追加しない。`elements/items/arguments`のchild countとliteral `trailing_comma`だけを維持する。
trailing implicit newlineはvalid sequence terminatorだが`trailing_comma`を`Some`にしない。したがってone-element
`(a\n)`のnewlineがqualifying trailing boundaryでも、literal commaがない限り`(a)`と同じgrouping / identity classificationである。
二element `(a\nb)`はchild countによってtupleになる。

#### Shared session contract

implementationはhard-coded newline checksを五loopへ複製せず、session-local typed frameを使う。

```rust
struct LayoutDelimitedFrame {
    owner: LayoutDelimitedOwner,
    base_indent: usize,
    delimiter_depth: usize,
    explicit_comma: bool,
    implicit_newline: bool,
}
```

frameはseparator probe、item parserへのlayout baseline、close / recovery safe point、colon outer-ownership queryを一箇所で提供する。
matching / missing / malformed close、missing item、EOFの全pathでexactly once popする。`StopKind::Comma` / right-delimiter stopは引き続き
token ownershipに使い、newline ownershipをbooleanの推測やraw stop-set unionだけで表さない。

### ColonApplicationTail outer ownership

old ruleの`incoming StopKind::Comma`だけを見る判定を次へ置き換える。

```text
outer_owns_inline_argument_sequence :=
    current lexical depthにactive outer sequence authorityがあり、
    そのownerがcommaまたはlayout newline boundaryをclaimする
```

outer ownerにはparenthesized / list / record containerだけでなく、`IndentedStatementBlock`、
`BracedStatementBlockExpression`、case/catch arm sequence等のcurrent item / statement boundary ownerを含む。nested delimiter内へ入った
outer frameはsuspendし、current lexical depthのtop ownerだけを問う。

- `outer_owns_inline_argument_sequence == false`: colon tailはown inline frameをpushし、commaとqualifying newlineの両方で
  one-or-more argumentsをparseする。
- `true`: colon tailはexactly one `OperatorChain`だけをparseし、commaもqualifying newlineもconsume / classifyせずouter ownerへ返す。

commaだけまたはnewlineだけをcolonが部分所有するstateは作らない。これによりroot expression `f: a, b`やouter sequenceを持たない
standalone `f: a\nb`はmulti-argumentになり得る。一方、`(f: a, b)`、parenthesized multiline element、brace / indented statement内の
colon applicationではouter sequenceがboundaryを保持し、colon RHSは一argumentで終了する。

colon直後のnewlineによる`IndentedStatementBlock` triggerはこのinline ownership判定より先に行い、変更しない。今回のnewline
separatorはinline first argumentが既に始まった後のargument間だけに適用する。

### Construct-specific authoritative revisions

#### `ParenthesizedExpression`

```text
ParenthesizedExpression :=
    LParen OpeningTrivia
    [
        OperatorChain
        { ParenthesizedExpressionSeparator OperatorChain }
        [ ParenthesizedExpressionSeparator ]
    ]
    RParen

ParenthesizedExpressionSeparator :=
    ExplicitCommaBoundary
  | ImplicitNewlineBoundary(parenthesized_expression_base)
```

| source | classification |
| --- | --- |
| `()` | zero elements |
| `(a)` | one element, no trailing comma |
| `(a,)` | one element, literal trailing comma / one-tuple |
| `(\n  a\n  b\n)` | base 2、two elements、valid trailing implicit boundary |
| `(a\nb)` at base 0 | equal-indent newline、two elements |
| `(a\n  b)` at base 0 | deeper continuation inside first OperatorChain、not a second element boundary |

qualifying newline前に`Missing(Comma)`をemitしない。deeper newline後にcurrent OperatorChainがvalid continuationをconsumeできない場合は
expression-local recoveryであり、list loopが`b`をnew elementへ昇格しない。`trailing_comma` / infer-side tuple ruleは変更しない。

#### `ParenthesizedPattern`

```text
ParenthesizedPattern :=
    LParen OpeningTrivia
    [
        Pattern@Lowest
        { ParenthesizedPatternSeparator Pattern@Lowest }
        [ ParenthesizedPatternSeparator ]
    ]
    RParen

ParenthesizedPatternSeparator :=
    ExplicitCommaBoundary
  | ImplicitNewlineBoundary(parenthesized_pattern_base)
```

`(A\nB)` at base 0と`(\n  A\n  B\n)`をvalid two-pattern formとし、Yulang2 fixtureを復元する。deeper newlineは
current Pattern continuationへ残る。semicolonはinvalidのままである。empty / terminal comma / uniform node / alias / alternation
precedenceは変更しない。

#### `ListPattern`

```text
ListPattern :=
    LBracket OpeningTrivia
    [
        ListPatternItem
        { ListPatternSeparator ListPatternItem }
        [ ListPatternSeparator ]
    ]
    RBracket

ListPatternSeparator :=
    ExplicitCommaBoundary
  | ImplicitNewlineBoundary(list_pattern_base)
```

| source | result |
| --- | --- |
| `[]` | valid empty list |
| `[a,]` | valid literal trailing comma |
| `[\n  head\n  ..middle\n  tail\n]` | base 2、three items、valid trailing implicit boundary |
| `[a\nb]` at base 0 | valid two items |
| `[a\n  b]` at base 0 | deeper continuation in first Pattern、not a second list item |
| `[a; b]` | separator Error。semicolon invalid |

ordinary / spread item node、full Pattern spread RHS、unrestricted spread position / multiplicity、exact `..` ruleを変更しない。
qualifying newline before ordinary / spread candidateはmissing comma recoveryでなくvalid boundaryである。

#### `InlineColonArguments`

```text
InlineColonArguments(no_outer_sequence_owner) :=
    OperatorChain
    { InlineColonArgumentSeparator OperatorChain }
    [ ImplicitNewlineBoundary(colon_inline_base) ]

InlineColonArgumentSeparator :=
    ExplicitCommaBoundary
  | ImplicitNewlineBoundary(colon_inline_base)

InlineColonArguments(outer_sequence_owner) :=
    OperatorChain
```

literal trailing commaは従来どおりinvalid / outer-ownedであり、colon own listのvalid trailing separatorへ追加しない。qualifying
newlineだけはsource tokenを持たない自然なline terminationでもあるため、final implicit boundaryをvalidとする。outer owner caseでは
trailing newlineもouterへ返す。

| source context | colon ownership |
| --- | --- |
| standalone `f: a, b` | colon owns comma、two arguments |
| standalone base-0 `f: a\nb` | colon owns qualifying newline、two arguments |
| standalone base-0 `f: a\n  b` | deeper continuation inside first argument |
| `(f: a, b)` | parenthesized owner active、colon one argument、comma outer-owned |
| multiline parenthesized / list item内 | outer frame active、colon one argument、qualifying newline outer-owned |
| indented / braced statement sequence内 | statement owner active、colon one argument、statement newline outer-owned |

#### `RecordPattern`

直前のRecordPattern追補をin-placeで次へ更新済みである。

```text
RecordPattern :=
    LBrace OpeningTrivia
    [
        RecordPatternItem
        { RecordPatternSeparator RecordPatternItem }
        [ RecordPatternSeparator ]
    ]
    RBrace

RecordPatternSeparator :=
    ExplicitCommaBoundary
  | ImplicitNewlineBoundary(record_pattern_base)
```

`{a\nb}`をvalid two-shorthand recordとして復元する。deeper newlineはfield / spread RHS continuationであり、next itemを開始しない。
field form、same-line field `:` / `=` introducer、nested Pattern、default OperatorChain、exact Equal stop、spread、CST / AST shapeは変更しない。

### Recovery corrections shared by all five constructs

| situation | corrected recovery |
| --- | --- |
| qualifying newline between complete items | valid boundary。Missing / Errorなし |
| qualifying trailing newline before close | valid trailing implicit boundary。empty itemを作らない |
| deeper newline | current item continuationへ返す。next item same-position retryを行わない |
| same-line next item candidate without comma | zero-width missing delimited separator、same-position retry |
| explicit comma followed by newline | one explicit boundary。newlineはfollowing trivia |
| qualifying newline followed by comma | one boundary cluster、literal commaをauthorityとしempty itemを作らない |
| repeated literal comma | existing missing-item recoveryを維持 |
| semicolon | non-empty separator Error。五constructではvalidにしない |
| missing close after implicit boundary | newline triviaを保持し、close-owned zero-width Missing一件 |
| caller-owned comma / newline in colon RHS | colon consumes neither。outer ownerが一回だけ処理 |

missing separator diagnosticのprimary expectationは表示上`comma or layout newline`を表せるtyped
`ExpectedSyntax::DelimitedSequenceSeparator`へ広げる。source位置にnewlineが既にあるqualifying caseではdiagnostic自体を作らない。

### Architecture interactions and implementation gates

- **syntax-as-written CST:** implicit boundaryはliteral newline triviaとsibling item boundaryで表し、source-absent token / nodeを作らない。
- **single layout authority:** base snapshotと`<=` / `>` classificationをshared helperへ集約し、五loopで再実装しない。
- **rollback discipline:** opening trivia / trailing trivia / comma clusterをsink-free probeし、classification後に一度だけemitする。
- **lexical-region awareness:** opaque region内newlineをseparatorにせず、nested delimiter frameがouter authorityをsuspendする。
- **flat OperatorChain:** deeper newlineはcurrent flat chainへ残り、separator loopがoperator / primary contentからboundaryを推測しない。
- **fixed pattern precedence:** pattern NUD / LED precedenceは変更せず、caller containerがreturned layout boundaryだけを分類する。
- **colon terminality:** terminal outer tail / inline-vs-indented ruleを維持し、inline argument sequence ownershipだけを拡張する。
- **incremental stability:** trivia indentation editはaffected container sequence / descendantsをinvalidateするが、operator table BP変更とは独立する。

implementation sliceのrequired gatesは次である。

1. shared base snapshotがinline open、open直後deeper newline、nested containerでYulang2 formulaと一致する。
2. each constructでequal / shallower newlineがvalid、deeper newlineがcontinuationになる。
3. comma + newline clusterを一boundaryとしてemitし、repeated comma recoveryは維持する。
4. implicit boundaryでempty Separator / Missing commaをemitせず`green.to_string() == source`を満たす。
5. trailing implicit boundaryがvalidで、AST `trailing_comma`はliteral commaだけを表す。
6. parenthesized expression / pattern、list / record patternでnested delimiter scopeがouter base / ownerをrestoreする。
7. colon root-owned comma / newline multi-argumentとouter-owned exactly-one argumentを両方fixture化する。
8. colon post-introducer newlineのIndentedStatementBlock classificationを変更しない。
9. missing close / malformed item / outer arm stopでframeをexactly once popし、diagnosticを重複しない。
10. existing tuple / spread / field / default / operator-chain AST and CST assertionsはseparator関連以外を変更しない。

### Closed decisions and review focus

本追補でimplementationをblockするopen questionはない。次を確定する。

- baseはopen accept直後、opening triviaとincoming indentからYulang2 formulaで一度だけ決める。
- newline following indent `<= base`はseparator、`> base`はcontinuationである。
- implicit separatorはCST node / tokenを合成せずliteral triviaとitem hierarchyで表す。
- explicit commaとqualifying newlineの同一episodeは一boundary clusterにする。
- five constructsはcomma + implicit newlineを持ち、semicolonを持たない。
- colonはouter sequence ownerがなければcomma / newline両方を所有し、あればexactly one argumentに制限する。
- trailing implicit newlineはvalidだが`trailing_comma` markerではない。
- separator以外の各construct designを変更しない。

Claude reviewでは、特にYulang2 base snapshot formula、newline-before-comma normalization、open-inlineとopen-newlineのbase差、deeper
newlineをmissing separatorへ誤変換しないこと、one-element trailing newlineとtuple interpretation、colon outer statement ownership、
nested delimiter frame、no synthetic Separator node、all recovery exitのframe balanceを確認対象にする。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定、ユーザ承認済み
（2026-08-22、layout-aware comma-or-newline delimited sequence authority追補案）。

## 追補案: call / field / path / ML applicationのfixed OperatorChain tail

Status: Claude review / exact wordingのfinal sign-off待ち。

### Scopeと既存architectureへの関係

本追補は、precedence-neutral `OperatorChain`追補で名前とflat source-order placementだけを予約した次の四形式を
具体化する。

```text
CallTail       # f(x, y)
FieldTail      # value.field
PathTail       # Module::name
MlArgument     # f x y の各 x / y
```

`IndexTail`（`a[i]`）と`ProjectionTail`（`a.(...)` / `a.{...}`）はYulang2にも実在する別grammarであるが、
本追補のscope外である。既存architectureにあるnamed-but-unspecified variantを維持し、CST body、AST field、adjacency、
recoveryを本追補から推論してはならない。future index / projection addendumがそれぞれのauthorityになる。

本追補は次をsupersedeしない。

- flat `OperatorChain`、BP-neutral surface invariant、target-free structural continuation。
- dynamic operator role judgeとHIR-side single association authority。
- `ColonApplicationTail`のterminality、inline / indented RHS、outer sequence ownership。
- 既存五constructの`LayoutDelimitedSequence` rule。

ただし`CallTail`のargument groupはYulang2でもlayout-aware delimited listだったため、本追補から
`LayoutDelimitedSequence` primitiveの新しいconsumerになる。これは先行追補が実装対象とした「五construct」を六constructへ
読み替えるretroactive supersessionではない。call固有のexplicit semicolonを含むseparator policyは本追補だけが所有する。

### Yulang2 oracle evidence

historical behaviorのauthorityを次で固定する。

- fieldは`scan_dot_field`が`.`と直後のidentifierを一個の`DotField` lexへscanし、LED `Field`がtarget-free tailをemitして
  shared tail loopへ戻った
  （`yulang2-oracle@a58eefc3:crates/parser/src/scan/mod.rs:123-128`,
  `crates/parser/src/expr/tail.rs:54-59`, `crates/parser/tests/expr_grammar.rs:870-880`）。
- pathはLED `PathSep`が`::`を保持し、ordinary / sigil identifierをmandatory RHSとしてscanしてshared tail loopへ戻った。
  missing RHSはempty `InvalidToken`、non-name RHSはnon-empty invalidだった
  （`crates/parser/src/expr/tail.rs:84-101,299-302,351-366`,
  `crates/parser/tests/expr_grammar.rs:883-917`, `crates/parser/tests/recovery.rs:20-36`）。
- callはleading triviaが`TriviaInfo::None`の`(`だけを`CallStart`にし、`ExprListMachine`へdelegateした。call listは
  comma / semicolonをliteral separator、following indent `<= call_base`のnewlineをimplicit separatorとして扱った
  （`crates/parser/src/expr/scan.rs:239-255`, `crates/parser/src/expr/tail.rs:103-108`,
  `crates/parser/src/expr/group.rs:30-117`, `crates/parser/src/parse/mod.rs:21-77`）。
- ML applicationは一回のLED `MlNud`につき一個の`ApplyML`を作り、nested parseだけ`ml_arg = true`にした。
  `ml_arg`中は次tail前のtriviaがnon-emptyならargumentを終了し、outer shared loopが次argumentをclaimした。
  equal-or-shallower newlineはtail loop全体を止め、deeper newlineはcandidateを許した
  （`crates/parser/src/expr/tail.rs:21-45,273-294`, `crates/parser/src/expr/scan.rs:217-283`,
  `crates/parser/tests/expr_grammar.rs:824-843`, `crates/parser/tests/stmt_grammar.rs:2971-3048`）。
- fixed tailはnumeric `min_bp`比較を通らず、call / field / pathの後も同じtail loopへ戻った。したがってこれらは互いにも
  dynamic operatorにもsource順にinterleaveした
  （`crates/parser/src/expr/tail.rs:47-113,226-294`）。

### Authoritative surface grammar

`G*`はemptyでもよい一回のmaximal `TriviaRun`、`G+`はnon-empty maximal `TriviaRun`である。
`ChainContinuingTrivia`と`MlArgumentSeparator`のnewline条件は後節でexhaustiveに定義する。

```text
FixedExpressionContinuation :=
    CallTail
  | ChainContinuingTrivia FieldTail
  | ChainContinuingTrivia PathTail

ChainContinuingTrivia :=
    maximal G* containing no physical newline
  | maximal G* whose following_line_indent > active_base

CallTail :=
    LParen OpeningTrivia
    [
        OperatorChain
        { CallArgumentBoundary OperatorChain }
        [ CallArgumentBoundary ]
    ]
    RParen

CallArgumentBoundary :=
    ExplicitCallArgumentBoundary
  | ImplicitNewlineBoundary(call_base)

ExplicitCallArgumentBoundary := Comma | Semicolon

FieldTail := Dot Identifier

PathTail := ColonColon G* PathSegment
PathSegment := Identifier | SigilIdentifier

MlApplicationContinuation := MlArgumentSeparator MlArgument
MlArgumentSeparator := G+ satisfying the ML boundary table
MlArgument := OperatorChain under the ml_arg stop scope
```

`CallTail`の`LParen`はcompleted operandにbyte-adjacentでなければならない。`FieldTail`の`Dot Identifier`も
内部triviaを許さない。対してfield / path introducerの前には`ChainContinuingTrivia`を許し、`PathTail`の`::`後には
maximal `G*`を許す。leading / inter-tail triviaはouter `OperatorChain`直下、path segment前のtriviaは`PathTail`直下、
call opener後とargument間のtriviaは`CallTail`直下にsource orderで一度だけ置く。

### CST vocabularyとshape

追加するnode kindは次の四個だけである。既存の`Dot`、`ColonColon`、`LParen`、`RParen`、`Comma`、`Semicolon`、
`Identifier`、`SigilIdentifier`、trivia、`Missing`、`Error` token / node vocabularyを再利用する。

```text
SyntaxKind::CallTail
SyntaxKind::FieldTail
SyntaxKind::PathTail
SyntaxKind::MlArgument
```

valid CST shapeを次で固定する。

```text
# f(x, y)
OperatorChain
  IdentifierExpression "f"
  CallTail
    LParen "("
    OperatorChain
      IdentifierExpression "x"
    Comma ","
    Whitespace " "
    OperatorChain
      IdentifierExpression "y"
    RParen ")"

# value.field::method
OperatorChain
  IdentifierExpression "value"
  FieldTail
    Dot "."
    Identifier "field"
  PathTail
    ColonColon "::"
    Identifier "method"

# f x y
OperatorChain
  IdentifierExpression "f"
  Whitespace " "
  MlArgument
    OperatorChain
      IdentifierExpression "x"
  Whitespace " "
  MlArgument
    OperatorChain
      IdentifierExpression "y"
```

tail nodeはtargetをchildにしない。call argumentだけが`CallTail`のnested `OperatorChain`、ML argumentだけが
`MlArgument`のnested `OperatorChain`になる。field / pathのname slotはleaf tokenであり、name用wrapper nodeを追加しない。
literal call separatorは`CallTail`直下のraw `Comma` / `Semicolon` tokenとし、`Separator` wrapperを作らない。
implicit call boundaryもraw triviaだけで表し、empty `Separator`、`Missing(Comma)`、sourceにないtokenを合成しない。

Yulang2のcomposite `DotField(".field")`は移植せず、Yulang3ではadjacentな`Dot(".")` + `Identifier("field")`へ分ける。
これはsource acceptanceを変えないtokenization divergenceであり、mandatory name slotとzero-width recovery positionを
typedに表すための意図的な差である。Yulang2 `ApplyC` / `Field` / `PathSep` / `ApplyML` node名も、既存architectureで
予約済みのtarget-free `CallTail` / `FieldTail` / `PathTail` / `MlArgument`へ置き換える。

`IndexTail` / `ProjectionTail`は上のnode追加listとshape例に意図的に含めない。本追補はその既存予約を削除もしない。

### Parser-side surface AST

precedence-neutral parser-side valueを次へ具体化する。separator trivia / tokenはlossless CSTがauthorityであり、ASTへ複製しない。

```rust
pub(crate) enum OperatorChainItem<'source> {
    // existing dynamic / primary / terminal variants,
    FixedPostfix(FixedPostfixTail<'source>),
    MlArgument {
        argument: Box<OperatorChain<'source>>,
        range: Range<usize>,
    },
    // existing recovery variants,
}

pub(crate) enum FixedPostfixTail<'source> {
    Call(CallTail<'source>),
    Field(FieldTail<'source>),
    Path(PathTail<'source>),
    // Index / Projection remain reserved and unspecified by this addendum.
}

pub(crate) struct CallTail<'source> {
    open: Range<usize>,
    arguments: Vec<OperatorChain<'source>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

pub(crate) struct FieldTail<'source> {
    dot: Range<usize>,
    name: Recovered<WordSpan<'source>>,
    range: Range<usize>,
}

pub(crate) struct PathTail<'source> {
    separator: Range<usize>,
    segment: Recovered<PathSegment<'source>>,
    range: Range<usize>,
}

pub(crate) enum PathSegment<'source> {
    Identifier(WordSpan<'source>),
    SigilIdentifier(WordSpan<'source>),
}
```

missing call argumentは`OperatorChainItem::MissingOperand`を含むtotal nested chainとして`arguments`へ置く。
explicit trailing comma / semicolonはcall semantic arityを変えないためAST markerを追加しない。missing close / name / segmentの
`Recovered`とrangeはCST recovery siteを指し、target application edgeやnumeric BPを持たない。

### Continuation recognitionとcall / ML adjacency

operand-complete siteのjudge順とownershipを次で固定する。fixed punctuationとdynamic spellingが同じsource positionから
始まり得るcaseは、既存のcanonical longest-spelling / call-path-sensitive continuation judgeを一回だけ使い、
本追補専用のsecond scannerを作らない。

1. active owner stop、equal-or-shallower newline、matching delimiterを先に判定し、owner boundaryをconsumeしない。
2. canonical judgeがaccepted dynamic suffix / infixを返せば、そのroleを保持する。fixed tail recoveryがaccepted operator spellingを
   shorter punctuationへsplitしてはならない。
3. structural candidateがauthorityを得た場合、no-leading-trivia `(`は`CallTail`、exact `.identifier`は`FieldTail`、
   exact `::`は`PathTail`としてacceptしてcutする。reserved projection lookaheadのbody grammarは本追補では開かない。
4. non-empty triviaとshared NUD candidateがML boundary tableを満たす場合だけ`MlArgument`をacceptする。同じpositionの
   longer NUD token（将来の`:symbol`等）が成立する場合、shorter terminal punctuationへsplitしない。
5. terminal `ColonApplicationTail`をacceptしたらchainを終了する。

concrete call / ML disambiguationは次だけで決まり、semantic typeやnumeric BPを読まない。

| source | classification |
| --- | --- |
| `f(x)` | triviaなしの`(`なのでone `CallTail` |
| `f (x)` | non-empty same-line triviaなのでone `MlArgument(ParenthesizedExpression)` |
| `f/*c*/(x)` | commentもnon-empty triviaなのでone `MlArgument` |
| root base 0の`f\n  (x)` | following indent 2 > 0なのでone multiline `MlArgument` |
| root base 0の`f\n(x)` | following indent 0 <= 0なのでchain stop。newline / `(x)`はouter ownerへ返す |

`(`にleading triviaがない場合、ML argumentを表すempty separatorは存在しないためcallが常にauthorityを持つ。
leading triviaがある場合、call recognitionは失敗し、qualifying ML separator + shared parenthesized NUDとしてだけacceptできる。
call/path-sensitive prefix-or-nullfix word ruleも維持する。たとえば`last()` / `last::sub`では直後の`(`/`::`を
dynamic operator spellingのargumentとせず、identifier head + structural tailを優先する。

field normal recognitionはexact adjacent `.field`だけである。`.(` / `.{`はfuture `ProjectionTail` authorityへ残し、
`..`、`...`、operator tableがacceptするlonger spellingを`.` + missing fieldへsplitしない。pathは`::`を`:`二個へsplitせず、
`ColonApplicationTail`より先にlongest fixed punctuationとして判定する。

### ML whitespace / newline boundary table

ML applicationはdelimiter pairを持たないためown `LayoutDelimitedFrame`をpushしない。prospective separatorの
maximal `TriviaRun`と、current lexical depthのactive `IndentationBaseline.column`を使う。

```text
MlArgumentSeparator(trivia, active_base) :=
    trivia is non-empty
    and (
        trivia contains no physical newline
        or following_line_indent > active_base
    )
    and shared OperatorChain NUD candidate follows
```

tableはexhaustiveである。

| trivia before prospective argument | following candidate | result / owner |
| --- | --- | --- |
| empty | any NUD | ML separatorではない。no-space call / fixed tail / dynamic judgeへ残す |
| non-empty、physical newlineなし | shared NUD | one `MlArgument` |
| newlineあり、following indent `> active_base` | shared NUD | one `MlArgument` |
| newlineあり、following indent `<= active_base` | shared NUD | current tail loopをstopし、triviaとcandidateをouter sequence / statement ownerへ返す |
| qualifying trivia | shared NUDなし | ML tailをcommitしない。triviaをouter chain / callerへ残す |
| opaque lexical region内部だけのnewline | — | trivia classifierへ出ないためML layout判定に参加しない |

shared NUD candidateはcurrent `OperatorChain`が実際にacceptできるprimary、prefix、nullfixであり、identifier / integer /
parenthesized / braced / `if` / `case` / `catch`等の実装済みprimaryと、将来同じprimary authorityへ追加されるstring / rule等を含む。
candidate listをML専用に複製しない。LED siteでdynamic judgeがinfix / suffixを選んだoperatorはML NUDへ再解釈しない。
これによりYulang2 fixture同様、`1\n    +2`はdynamic infixになり得る一方、judgeがprefix NUDを選ぶ
`1\n    -2`はML argumentになり得る。

one `MlArgument`をacceptした後、nested `OperatorChain`だけ`ml_arg = true`にする。このscopeではtail前triviaが
non-emptyになった時点でnested chainを終了する。adjacent `x.field(y)::z`は同じnested argumentに残るが、
`f x y`の`y`前spaceはnested argumentへ入らず、outer chainが二個目の`MlArgument`としてclaimする。
separator triviaはouter `OperatorChain`直下であり`MlArgument` rangeに含めない。scope exit / recovery / rollbackの全pathで
original `ml_arg`をexact restoreする。

#### `LayoutDelimitedFrame`との合成

ML boundaryと`LayoutDelimitedSequence`はorthogonalだが独立したindent値を競合させない。delimiter ownerは従来どおり
`LayoutDelimitedFrame`をpushし、そのbaseをcurrent lexical depthのactive indentation baselineにする。nested
`OperatorChain`のML probeはそのtop baselineを読むだけで、layout frameを再計算・上書きしない。

- newline indent `<= container base`: current expression chainとML probeがstopし、containerがimplicit separatorとしてclaimする。
- newline indent `> container base`: container separatorではなくcurrent expression continuationであり、shared NUDがあればML argumentになる。
- delimiterを抜ければtop baselineをexact restoreし、outer statement / arm / containerの判定へ戻る。

root / non-delimited expressionではnearest block / introducer baseline、なければ0を使う。したがってML applicationは
own delimiter frameを持たないが、enclosing call / parenthesized / list / record / statement layoutとtyped baseline stack経由で
一意にcomposeする。raw `line_indent`だけを見たり、`LayoutDelimitedFrame::inline`をML argumentごとにpushしたりしない。

### Call argument layout

`CallTail`はopen accept / cut直後にopening triviaを一回consumeし、先行`LayoutDelimitedSequence`と同じ式で
`call_base`をcaptureする。

```text
incoming_base := current lexical-depth indentation baseline, or 0
call_base :=
    if OpeningTrivia contains a physical newline
       and following_line_indent > incoming_base
    then following_line_indent
    else incoming_base
```

baseをfirst argumentから導出しない。comma / semicolonとqualifying newlineが同じinter-argument gapにある場合は
literal punctuationをauthorityとするone boundary clusterであり、newline triviaを二度数えない。qualifying trailing newline、
trailing comma、trailing semicolonはいずれもvalidで、empty argumentを作らない。semicolonはCallTailだけのhistorical explicit
separatorであり、先行五constructでは引き続きinvalidである。

### Recovery contract

全四形式でaccepted introducer後はcutし、malformed tailをdynamic operatorやnew primaryへreinterpretしない。
pure absenceはzero-width `Missing`、source byteを所有するmalformationは次のvalid retry / owner safe pointまでのmaximal
non-empty `Error`、one committed recovery node = one recovery diagnosticとする。active stop、matching outer delimiter、
equal-or-shallower newline、EOFをconsumeしない。AST / direct-CSTは同じcandidate probeとrecovery siteを共有する。

session vocabularyは既存`ConstructRole::ArgumentList`、`ExpectedSyntax::{Identifier, Expression,
DelimitedSequenceSeparator}`、closing-delimiter roleを再利用し、expression-local siteとして概念上次を追加する。

```text
ExpressionRole::CallArgument
ExpressionRole::CallArgumentSeparator
ExpressionRole::FieldName
ExpressionRole::PathSegment
ExpressionRole::MlArgument
```

`StopKind::{Comma, Semicolon, RightParenthesis}`、existing `ml_arg` flag、delimiter / indentation stackで足りるため、
newline専用またはtail専用のuntyped stop booleanを追加しない。

#### `CallTail` recovery table

| situation | CST / recovery |
| --- | --- |
| `f()` | valid zero-argument call。recoveryなし |
| `f(a,)` / `f(a;)` / qualifying trailing newline before `)` | valid trailing boundary。empty argument / Missingなし |
| `f(,a)` | first comma前にzero-width `OperatorChain > Missing(CallArgument)`一件。commaを保持して`a`をretry |
| `f(a,,b)` | second comma前にzero-width missing argument一件。second commaをboundaryとして保持して`b`をretry |
| same-line next argument candidate without boundary | zero-width `Missing(CallArgumentSeparator)`、same-position retry。ただし`f(a b)`の`a b`がvalid ML applicationならone argumentであり、このrecoveryを発行しない |
| malformed argument bytes then valid NUD | next NUD直前までone maximal non-empty `OperatorChain > Error`、same argument slotをretry |
| `f(a` + EOF / caller-owned boundary | argumentを保持し、boundaryをconsumeせずzero-width missing `RParen`一件 |
| stray mismatched close | caller-owned outer closeならconsumeせずmissing `RParen`。otherwise close tokenをone non-empty `Error`にしてsame close slotを続行 |
| explicit comma / semicolon + qualifying newline | one literal-authoritative boundary。newlineはfollowing trivia、duplicate item / diagnosticなし |
| deeper newline in an argument | call separatorへ昇格しない。current `OperatorChain` continuation / recoveryが所有 |

call scopeは`Comma`、`Semicolon`、matching `RightParenthesis`をcurrent-depth owner stopにする。これによりcall argument内の
`ColonApplicationTail`はouter sequence ownership ruleに従ってexactly one inline RHS argumentだけを取り、call separatorを返す。

#### `FieldTail` recovery table

| situation | CST / recovery |
| --- | --- |
| `x.field` | valid `FieldTail(Dot, Identifier)` |
| `x.` + EOF / owner safe point | `Dot`を保持した`FieldTail`内にzero-width `Missing(FieldName)`一件 |
| `x. field` | dynamic operator authorityがないexact standalone dotならdot直後へzero-width missing name。following trivia / `field`はconsumeせずouter continuationへ返す |
| `x.` followed by non-name invalid bytes | dotを保持し、次fixed continuation / dynamic LED / owner boundaryまでをone maximal non-empty `Error(FieldName)`にする |
| `x..`, `x...`, `x.(`, `x.{` | longer operator / reserved projection candidateをfield + Missingへsplitしない。respective authorityへ返す |

bare-dot recovery probeはprojection lookaheadとcanonical longest operator probeが不成立のときだけcommitできる。
Yulang2はmalformed dotをgeneric invalidへ落としたが、Yulang3はaccepted standalone field introducerが一意な場合だけmandatory
name slotを保持する。これは本節末尾のexplicit divergenceである。

#### `PathTail` recovery table

| situation | CST / recovery |
| --- | --- |
| `x::name` / `x:: $name` | valid path segment。`::`後triviaはtail内に保持 |
| `x::` + EOF / owner safe point | `ColonColon`を保持した`PathTail`内にzero-width `Missing(PathSegment)`一件 |
| `x::::name` | first tailのsegment位置へzero-width Missing一件、second `::`をconsumeせずouter tail loopからsame-position retry |
| `x::123` | `ColonColon`を保持し、non-name RHSをone maximal non-empty `Error(PathSegment)`にする |
| invalid run followed by fixed continuation / owner boundary | boundary直前までone non-empty Error、boundaryをouter tail / callerへ返す |

path recoveryは`::`をcolon application二個へsplitせず、missing / Error segmentをordinary expression primaryとして
捏造しない。valid segment後はshared tail loopへ戻る。

#### `MlArgument` recovery table

| situation | CST / recovery |
| --- | --- |
| `f x`、`f\n  x` at base 0 | valid separator + one `MlArgument`。recoveryなし |
| `f ` + EOF / owner boundary | shared NUD candidateがないためML tailをacceptしない。triviaだけを保持しMissing argumentを作らない |
| equal-or-shallower newline before candidate | ML tailをacceptせずnewline / candidateをouter ownerへ返す。recoveryなし |
| separator後にaccepted prefix/nullfix introducerがありoperand欠落 | `MlArgument > OperatorChain`内でoperator-useを保持し、nested mandatory operandのzero-width Missing一件 |
| separator後のparenthesized / braced primaryがmalformed | accepted primaryのdelimiter / item recoveryをnested chain内で一回だけ行い、ML-specific duplicate Missingを作らない |
| separator後がshared NUDでないinvalid run | ML tailをcommitしない。current outer expression / statement ownerのgeneric maximal Errorへ渡す |

normal ML recognitionはseparatorとshared NUD candidateを一個のsink-free probeで確認してからtrivia / nodeをcommitする。
したがってtrailing whitespaceだけから空`MlArgument`を作らない。accepted NUD後のfailureはtotal nested `OperatorChain` recoveryが
所有し、ML layerが同じcauseへ第二diagnosticを重ねない。

### Chaining、dynamic operator、ColonApplicationTail

四形式はCSTで常にsource-order siblingになる。representative mixed formを次で固定する。

```text
a.b(c)::d e

OperatorChain
  IdentifierExpression "a"
  FieldTail ".b"
  CallTail "(c)"
  PathTail "::d"
  Whitespace " "
  MlArgument
    OperatorChain "e"
```

parserはどのfixed tail / ML argumentでもnumeric BPを比較せず、accept後はoperand-complete tail loopへ戻る。
HIR associatorは既存contractどおりcall / field / pathをreserved structural postfix、nested `MlArgument`を先にassociateした
fixed left applicationとしてcurrent association cursorへsource orderで適用する。したがって`f x y`は`(f x) y`、
`a + b(c)`は`b(c)`がright operand内のfixed continuation、`a!()`と`a()!`はそれぞれsource orderのsuffix / call列になる。
このsemantic nestingをCST / parser-side ASTへ書き戻さない。

field / path / call / MLは`ColonApplicationTail`より前に何個でも現れてよい。outer `ml_arg` scopeに戻った後のcolonは
outer chainのterminal tailになるため、`f x: rhs`は`Primary(f), MlArgument(x), ColonApplicationTail(rhs)`である。
一方、nested `MlArgument`のparse中はexisting `ml_arg` reservationによりcolonをacceptせずouter loopへ返す。

`ColonApplicationTail`をacceptした後、同じ`OperatorChain`へcall / field / path / ML / dynamic operatorを追加してはならない。
colon RHS内部はown nested chainsとして四形式を普通に含められる。colon application resultへさらにtailを付けるsourceは
`(f: rhs).field`のようにparenthesizeし、outer chainで新しいtailを開始する。terminal tail後のpunctuation / triviaを
same-chain continuationとしてrecoverしない。

### Explicit Yulang2 divergences

本追補の意図的なCST / recovery shape差は次の四点であり、それ以外のacceptance / chainingを「consistency」の名で変更しない。

1. Yulang2 `DotField` composite tokenをYulang3 `Dot` + `Identifier`へ分割する。adjacencyは維持する。
2. Yulang2のimplicit call separator用empty `Separator` nodeとexplicit separator wrapperを移植せず、raw trivia / punctuationと
   sibling argument hierarchyで表す。これは先行`LayoutDelimitedSequence`のsyntax-as-written CST ruleをcallへ適用する差である。
3. Yulang2のmalformed field dotはgeneric invalidだったが、Yulang3ではlonger operator / projection authorityがなくstandalone dotが
   field introducerとして一意なcaseに限り`FieldTail + Missing(FieldName)`へする。one committed recovery siteとmandatory-slot
   disciplineを優先し、ambiguous spellingはfieldへcommitしない。
4. Yulang2のempty / non-empty `InvalidToken` recoveryは、call / field / pathのtyped mandatory slotではzero-width `Missing` / maximal
   non-empty `Error`へ置き換える。これは本architecture全体のone recovery node = one diagnostic contractを適用するshape差であり、
   malformed bytesをvalid sourceへ再解釈する変更ではない。

さらに、既存architectureが予約した`MlArgumentSeparator`の**non-empty trivia**要件を維持する。Yulang2 scannerはtoken boundaryだけで
separate NUDを作れる一部punctuation / literal starterをtriviaなしの`MlNud`へ送れた
（`yulang2-oracle@a58eefc3:crates/parser/src/expr/scan.rs:239-255,277-283`）が、本追補はそれを一般化しない。
no-space `(`はCallTail、no-space fixed punctuationはそのfixed tail、その他のno-space token列はshared lexical / dynamic judgeの
authorityであり、ML applicationはwhitespace / layout continuationだけである。このacceptance divergenceはreviewで明示確認する。

### Implementation gates

1. AST / direct-CSTが同じfour-tail recognizerを使い、BP-only table changeでshape / recoveryが不変である。
2. `f(x)`と`f (x)`、same-line / deeper / equal-or-shallower newlineのcall-vs-ML tableを全てfixture化する。
3. `f x y`がtwo sibling `MlArgument`、各argumentがone nested flat `OperatorChain`になる。
4. field / path / call / MLとprefix / infix / suffixのmixed source-order CST、HIR association fixtureを分離して固定する。
5. callのempty、comma / semicolon / implicit-newline、trailing boundary、mixed literal+newline、deeper continuationを固定する。
6. call argument frameとouter parenthesized / list / record / statement frameがnested lexical depthでexact restoreされる。
7. field `Dot + Identifier`、path `ColonColon + (Identifier | SigilIdentifier)`のnormal / missing / malformed caseを固定する。
8. `.(` / `.{` / longer dot operatorをFieldTail recoveryへsplitせず、`::`をColonApplicationTailへsplitしない。
9. ML argument内のadjacent fixed tail、non-empty-trivia stop、prefix/nullfix mandatory operand recoveryを固定する。
10. all recoveryでMissing zero-width、Error non-empty、node / diagnostic一対一、owner boundary unconsumed、node / scope balance、
    `green.to_string() == source`を満たす。
11. fixed / ML tailの後にcolonを許し、colon後のsame-chain continuationを0件にする。nested RHS tailは別chainに残す。
12. `IndexTail` / `ProjectionTail`のSyntaxKind、AST body、scanner、recoveryをこのimplementation sliceへ混ぜない。

### Closed decisions and review focus

本追補で四形式のimplementationをblockするopen questionはない。次を確定する。

- call / field / pathはtarget-free `FixedPostfixTail`、MLはone-argument-per-nodeの`MlArgument`である。
- `f(x)`はcall、`f (x)`はML parenthesized argumentである。
- ML separatorはnon-empty same-line triviaまたはactive baseよりdeeperなnewlineであり、equal / shallower newlineはouter ownerへ返す。
- MLはown `LayoutDelimitedFrame`を持たず、enclosing typed baseline stackを読む。
- callはcomma / semicolon / implicit newline listで、approved layout base formulaとraw-trivia boundary shapeを使う。
- field nameはdot-adjacent ordinary identifier、path segmentはtriviaを挟めるordinary / sigil identifierである。
- fixed / ML tailはdynamic numeric BPを読まずsource orderでchainし、colonはそれらの後にだけ置けるterminal tailである。
- Index / Projectionはnamed-but-unspecifiedのfuture scopeである。

Claude reviewでは、特にcallのhistorical semicolon、call base capture、`f(x)` / `f (x)`、Yulang2のtrivia-free
`MlNud`からの明示的 divergence、ml_arg中のnon-empty-trivia stop、delimited frameとのbaseline composition、DotField token split、
bare-dot recoveryのlongest-spelling guard、colon terminality、Index / Projection scope exclusionを確認対象にする。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定
（2026-08-22、call / field / path / ML application fixed-tail追補案）。
