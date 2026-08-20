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

調査対象は `chasa 0.5.0` と、annotated tag `yulang2-oracle` が指す commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`（以下 `yulang2-oracle@a58eefc3`）である。
`chasa` の source は local Cargo registry cache に展開済みだったため、network access は
使っていない。

## Decision summary

`crates/yu-syntax` の full parser は、source 全体を先に
`Vec<LexedToken>` へ materialize する構成を廃止し、`chasa` の `Input<Item = char>` を
grammar が直接消費する構成へ置き換える。

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

## Implementation gates

architecture-level gate と question 7 / 8 の diagnostic detail は上の resolved decision で閉じた。
最初の vertical slice の完了条件は次とする。

- `chasa` が crates.io の normal dependency として `=0.5.0` に exact pin され、source の vendor / copy
  や workspace member / path dependency を使わない。
- `chasa` input から shared declaration grammar と最小 Pratt expression grammar が直接 source を読む。
- 通常の alternation は `choice` / `or` を使い、明示的 rollback は構造的に必要な operator-candidate
  区間へ限定される。
- `lex() -> Vec<LexedToken>` と `scan_symbol_end` を production path から除去する。
- `HeaderInfo` と immutable `OperatorTable` が `BpVec` 相当の prefix / infix / suffix / nullfix を
  最初から持ち、full parse 中に table mutation がない。
- canonical full-fixity fixture の `+!a` / `a+!b` が oracle judge table のまま user-confirmed tree
  shape を持つ。
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
  `crates/yu-syntax/src/{lib,parse,input,session,sink,syntax_kind}.rs`、
  `notes/design/2026-08-20-phase2-parser-fixture-schema.md`、phase 2 parser fixtures、
  commit `e1737368` と `7022ed27`。
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
- この revision は本 design document だけを変更し、source、manifest、fixture、正本 architecture
  document は変更していない。

著者: Codex gpt-5.6-sol xhigh（2026-08-20）
