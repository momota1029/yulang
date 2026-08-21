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
- scanner が確定した source byte range、contextual tag、fixity、binding power、delimiter / layout 情報を返す。
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

buildに成功したtableは`FullParseSession` / `ParseEnv`が所有または`Arc`で固定し、scannerとPratt parserは
同じreferenceだけを見る。full parse中のinsert、overlay、lazy rebuild、HeaderInfo / CST再走査は置かない。
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
5. NUD / LED probeとdirect Pratt continuation。`start_node_at`によるprefix / infix / suffix / nullfix CST。
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

この convention は declaration continuation に限定する。既決の expression operator scanner が返す
`ScannedOperator.trailing_trivia` は trailing result のままであり、Pratt CST の所有規則を変更しない。
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
NUD / LED scanner と Pratt parser が読む hot `OperatorEntry` は現在の shape のままにし、build error と
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

build 成功後、full parse session が完成 table を所有するか `Arc` で固定し、`ParseEnv::full`、operator
scanner、Pratt parser はその一 reference だけを見る。header declaration continuation は full parse 中に
table insert を行わない。

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
  operator definitionは既決の`OperatorHeader` nodeと、その後ろのdirect Pratt expression bodyを一つの
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
含む。`my value = +!a`と`my value = a+!b`はsub-slice 5と同じcandidate fallback / BP semanticsでparseする。
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
header fact parityのIDへ混ぜない。今回のvertical sliceが構造化するbody grammarはsub-slice 5のdirect Pratt
domainまでである。将来block、pattern、type、Yumark statement familyを追加する際は`StatementIntro`と
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
  Pratt authorityがあり、scopeを縮めるとAST/full CSTで別grammarになる。
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

この追補のgrouped-expression AST / CST shape、binding-power integration、trivia ownership、
mandatory recovery、fixtureの2-recovery acceptance targetについて、既存code / design / fixtureから
解けずに残るquestionは **ない**。

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
