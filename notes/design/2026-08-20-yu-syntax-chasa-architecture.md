# `yu-syntax` chasa-based parsing architecture

Status: Proposal。実装、dependency 追加、grammar の拡張はこの文書の scope 外とする。

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
grammar position（NUD または LED）と live `OperatorTable` を渡された operator scanner が、
character stream 上で spelling、fixity、boundary、後続条件を同時に判定する。

header discovery の現在の二 pattern は context-dependent operator tokenization を必要とせず、
この問題だけについては壊れていない。それでも §4.2.2 の shared grammar authority と
header/full parity を満たすため、`scan_header` も同じ chasa-based scanner と declaration
grammar を restricted mode で呼ぶ構成へ移す。

chasa から Rowan を直接呼ぶのではなく、grammar は source range を持つ rollback 可能な
parse event を生成する。parse が終わった後、専用 Rowan sink が event と元 source を
`GreenNodeBuilder` へ replay し、`ParsedFile.green: GreenNode` を構築する。これにより、
operator probe や recovery branch の rollback が CST event にも適用される。

## Problem statement

dynamic operator table に次を登録する。

- infix operator `+!`
- prefix operator `+`
- prefix operator `!`

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

- chasa を使う input、scanner、grammar、event、Rowan sink の責務境界。
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
`env` ではない。この差は CST builder、scope、diagnostic、header fact を置く場所の design に
直結する。rollback されるべき mutation を `env` に置いてはならない。

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

### Confirmed discrepancy in the tagged oracle

この exact example は `yulang2-oracle@a58eefc3` の現状では両方とも成功するわけではない。
tag を `/tmp` へ展開し、infix `+!` と prefix-only `+` / `!` を `OpTable` に登録した test を
追加して実行した結果は次だった。

| source | tagged oracle result |
| --- | --- |
| `a+!b` | `Infix "+!"` として成功 |
| `+!a` | 先頭 `+` が `Unknown` / `InvalidToken` へ落ちる |

原因は `expr/scan/op/scan.rs:153-167` の `op_value_start_inner` にある。line 160 の

```rust
kinds.contains(OpKindSet::PREFIX | OpKindSet::NULLFIX)
```

は、この `OpKindSet::contains` の定義上「PREFIX または NULLFIX」ではなく「PREFIX と
NULLFIX の両方」を要求する。したがって prefix-only の `!` は、短い `+` candidate の RHS
value start と認識されない。

一時 copy だけで条件を

```rust
kinds.contains(OpKindSet::PREFIX) || kinds.contains(OpKindSet::NULLFIX)
```

へ変えると、同じ test で `+!a` は二重 `PrefixNode`、`a+!b` は一つの `InfixNode` として
両方成功した。これは repository への修正ではなく、chasa の rollback mechanism と oracle
側 continuation predicate の責務を切り分けるための実験である。

結論は次の二点に分かれる。

- chasa の character input + `longest_match_then` + uncut rollback は、この曖昧性を解く
  mechanism を実際に提供している。
- tagged oracle はその mechanism を使う構造だが、exact prefix-only chain には一行の
  predicate bug があり、現状をそのまま correctness oracle としてコピーしてはならない。

Yulang3 の implementation fixture には、この二 source を最初から同じ operator table で入れ、
この bug を port しない。

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

ただし oracle の `State.sink` は chasa の `env` 内にあり、`In::checkpoint` の rollback 対象では
ない。oracle は scanner choice を CST emission 前に終わらせ、grammar-level subtree
backtracking を避ける predictive parser なので、この制約を運用で守っている。Yulang3 の
shared recovery と diagnostic transaction まで含めるなら、`GreenNodeBuilder` へ speculative
branch から直接書く構成は脆い。

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

### Module and responsibility layout

public entrypoint と主役の product は見つけやすい位置に残し、implementation を次の責務へ分ける。

```text
src/
  lib.rs                 public products and re-exports
  header.rs              scan_header orchestration
  parse.rs               parse_file orchestration
  input.rs               byte-positioned chasa source input
  session.rs             ParseEnv, rollback-aware ParseLocal, scoped context
  operator.rs            OperatorTable and chasa TrieState adapter
  event.rs               markers, tokens, recovery events, checkpoints
  sink.rs                validated event stream -> Rowan GreenNode
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
- token event は copied `Box<str>` より source `Range<usize>` を保持する。

### Parse environment and rollback-aware local state

chasa の `env` と `local` を意図的に分ける。

`ParseEnv` は speculative branch で mutation しない data を持つ。

- original source
- `ParseMode::{Header, Full}`
- selected `SyntaxEnvironment`
- full parse が照合する `HeaderInfo`
- immutable lexical/statement-start authority

`ParseLocal` は rollback される mutable state を持ち、cheap checkpoint を実装する。

- event log と open marker state
- scoped indentation / stop set / delimiter context
- staged header fact transaction
- staged recovery event sequence と full-origin diagnostic staging
- parse 中に追加される local operator definitions、またはその rollback-aware overlay

`ParseLocal::Checkpoint` は大きな structure の clone ではなく、各 append-only log の length、
scope stack depth、operator overlay checkpoint を保存する。rollback は truncate / restore で行う。
これにより §4.2.1 が禁止する grammar function ごとの手書き save/restore を、session の
scoped API と chasa checkpoint に集約する。

chasa の `ErrorSink` には speculative expectation を置く。recovery が path を確定した時だけ、
期待情報を `ParseLocal` の recovery event へ変換する。branch failure の expectation を
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

実際の generic signature は chasa / reborrow 制約に合わせる。重要なのは `site` と live table が
token boundary 決定前に渡ることである。

`scan_operator` は `OperatorTable::state().longest_match_then(...)` を使い、candidate callback で
boundary、fixity、whitespace、value-start lookahead を検査する。NUD callback は prefix /
nullfix だけ、LED callback は infix / suffix と grammar が許す argument form だけを認める。
value-start operator 判定は `PREFIX || NULLFIX` であり、両方を要求しない。

candidate が確定するまで event を emit せず、cut もしない。確定後に token range と trailing
trivia を `ScannedOperator` として返す。caller の predictive branch が operator use を採用した後、
必要ならその branch の introducer に cut を置く。

### Expression parser

Yulang2 の algorithm は維持する。

1. `parse_expr_bp` が NUD scanner を呼ぶ。
2. NUD tag に応じて atom / group / prefix subtree を作る。
3. prefix RHS は prefix binding power を `min_bp` として recursive parse する。
4. operand 完了後、tail loop が LED scanner を呼ぶ。
5. infix / suffix binding power と `min_bp` を比較し、Pratt continuation を進めるか caller へ返す。

この「NUD scanner を呼んでいるか、LED scanner を呼んでいるか」が operator tokenization の
parser state そのものである。別 lexer state machine を追加しない。

grammar-level subtree backtracking は避け、chasa rollback は operator spelling、keyword /
punctuation overlap、lookahead のような局所 token-level decision に限定する。これにより source
全体を暗黙に二度 parse せず、operator run の長さに比例する局所 probe だけを行う。

### Header discovery and full parse

`scan_header` と `parse_file` は別 phase product のまま維持する。これは §4.2.2 が必要とする
syntax planning の boundary であり、独立 lexer + parser の二重化とは異なる。

両 entrypoint は同じ `grammar::declaration` と shared statement-start classification を使う。

Header mode:

1. source 先頭から trivia と header starter を読む。
2. shared `use` / operator-header grammar を restricted mode で呼ぶ。
3. mandatory field が一意に確定した declaration fact だけを transaction commit する。
4. operator body は expression parse せず、delimiter と indentation を使う shared opaque scanner で
   次の top-level boundary まで進める。
5. 最初の non-header starter は normal stop とし、error にしない。
6. `HeaderInfo` に coverage、facts、header-origin diagnostics を凍結する。partial GreenNode は返さない。

Full mode:

1. imported syntax environment から parse-session operator table を作る。
2. source 先頭の header declaration を同じ shared grammar で再度読む。
3. local operator header を順に live table へ反映する。
4. shared grammar が独立に得た full header projection を `HeaderInfo` と range / path / visibility /
   operator shape で照合する。不一致を silent overwrite しない。
5. body を integrated scanner + grammar で最後まで parse し、recovery event と diagnostics を集める。
6. header-origin diagnostic は同じ `DiagnosticId` を一度だけ final list に取り込む。

full parse は `HeaderInfo` の range を使って pre-tokenized source を node で包むのではない。
`HeaderInfo` は expected parity input と syntax planning product であり、full CST grammar の代替ではない。

### Parse events and Rowan sink

grammar は rollback 可能な event buffer に概念的に次を出す。

```rust
enum ParseEvent {
    StartNode(SyntaxKind),
    Token { kind: SyntaxKind, range: Range<usize> },
    FinishNode,
    // Marker/forward-parent metadata may be separate fields.
}
```

`Missing` は zero-width `Missing` node の start/finish event と対応 recovery record を生成する。
`Error` は `Error` node の中に一 byte 以上を覆う token event を入れる。trivia も独立 token kind と
range を持ち、source byte を捨てない。

Pratt parser がすでに出した left operand を後から node で包む必要があるため、event layer は
`Marker` / `CompletedMarker` と forward-parent、または同等の `start_node_at` ordering を提供する。
この bookkeeping は grammar function から Rowan API を隠す。

`ParseLocal` の checkpoint は event length と marker state を含む。uncut failure では tentative
token、node、recovery event、fact staging をまとめて rollback する。これは oracle の direct
`GreenSink` より一段明示的だが、§4.2.2 の recovery transaction に必要である。

parse 完了後、`RowanSink` は event stream を検証して `GreenNodeBuilder` へ replay する。

- marker が balanced。
- token range が source order で重ならない。
- full parse の token/trivia range が `0..source.len()` を gap なく一度ずつ覆う。
- token text は必ず `&source[range]` から取る。
- `Missing` は byte を持たず、`Error` は一 byte 以上を持つ。

検証後に `builder.start_node`、`builder.token(kind, source_slice)`、`builder.finish_node` を呼び、
`builder.finish()` を `ParsedFile.green` に格納する。`ParsedFile.green: GreenNode` と
`green.to_string() == source` は architecture contract のまま維持される。

event buffer の一回の replay は source の再 tokenization / 再 parsing ではない。grammar が確定した
構造を immutable Rowan storage へ materialize する sink phase である。event に source range を
置くことで、oracle の `Box<str>` per token より copy を減らせる。

### Recovery and diagnostic ownership

shared recovery layer は header/full の両 mode から呼ばれ、§4.2.2 の safe-point hierarchy と
consume-or-stop guarantee を所有する。operator scanner の「candidate がこの position で無効」は
通常の backtracking failure であり、直ちに diagnostic にしない。候補を尽くし、grammar が
recovery path を commit した地点だけが recovery episode になる。

header discovery で作った recovery event は deterministic `DiagnosticId` を持つ。full mode で
同じ shared header grammar が同じ site に到達したときは、`HeaderInfo` の event identity を照合・
再利用し、新しい diagnostic を発行しない。body recovery は full-origin の新しい ID を持つ。
final list は §4.2.2 の ordering key で一度だけ sort / freeze する。

## Fate of the committed code

### Reuse assessment

| current element | decision | reason / destination |
| --- | --- | --- |
| `HeaderInfo`, `HeaderImport`, `HeaderOperator` | keep/evolve | diagnostics/hash と full fixity を追加する |
| `ParsedFile` and `parse_file` API shape | keep | `green: GreenNode`、diagnostics ownership、syntax key は正本と一致する |
| `SyntaxEnvironment` boundary | keep and implement | imported/live operator table の入力になる |
| trivia/content distinction | keep as a concept | lossless CST と indentation grammar に必要。chasa scanner output へ移す |
| delimiter stack | keep as a concept | opaque body scan と recovery safe point に必要。rollback-aware local state へ移す |
| indentation / line-start tracking | keep as a concept | layout に必要。session の byte-positioned state へ移す |
| `newline_len`, indentation predicates | port selectively | shared scanner の char/byte helper へ移す |
| `GreenNodeBuilder` start/token/finish bridge | keep | dedicated `RowanSink` へ移す |
| `HeaderCursor` as token-producing cursor | replace | operator boundary を grammar 前に確定するため foundation にはできない |
| `HeaderCursor::next` / `scan_token` | replace | source char input と context-specific scanner に分解する |
| `scan_symbol_end` / `starts_distinct_item` | delete | context-free maximal munch が confirmed root problem |
| `TokenKind::Symbol` as preclassified run | delete | spelling/fixity/site を operator scanner が同時に決める |
| `lex() -> Vec<LexedToken>` | delete | architecture correction の中心 |
| `LexedToken`, `token_index` | delete | streaming char parse + event range に不要 |
| `FullCstBuilder` orchestration | replace | grammar session と final `RowanSink` に責務分割する |
| `HeaderNode` / header ranges で CST を包む処理 | delete | shared declaration grammar と parity projection へ置き換える |
| `syntax_kind(TokenKind, text)` | replace | shared lexical authority と grammar-site classification に統合する |

### Rewrite strategy

既存 `lib.rs` と `parse.rs` の中で巨大な replacement を続けず、新しい named module に
character input、session、event、sink、shared declaration grammar の vertical slice を作る。
最小 slice が leading `use`、一つの operator header、`my <ident> = <expr>`、二つの `+!` case を
end-to-end に通した時点で、old `HeaderCursor` / `lex` / `FullCstBuilder` path を同じ change で削除する。

old/new parser を feature flag や fallback として長期間並存させない。二つの lexical authority と
header grammar が残り、parity failure を隠すためである。移行中も public entrypoint は
`scan_header` / `parse_file` の一つだけに保つ。

## Required implementation tests

最初の implementation slice で少なくとも次を固定する。

1. 同じ table に infix `+!`、prefix `+`、prefix `!` を入れ、`+!a` が `+ (! a)`、
   `a+!b` が `a +! b` になる。
2. longer trie candidate が current site で無効なとき、shorter candidate の末尾へ input、
   local event、expectation error がすべて rollback する。
3. accepted candidate の後では unrelated grammar branch へ戻らない cut placement を確認する。
4. ASCII と multi-byte operator / identifier の diagnostic と header range が UTF-8 byte offset になる。
5. leading `use` と operator header の header/full projection が一致する。
6. valid operator header + malformed body で header fact は残り、body diagnostic だけが増える。
7. malformed header 後の valid header を recovery が発見し、fact transaction が partial field を
   commit しない。
8. all current fixtures で `green.to_string() == source`、event balance、range conservation が成立する。
9. every byte prefix fuzz test が panic / hang せず、`Missing` / `Error` contract を守る。
10. current narrow `scan_header` compatibility fixtures の range / fact output を意図せず変えない。

oracle differential test は tagged oracle の `+!a` result を期待値にしない。この case は今回
確認した oracle predicate bug を明示する Yulang3 architecture test とし、user-confirmed language
semantics を authority にする。

## Performance constraints

- source 全体の token vector と token text copy を作らない。
- operator lookup は prebuilt trie を一 character ずつ進み、run 全体の再走査を避ける。
- `longest_match_then` の rollback は同じ operator run 内の candidate boundary に限定する。
- event/local checkpoint は collection 全体の clone ではなく length/depth snapshot にする。
- header discovery は body を full expression parse せず opaque scan し、syntax planning のための
  軽量 phase という性質を維持する。
- full parse 中に HeaderInfo ranges を使った source 再走査や CST 再走査を追加しない。
- Rowan replay は一回だけ行い、token text は source range から borrow する。

benchmark では少なくとも parse elapsed、operator trie probe count / rollback count、event count、
token bytes、peak event capacity を測り、current fixture と Yulang2 representative corpus の
regression を見る。

## Open questions for Claude / user

1. `chasa` は crates.io `0.5.0` を exact pin するか、同 repository の workspace crate として
   source authority を戻すか。0.5.0 README は API を experimental としているため、caret range の
   無言 upgrade は避けたい。
2. dynamic operator trie の storage は oracle と同じ `qp-trie` を使うか、syntax planning が
   immutable に compile する専用 trie を置くか。chasa は traversal trait だけを提供する。
3. full operator grammar の canonical fixity set と binding-power representation を、Yulang2 の
   `BpVec` まで移植するか。current `HeaderOperator` は infix + `u16` pair だけであり、prefix /
   suffix / nullfix を表せない。
4. oracle の whitespace/fixity `judge` table をそのまま language rule として採用するか。
   `+!` example の position rule は確定しているが、prefix/nullfix/suffix が同じ spelling に重なる
   全 combination の rule は別途 fixture で固定する必要がある。
5. rollback-safe CST construction は、この proposal の event-buffer + final Rowan replay を採用するか。
   direct `GreenSink` を使うなら「speculative parser は一 event も emit しない」を型/API で
   強制する別 design が必要である。
6. local operator declaration の table update を rollback-aware overlay にするか、shared
   declaration parser が fact commit 後だけ immutable table を差し替えるか。header recovery 中の
   partial operator を live table に見せてはならない。
7. chasa expectation error と public `SyntaxDiagnostic` の bridge で、どの expectation merge を
   user-facing primary message に採用するか。`LatestSink` を exhaustive diagnostic authority に
   しない点は確定する。
8. full parse の header replay が existing `DiagnosticId` を照合する key を、shared recovery event
   sequence だけで作るか、grammar role + range も含む typed key にするか。
9. HeaderInfo/current fixture compatibility を保つ migration commit と、full fixity API extension を
   同じ slice にするか分けるか。architecture replacement と public schema expansion の review を
   分離する方が追跡しやすい。

## Implementation gates

implementation 着手前に open question 1-5 を決める。最初の vertical slice の完了条件は次とする。

- `chasa` input から shared declaration grammar と最小 Pratt expression grammar が直接 source を読む。
- `lex() -> Vec<LexedToken>` と `scan_symbol_end` を production path から除去する。
- `+!a` / `a+!b` が user-confirmed tree shape を持つ。
- `scan_header` と full parse が同じ declaration grammar を使い、fixture で parity が成立する。
- `ParsedFile.green` が lossless Rowan root で、structured diagnostic product と同じ revision に属する。
- old path への fallback がない。

## Sources inspected

- local Cargo registry `chasa-0.5.0`: `README.md`、`src/lib.rs`、`src/back.rs`、
  `src/input/*`、`src/error.rs`、`src/parser.rs`、`src/parser/choice.rs`、
  `src/parser/prim.rs`、`src/parser/token.rs`、`src/parser/str.rs`、
  `src/parser/trie.rs`、`src/parser/memo.rs`。
- `yulang2-oracle@a58eefc3`: `crates/parser/src/context.rs`、`lib.rs`、`lex.rs`、
  `sink.rs`、`op.rs`、`scan/mod.rs`、`scan/trivia.rs`、`expr/core.rs`、
  `expr/tail.rs`、`expr/scan.rs`、`expr/scan/op/{scan,judge,boundary}.rs`、
  `stmt/op_def.rs`、`stmt/mod.rs`、`tests/expr_grammar.rs`、Cargo manifest / lock。
- Yulang3 current tree: `docs/yulang3-architecture.md` §4.2.1-4.2.2、
  `crates/yu-syntax/src/{lib,parse,syntax_kind}.rs`、phase 2 parser fixtures、
  commit `e1737368` と `7022ed27`。

## Verification performed during investigation

- `chasa 0.5.0`: 12 unit tests と 124 doctests が offline で成功した。
- `yulang2-oracle` temporary copy: exact `+!` test により tagged behavior の差異を再現した。
- 同 temporary copy: `op_value_start_inner` の prefix/nullfix condition だけを OR にした実験で、
  `+!a` と `a+!b` の両方が expected tree になることを確認した。
- repository の tracked source、manifest、fixture、architecture document は変更していない。

著者: Codex gpt-5.6-sol xhigh（2026-08-20）
