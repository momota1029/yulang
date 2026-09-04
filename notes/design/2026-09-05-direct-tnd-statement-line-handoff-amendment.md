# Direct TND statement-line handoff amendment

Status: Authoritative

Scope: source-free, direct-CST-only successor rewrite における bare nominal
`TypeDeclaration` の terminal newline 判定だけ。`TND-G/J/T/R` の観測可能な文法、
CST、trivia 所有、recovery cardinality は維持し、旧 chasa parser / public dispatch /
AST / HIR / header / session / diagnostic record は変更しない。

Drafted-by: primary with architecture review

Reviewed-by: M3 compiler-referee and specification review, 2026-09-05

Approved-by: user, 2026-09-05

Supersedes: `2026-08-20-yu-syntax-chasa-architecture.md` の TND にある
ambient-owner stack / skipped-inline count を読む**実装経路だけ**。TND の grammar、
priority、recovery、scope exclusion は supersede しない。

## 1. 問題と authority

Authoritative TND は complete Type header の後で、terminal statement boundary だけを
valid Nominal の根拠にする。exact `=`、missing-`=` reusable TypePrimary、malformed
DefinitionIntroducer は Equality / recovery のままであり、`=` がないことだけから
Nominal を選んではならない。

特に次の二つは物理 newline だけでは区別できない。

- ordinary braced canonical statement sequence の newline は Nominal を閉じる。
- braced Catch arm の newline は、one-or-more inline canonical Statement crossing を経て
  TypeDeclaration に到達した場合だけ Nominal を閉じる。zero crossing は根拠にしない。

旧 TND は rollback-owned ambient stack を top-down に読み、Braced barrier と skipped
inline frame count からこの差を作っていた。しかし current direct rewrite は、ユーザーが
承認した minimal rewrite contract により、`Recover` に immutable OperatorTable だけを置く。
source、cursor、context stack、token buffer、source replay を戻すことはできない。

この追補は、ancestor の再構成を止め、nearest statement owner が必要な newline provenance
を作り、direct call chain がそれを値として運ぶ経路へ置換する。

Governing authority:

- `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の `TND-G/J/T/R`
  （19677--20277）、特に braced / Catch-inline boundary、priority、no-upgrade recovery。
- `notes/design/2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md` §3.2--3.3:
  owner/frame value の explicit threading と current-item handoff。
- `notes/design/2026-09-03-yu-syntax-minimal-rewrite-token-transaction-amendment.md`
  §1--2: `Recover` の最小性、source-free `Item`、direct procedure の immediate owner
  arguments、token-only transaction。

## 2. 提案する direct-only transport

次の lifetime-free Copy value を導入する。

```rust
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StatementLineHandoff {
    OrdinaryLayout,
    BracedStatementSequence,
    CatchBracedArm,
    CatchArmSequenceThroughInlineCanonicalStatement,
}

impl StatementLineHandoff {
    fn through_inline_statement(self) -> Self {
        match self {
            Self::CatchBracedArm
            | Self::CatchArmSequenceThroughInlineCanonicalStatement => {
                Self::CatchArmSequenceThroughInlineCanonicalStatement
            }
            other => other,
        }
    }
}
```

これは parser-wide state や `Context` bundle ではない。source、range、cursor、token、
builder、frame stack、lifetime を持たず、immediate owner argument としてだけ渡す。operator
token の stop set は字句境界、`StatementLineHandoff` は nearest statement owner の newline
authority であり、両者を一つの bit set に混ぜない。

値の生成・置換・遷移は次に限る。

| owner / entry | handoff |
| --- | --- |
| outer direct-statement harness、root canonical statement、indented canonical statement | `OrdinaryLayout` に置換 |
| braced canonical statement sequence | `BracedStatementSequence` に置換 |
| braced Catch arm の expression body | `CatchBracedArm` に置換 |
| `WithBodyTail` または `ModColonBody` が inline canonical Statement を開始 | `through_inline_statement()` |
| new indented / braced canonical statement block | その block 自身の値に置換 |
| nested expression entry、operator、ML application、parenthesis、If inline body、delimiter、Type / Pattern sub-owner | incoming value を不変で通す |

`through_inline_statement` は idempotent であり、inline crossing の正確な個数を保存しない。
TND が観測するのは zero と one-or-more だけなので、任意の深さを上限や overflow なしで表せる。
この zero/nonzero への縮約は、旧 TND の skipped-inline count を direct rewrite 内で置換する
新しい durable decision 候補である。

置換は全て lexical scope を持つ。block / Catch / inline owner は incoming Copy value を自分の
local に残し、contained parser call にだけ replacement / transition value を渡す。callee が close
して caller continuation へ戻った後は、caller が保存していた incoming value をそのまま再利用する。
`StatementLineHandoff` に push/pop mutation はなく、return value や `Recover` から provenance を
復元しない。従って completed `{ ... }`、nested Catch、inline canonical statement の後に続く outer
tail は、contained block / arm の value を漏らさない。

current direct closure では TypeDeclaration は `canonical_statement` からのみ開始し、Catch
braced arm は最初に OperatorChain を読む。したがって Catch braced arm から TypeDeclaration
へ到達する経路は、With または Mod の inline canonical Statement entry を少なくとも一度通る。
この call-graph fact が zero-inline Catch を `CatchBracedArm` のまま、newline-based Nominal
authority を持たない状態に保つ根拠となる。EOF、semicolon、active fixed stop のような
newline 以外の TND terminal familyは `CatchBracedArm` でも通常どおり個別に判定する。

### Closed current direct edge matrix

この table は C14 前の current direct call graph を閉じる。implementation は各行を
create / preserve / replace / transition のいずれかとして code と focused witness に対応付ける。

| direct entry / callee | incoming | value passed into contained parse | caller continuation after close | responsibility |
| --- | --- | --- | --- | --- |
| outer direct statement harness、`statement::statement` | none | `OrdinaryLayout` | n/a | outer root-like canonical Statement entry |
| `statement::indented_statement_block` と全 caller | any | `OrdinaryLayout` | incoming | nearest indented statement sequence replaces ancestor only inside the block |
| `statement::braced_statement_block`、`statement::braced_nud` と全 caller | any | `BracedStatementSequence` | incoming | nearest ordinary braced statement sequence replaces ancestor only inside the block |
| `case_like::arm_body` / `arm_inline_body_item` under `CatchBraced` | any | `CatchBracedArm` | incoming | Catch arm expression establishes zero-inline state only inside the arm |
| `case_like` の Case / CatchInline / Indented arm | incoming | incoming、または indented block replacement | incoming | no synthetic Catch-braced authority |
| `tails::with_inline_item` → `canonical_statement` | any | `through_inline_statement()` | incoming | first and nested With inline crossing |
| `mod_decl::parse_inline_statement` → `canonical_statement` | any | `through_inline_statement()` | incoming | first and nested Mod inline crossing |
| `driver::{expr_from_nud,required_expr_item,required_expr_after_accept,tail,continue_completed_tail}` | incoming | incoming | incoming | expression recursion never resets line owner |
| `if_expr` inline condition/body and `delimited` parenthesized/list/record expression paths | incoming | incoming | incoming | expression / delimiter preservation |
| `if_expr` / `tails` / `mod_decl` / `binding` / `for_decl` / `case_like` indented or ordinary braced statement body | any | the called block's replacement | incoming | nearest statement block wins only within its own call |
| `binding` body, `for_decl` inline iterable/body, `pattern::delimited` default expression | incoming | incoming | incoming | transitive expression preservation |
| `type_decl::type_declaration` after `canonical_statement` dispatch | incoming | consumed only by form judge | incoming | no creator or reset inside TypeDeclaration |

`struct_decl`、`use_decl`、`type_expr` と direct lexer are not implicit creators: C14 pre-write
inventory must list their actual calls to the five named entry families and show either an existing
matrix row or direct unreachability. The same inventory must enumerate every current call to
`canonical_statement`、`expr_from_nud`、`required_expr_item`、`indented_statement_block`、
`braced_statement_block`; a default `OrdinaryLayout` at an omitted edge is forbidden.

future inline statement owner、statement sequence owner、Catch の direct statement entry、
declaration companion が TypeDeclaration を reachable にする時は、successor/addendum に explicit
edge row、compiler/spec review、user approval を追加するまで `StatementLineHandoff` を受け取れない。

## 3. TypeDeclaration form judge

name と same-line parameter scan が終わった後、TypeDeclaration は maximal post-header trivia と
次の一 logical payload からできた pending Item を
一回だけ受け取る。その leading trivia は form decision まで emit しない。classifier は input、
`Recover`、Rowan を mutate せず、次だけの total function である。

```text
(header completion, pending Item, baseline, active token stops,
 StatementLineHandoff, Option<ActiveStatementCompanion>)
    -> TypeDeclarationFormDecision
```

```rust
enum TypeDeclarationFormDecision {
    Equality { name_was_incomplete: bool },
    Nominal(NominalBoundary),
    EqualityRecovery,
    IncompleteHeader,
}

enum NominalBoundary {
    EofOwnedTrivia,
    OuterSemicolon,
    OrdinaryLayoutNewline,
    BracedStatementSequenceNewline,
    CatchArmSequenceNewlineThroughInlineCanonicalStatement,
    ActiveFixed(TokenKind),
    AmbientCompanion,
}
```

`NominalBoundary` は selected form を commit するためだけの local evidence であり、`Recover`、
`Item`、CST、AST に保存しない。

If companion は free boolean や raw spelling では渡さない。C14 は `if_expr::arm_keyword` と
Type form judge が同じ exact-maximal/layout rule を使う、shared source-free helper を抽出する。

```rust
enum ActiveStatementCompanion {
    Elsif,
    Else,
}

fn active_statement_companion(
    i: RewriteIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> Option<ActiveStatementCompanion>;
```

これは corresponding `STOP_ELSIF` / `STOP_ELSE` が active であり、current `if` continuation
owner が same original gap を受理し、source-only suffix probe が exact word を確認した時だけ
返す。ordinary `elsif` / `else`、operator suffix を持つ spelling、inactive stop は `None` である。
TypeDeclaration は original pending Item と live suffixからこの helper を一回だけ呼び、その
`Option<ActiveStatementCompanion>`を typed evidence として pure classifierへ渡す。classifier 自身は
sourceを読まず enum だけを使う。returned Item は companion owner へ non-consume で返る。active
companion claim は exact equality probe より先に原 gap を owner へ返し、rejected braced-newline
evidence の後には equality を妨げない。

priority は TND-J を次で direct form に写す。

| priority | original pending Item 上の条件 | decision / ownership |
| --- | --- | --- |
| 1 | name Incomplete + exact `=` | `Equality { name_was_incomplete: true }`。sole Name recovery の後、DefinitionIntroducer Missing を重ねず equals / TD-T RHS へ |
| 2 | name Incomplete + terminal / other Item | `IncompleteHeader`。shared Name owner だけが recovery を持ち、Nominal / Definition / RHS を cascade しない |
| 3 | name Complete + `active_statement_companion(...)` | `Nominal(AmbientCompanion)`。Item と gap は caller へ non-consume |
| 4 | name Complete + accepted same-line または strictly-deeper `Gtype*` の直後に exact lone `=`、かつ row 3 が None | `Equality { name_was_incomplete: false }`。trivia と equals を TypeDeclaration が emit し、unchanged TD-T RHS へ cut |
| 5 | name Complete + physical newline + `OrdinaryLayout` + indentation `<= baseline` | `Nominal(OrdinaryLayoutNewline)`。whole Item を handoff |
| 6 | name Complete + any physical newline + `BracedStatementSequence` | `Nominal(BracedStatementSequenceNewline)`。whole Item を braced sequence へ handoff |
| 7 | name Complete + any physical newline + `CatchArmSequenceThroughInlineCanonicalStatement` | corresponding Nominal。whole Item を Catch arm sequence へ handoff |
| 8 | name Complete + physical newline + `CatchBracedArm`、または `OrdinaryLayout` + indentation `> baseline` の後に EOF ではない logical payload | no nominal line authority。existing Equality recovery pathへ |
| 9 | name Complete + physical newline なしで EOF または outer semicolon | Nominal。same-line trivia だけ TypeDeclaration が所有し、EOF / semicolon は outer-owned |
| 10 | name Complete + physical newline なしで active `Comma` / `RParen` / `RBracket` / `RBrace` | `Nominal(ActiveFixed(..))`。exact active token を handoff |
| 11 | name Complete + `OrdinaryLayout` + strictly-deeper trailing trivia の後が EOF、かつ preceding nominal row がない | `Nominal(EofOwnedTrivia)`。row 8 は EOF でない payload に限るため、trivia を TypeDeclaration が一度だけ所有 |
| 12 | name Complete + その他 | existing DefinitionIntroducer / RHS `EqualityRecovery` |

`STOP_LINE_BREAK`、colon、left brace、arrow、`in`、`with`、raw declaration-starter spelling、inactive
close は Nominal evidence ではない。malformed post-header byte を Error として emit した後に
boundary を再検査して Nominal へ upgrade してはならない。Equality を選んだ後の RHS failure も
Nominal fallback を許さない。

この classifier は current rewrite の Item protocol と整合する。将来の Gate 4 が
`Item::Boundary` vocabulary を完全実装する際も、lexical `Item` に ancestor provenance を格納しない。
Boundary の lexical/layout/stop classification と statement-line handoff は別責務のままにする。

future Item adapter は次を exhaustively preserve する。C14 は current token / EOF Item だけを
実装し、Gate 4 はこの表と同じ form evidence を使うか、この addendum を supersede する。

| future pending payload | Type form evidence | ownership |
| --- | --- | --- |
| `EofAfterTrivia` | physical line evidence を先に rows 5--8 へ通す。ordinary equal/shallow は row 5、braced sequence は row 6、Catch-through-inline は row 7、zero-Catch は row 8。physical newline がなければ row 9、ordinary strictly-deeper newline だけが row 11 | rows 5--7 は whole Item を handoff、row 8 は recovery、row 9 / 11 は TypeDeclaration が該当 trivia だけを所有する。EOF terminal 自体は outer owner のままで、Item identity を置換しない |
| `Stop(Semicolon)` | physical line evidence を先に rows 5--8 へ通す。newline がなければ、outer statement separator proof が active な時だけ row 9。ordinary strictly-deeper newline と zero-Catch は row 8 | rows 5--7 は token を含む whole Item を outer sequence / Catch owner へ handoff。row 9 は same-line trivia を TypeDeclaration、semicolon token を outer owner。row 8 は existing recovery |
| `Stop(Comma/RParen/RBracket/RBrace)` | row 10 only when the exact matching stop proof is active | retained token と gap を byte-identically handoff |
| `Stop(LineBreak)` | never alone Nominal evidence | StatementLineHandoff と original leading trivia が rows 5--8 を決め、boundary は non-consume |
| `Stop(other)` | no Nominal evidence | existing recovery / caller handoff |
| `Dedent(LayoutEvidence)` | only `OrdinaryLayout` and equal-or-shallower evidence may use row 5 | active layout owner retains the same boundary identity |
| `Close(Delimiter)` | no Nominal evidence by itself | inactive/local close is not upgraded; existing owner decides |
| `BorrowedClose(Delimiter)` | row 10 only after exact active-owner proof | missing/wrong owner is fail-fast; no reclassification or consumption |

The table does not add a Boundary variant, stop bit, or ancestor field to Item.

## 4. CST と trivia

valid nominal は既存 `TypeDeclaration` node だけを持ち、Nominal wrapper、empty body、dummy
equals、empty TypeExpression、Missing、Error を作らない。

- Equality: accepted continuation trivia と `=` は TypeDeclaration が所有し、TD-T RHS は不変。
- same-line EOF / semicolon: same-line trivia は TypeDeclaration、EOF / semicolon は outer owner。
- deeper-trivia + EOF: maximal trivia は TypeDeclaration が一度だけ所有。
- layout / braced / Catch-through-inline newline、active fixed stop、ambient companion: pending Item と
  leading trivia を同一 identity のまま caller へ返す。
- Equality recovery: existing DefinitionIntroducer / RHS owner が同じ Item を consume または handoff
  し、TND-R の cardinality を保つ。

source rewind、second logical item、token vector、speculative TypeExpression parse、Rowan rollback は使わない。

## 5. C14 implementation boundary

C14 は transport だけの dead scaffold に分けず、isolated direct bare Nominal terminal familyを
一つの coherent gate として実装する。

1. `StatementLineHandoff` を direct statement / expression transitive cone へ明示 thread する。
2. braced statement sequence、braced Catch arm、With、Mod の table transition を実装する。
3. `type_decl.rs` の post-header trivia emission を form decision 後へ遅延し、pure direct classifier と
   Nominal emission / handoff を実装する。
4. complete header terminal familyを atomic に Nominal へ置換する。exact equality と existing
   Equality recovery は同じ gate で preservation fixture を再実行する。

対象候補は `rewrite/{driver,statement,tails,mod_decl,case_like,if_expr,delimited,binding,for_decl,
pattern/delimited,type_decl}.rs` とその direct focused tests である。`struct_decl`、`use_decl`、
`type_expr`、lexer の actual reachability も §2 matrix inventoryで明示する。実装で call graph が増えるなら、
この list と transition table を先に拡張して design reviewへ戻る。`Recover`、public/root parser、
AST/HIR/header/session、legacy grammar、typed diagnostics、Yumark は C14 の scope 外であり、Gate 9 まで変更しない。

form migrationを開始する前に、C14 ownerはdirect focused fixture inventoryを作る。inventory は each
complete-header direct expectationを、EOF、same-line EOF、deeper-trivia EOF、semicolon、ordinary
equal/shallow newline、direct-braced newline、Catch-through-inline newline、active comma / each right
close、ambient companion のいずれかへ一行ずつ対応付ける。changing expectation は旧
`Missing DefinitionIntroducer` removal と zero-recovery Nominal を一組で記録し、missing name、
malformed introducer、positive equality evidenceを変更集合から除外する。public / legacy fixtures、
AST expectation、header fixtureは編集禁止であり、Gate 9 まで inventoryの preservation controlとして
扱う。

## 6. Required evidence

Focused direct matrix は少なくとも次を持つ。

- EOF、same-line trivia + EOF、strictly-deeper trivia + EOF、outer semicolon。
- each `StatementLineHandoff` の equal / shallow / deeper newline classifier control。特に
  `OrdinaryLayout`だけがequal/shallow、`BracedStatementSequence`とCatch-through-inlineだけがany
  physical newline、`CatchBracedArm`はneitherをNominalにしないこと。
- root / indented の equal-or-shallower newline、direct braced sequence の equal / deeper newline。
- `catch action { A -> value with: type Point\n B -> fallback }`、nested With → Mod inline、任意の
  additional inline depth、nested normal braced block が Catch provenance を置換する control。Catch
  next arm がstrictly deeperでもordinary-layout resetで偶然通らないことを固定する。
- completed braced block の後に outer `with:` が続く control（`{ x } with: type Point\n  next`）と、
  completed nested Catch の後に outer tail が続く control。contained block / Catch arm の handoff が
  close 後の caller continuation へ leak せず、outer `OrdinaryLayout` judgement を使うこと。
- braced Catch zero-inline negative control。recoveryで TypeDeclaration が強制的に到達しても
  `CatchBracedArm`はnewline Nominal authorityを得ないこと。
- exact `=` same-line / strictly-deeper、shallow newline before `=`、multiline equality RHS。
- active と inactive の comma / each right close、active `elsif` / `else` と ordinary same spellings。
- incomplete name + exact `=`、incomplete name + terminal、malformed-name + exact `=`、retried-complete
  name + terminal、reusable RHS without `=`、malformed introducer to `=`、malformed introducer to
  boundary、missing RHS、`type Point @`、`type Point ('a)`。one slot = one recovery cardinalityを持つ。
- `impl` / `with` / `derives` / colon / brace non-Nominal scope controls。
- every handoff の pending Item identity / leading trivia、valid Nominal 下の zero Missing / Error /
  TypeExpression、lossless green tree。
- current and future Item adapter tableの各 Boundary variant、active-stop proof、retained-token
  identity、`STOP_LINE_BREAK` non-evidence control。特に `EofAfterTrivia` と `Stop(Semicolon)` は
  same-line、ordinary equal/shallow、ordinary deeper、braced sequence、Catch-through-inline、zero-Catch
  を別々に固定し、table の full priority を省略実装できないようにする。
- existing direct TypeExpression、statement, With, Mod, Catch, If, delimiter, Binding / Use / Struct / For
  focused controls。pre-edit inventoryで指定したpositive equality evidenceはunmodifiedで再実行する。

新しい traversal、allocation、clone、cache、replay は計画しない。implementation inspection でそれらが
現れた場合だけ performance review を追加する。

## 7. Rejected alternatives

- `Recover` に ambient owner stack を復活: approved minimal rewrite contract に反する。
- raw `STOP_LINE_BREAK` または private token-stop bit: braced / Catch identityとzero-inline Catch rejectionを
  lexical stop と混同して隠す。
- provenance を `Item` に保存: same lexical Item の意味を ancestor grammar に依存させ、Item の
  byte ownershipと混線する。
- closure / callback を TypeDeclaration に渡す: lifetime / capture を増やし、closed four-state relationを隠す。
- numeric inline depth: TND に必要ない exact count、overflow、artificial nesting limitを持ち込む。
- source probe / replay、speculative TypeExpression: current-item completionで足りず、one-forward contractに反する。
- malformed recovery後の nominal reclassification: TND-R の no-upgrade / no-cascade に反する。

## 8. Approval questions

この Draft を Authoritative にする前に、次の三点の user approval が要る。

1. old ambient stack query の direct-only replacementとして、四値 `StatementLineHandoff` を採用すること。
2. skipped inline frame count を、TND が観測する zero / one-or-more へ縮約すること。
3. transport と complete bare Nominal terminal family を C14 の一 coherent isolated gate で実装し、
   public / AST migration を Gate 9 まで deferred にすること。
