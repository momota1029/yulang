# Unary lambda parser construction preservation

Status: independently reviewed source-derived local construction theorem
Date: 2026-10-15
Producer: primary-assigned constructive proof leaf; no delegation or self-certification
Current baseline: `77870d2078389d3ab6fb1961b42b5f261317ef24`
Branch: `research/simple-sub-intrusion`
Snapshot: baseline plus the primary's final frozen parser/capability working diff; exact manifest below
Authority: `notes/design/2026-10-15-unary-lambda-parser.md` §§2–4
Requested runtime: `gpt-6.1-sol` / `high`; observed model and effort unknown
Parent gate: local parser obligations 1–4 discharged after independent review and primary verification; HIR/inference/runtime remain OPEN

This note derives the four assigned local construction obligations from the
final source constructors and consumers. It retains the original quantified
claim and compact records of the failed source routes. The fresh-child
argument uses the actual retained/rebased recovery activation; it does not
assume that clearing an activation proves child boundary preservation.
No test result is a premise of the derivation.

## Frozen statement and scope

For every finite UTF-8 source suffix at a reachable expression admission
point, quantify over every accepted immutable operator table, caller baseline,
Stops mask, line handoff, immediate origin/line-entry fact, optional fence,
ambient and sequence context supplied under the existing current-Item
invariant I. Include malformed prefixes and bodies, all raw Unicode identifiers
and terminal `?`/`!` suffixes, opaque multiline block comments, ordinary/quoted
fenced cells, NUD entry, actual LED ML entry and nested ordinary body constructs.
No alphabet, case-count or header/body-length bound is introduced by this proof.

I is the existing current-Item contract: live input and origin describe one
suffix of the same source allocation; each current Item owns exactly its
accepted physical prefix and payload (or accepted leading at a pending
boundary); its emission cursor records emitted leading parts; foreign quote
prefix splits are ordered, exact and belong to that Item; the pending fence
line remains unconsumed. Existing coordinates/scanner counters fit their
representation. Forged Items and resource exhaustion are not added accepted
source cases. These are infrastructure hypotheses, not new lambda admission
restrictions.

The original conclusions, unchanged by the failed attempts, are:

1. Failed complete-header admission has no parse effects and preserves the
   previous nonmatching operator/recovery route.
2. Matching headers consume each source Item once, preserve every byte and
   own introducer/binder/arrow in one LambdaExpression; introducer leading
   precedes that node.
3. The body obeys enclosing expression boundaries and recovery progress;
   recognized header structure survives absent/invalid body recovery.
4. Production NUD and actual LED ML admission use the same maximal binder/
   exact-arrow complete-header predicate before dynamic backslash selection.

“Enclosing boundary” has its approved ordinary grammar meaning at the current
lexical depth. A local comma/close/separating newline/fence stays with its
existing owner. An accepted If companion, path-name slot, delimiter interior
or indented body retains its own grammar. A raw physical newline is not, by
itself, an assertion that the outer lambda must end. This distinction preserves
the original scope and does not remove malformed or compound bodies from it.

Exclusions: global recursive parser termination, exhaustive diagnostics,
implementation of every pre-existing ordinary grammar rule, HIR binding,
capture, inference/Call/effect hygiene, soundness/principality and runtime.
This is a local parser-construction proof, not any of those broader theorems.

## Operational base and production reachability

The current-Item normalization addendum §§3–5 supplies the established lexical
contract. Actual owners are `lexical/current_item.rs::{current_item,
scan_current_item,boundary_item,classify_line}` and the fenced comment scanner
in `lexical/lexer.rs`. `cursor.rs::SyntaxIn::token` supplies unit-state LexIn
with immutable operator access and no Rowan builder. `chasa-recover` owns
input/recoverable-state rollback in `In::token` / `Token::run_once`; failed
transactions cannot publish CST or diagnostics.

`lexical/item.rs::{Item::finish,emit_all_remaining_leading,emit_remaining,
emit_leading_range_with_cursor,emit_payload_with_cursor,emit_physical_text}`
are the existing physical emission kernel. Its leading cursor advances
monotonically; source text/foreign fragments remain in physical order; payload
emission consumes the Item by value. Rowan uses those exact strings to derive
ranges. This proof reuses that established kernel and Rowan behavior; it adds
no range ledger, source reconstruction or second CST.

Production entry is concrete: `full_parse::parse_file` freezes the effective
operator table and calls `cursor::parse_root`. Root Statement scanning passes
through `statement::scan_statement_item_lexical`, `current_item`,
`scan_statement_payload`, then `scan_expression_payload` at NUD for a slash.
Canonical expression dispatch calls `expr_from_nud_normalized` / `append_nud`.
Normal expression children use `expression_item` /
`scan_expression_item_lexical`, which reach that same production payload
scanner. After a primary, `scan_tail_after_accept_normalized` requests it at
OperatorSite::Led. The proof does not infer production reachability from the
test-only optional NUD scanner.

## Header derivation: obligations 1, 2 and 4

`scan_lambda_backslash` borrows the current source and performs `strip_prefix`,
two `lambda_inline_suffix` observations, `source_identifier`, and
`is_exact_arm_arrow` before its only consuming `with_str(... next())` call.
Every rejected prefix returns before that consumption and before constructing
a Backslash Token. Observers allocate no successor Item, split carrier,
diagnostic or Rowan output. Both payload sites invoke this operation inside
`i.token(...)`; its failure leaves the old record-spread/arrow/keyword/
operator/assignment/dangling/token chain in its previous order. The shared
ordinary trivia observer still selects its prior `opaque_comments=false`
mode; only header gaps request logical mode. This proves effect-free failure
and preservation of nonmatching routing. A later complete header during normal
recovery, including a second slash after a rejected first one, remains allowed.

For admission/consumption correspondence, let p be the admitted slash payload
coordinate. The observation computes slash, maximal permitted gap G, maximal
raw Identifier, G, exact Arrow. The second gap coordinate is p plus the
physical byte-length difference of the original and after-binder suffixes.
No character-count approximation is used.

The gap correspondence follows the actual trivia cases:

- space/tab consume identical maximal bytes;
- CR, LF and CRLF outside a BlockComment produce logical newline and reject;
  a line comment consumes to its newline, which likewise rejects;
- nested BlockComments use the same open/close depth transitions. Their
  internal newlines are opaque to logical layout, matching one BlockComment
  part. An unterminated comment leaves no visible binder/arrow;
- fenced observation and consumption use the same `judge_fence_line` after
  LF/CRLF. Close/transition/EOF rejects observation. Accepted quote prefixes
  are skipped observationally and physically retained by the subsequent
  current Item and its foreign split. Bare CR is a logical newline but no LF
  fence transition. Opaque-comment state restoration affects logical facts,
  not physical fence checks or byte-coordinate advancement.

Hence every admitted gap leads actual consumption to the same payload suffix
without crossing a fence. `source_identifier` and `scan_identifier` share
`_`/XID_Start, maximal XID_Continue and at most one terminal `?`/`!`, so their
UTF-8 boundaries coincide. The binder consumer calls the raw scanner,
bypassing dynamic word operators and contextual expression keywords.
`scan_arm_arrow` calls the identical `is_exact_arm_arrow`; a following
operator-shaped scalar prevents splitting `->>` into `->` and a remainder.

The accepted current slash Item consumes only its slash payload. `append_nud`
then enters `lambda_nud_normalized`, emits remaining slash-leading outside
the LambdaExpression and the slash within it, and acquires exactly two further
current Items with raw Identifier/Arrow scanners. The correspondence just
proved supplies their actual token outcomes; their `expect`s are not an
assumed lambda-specific transition. `suffix_marker`/`advanced_origin` advance
by exact consumed-byte deltas; each non-multiline token returns InLine.
Header Item emission by value and the existing leading cursor preserve all
bytes once. Gap/quote-prefix bytes belong to the following binder/arrow Items
inside the node. Lookahead is an extra read, not extra consumption/emission.

Both production NUD and LED reach the same `scan_expression_payload` branch
before dynamic operator selection. The predicate receives no site, BP, Stops
or operator-table parameter. Literal-first dispatch cannot steal a slash.
Backslash is included in `is_normal_core_item` / `is_nud_item`. At LED,
`is_ml_argument` additionally enforces its existing nonempty gap, All mode and
layout eligibility. `ml_argument` wraps the primary, and `append_nud` dispatches
the same Backslash owner even under its incoming None ML mode/threshold.
Complete headers thus beat registered backslash at any BP, and `g \i -> ...`
has the required production route. This does not invent a gapless ML separator.

## Body construction and the actual recovery invariant

`lambda_nud_normalized` commits the full header before opening the body's
OperatorChain. It passes threshold None and MlMode::All, preserving original
baseline/Stops/line/fence/ambient/sequence values. Thus the outer ML argument's
None mode or association threshold cannot truncate `g x` in `f \x -> g x`.

Immediately after header consumption it performs `stops | C`, where
`C = LAMBDA_RECOVERY_BOUNDARY = 1 << 15`. The definition in `lexical/stops.rs`
is exactly

```text
lambda_recovery_boundary(s,b,L)
  = (s & C != 0) && implicit_delimited_newline(b,L).
```

The latter uses existing logical Newline-part indentation at or below b,
excluding opaque BlockComment contents and foreign quote-prefix parts. C is
private immediate recovery activation, not a token stop: `active_stop` and
`active_stop_item` do not recognize it. Lexical maximal matching and ordinary
operator/continuation selection therefore retain their existing meanings.
With C absent the new predicate is identically false; no-stops standalone
mandatory operand retry retains its existing behavior.

The invariant R is constructional: at each mandatory expression slot reached
under activation, an Item qualifying as its current owner's implicit boundary
is retained before leading/payload emission or NUD retry; malformed preceding
Items remain emitted once. Accepted child owners may claim that Item only
under their own ordinary separator/introducer/continuation rules. Activation
is retained while baseline and token stops follow each actual local owner.

`required_operand::required_expr_item_with_boundary` establishes R at three
actual consumer positions: initial classification before any emission; the
Error loop's successor classification before NUD/another iteration; and the
post-run check before `append_nud`. The loop retains the exact Item, emission
cursor, fragments, origin and line-entry fact. The post-run guard prevents a
stopped Error run from immediately reaccepting its boundary as a primary.
The lambda's outer initial slot also uses the existing inline-slot boundary
predicate to protect separator/close, active stop and missing body cases.

`operator_nud` / `operator_tail` forward unchanged Stops/baseline into
`required_expr_after_accept_normalized` and hence those three guards. Same-line
and strictly deeper retries do not satisfy the predicate and continue normally.
A stopped unrelated Identifier at a separating newline is not an eligible ML
argument when ordinary tail continuation resumes. Ordinary valid continuation
roles are still chosen by their existing owners.

## Accepting consumers cannot bypass a protected return

The source bridge must include consumers after the shared required parser;
storing/checking C at that parser alone is insufficient. The final code has
the following complete local acceptance guards.

| Source owner | Action before consuming/emitting |
| --- | --- |
| If condition | `condition_normalized` checks R before leading emission and includes it in condition-missing classification. |
| If missing arm | `missing_if_arm_normalized` receives original baseline/Stops and guards returned Item/EOF leading. |
| If Colon | `if_arm_normalized` dispatches protected Items to missing/handoff before token-kind Colon admission. |
| Case/Catch optional label and scrutinee | Head checks R before SigilIdentifier label emission; shared required parser gets inherited Stops. |
| Case Colon / Catch LBrace | Head's protected-return branch precedes either introducer match. |
| Catch optional comma | `arm_normalized` requires non-protected leading under actual arm_baseline before emitting the comma. |
| Catch handler Pattern | Its acquired handler Item is checked under actual arm_baseline before `pattern_from_entry_item_normalized`. Protected Items use existing `finish_absent_arm_normalized` handoff. |
| Guard keyword / guard operand | Arm filters keyword admission by R; `guard_normalized` checks leading before shared required dispatch. |
| Arm Arrow | Protected-return branch precedes Arrow emission, so Arrow indentation cannot rebase a previously protected Item into an accepted body. |
| For inline body | Checks R before leading emission and passes Stops to shared required parsing; earlier Pattern/In/iterable/body-introducer owners already check their actual implicit/outer boundary. |

The Catch handler check is deliberately at CaseLike's caller boundary. Pattern
entry can rebase its own baseline before primary admission; that does not
justify giving a protected handler Item to it. The check preserves standalone
Pattern grammar rather than assuming its admission proves caller ownership.
CaseLike's `missing_block` already preserves ordinary-newline-bearing
non-EOF returned Items. Missing/absent-arm helpers publish recovery without
emitting the protected payload or erasing its leading.

Assignment, inline Colon and With have existing initial/retry inline-boundary
checks and forward activated Stops to admitted same-depth expression/Statement
children. Binding's `binding_body_static_boundary` similarly checks implicit
layout before its initial/retry body. Fixed field/path recovery retains
nonempty leading for ordinary continuation; its accepted name-slot behavior
is not replaced with a blanket raw-newline ban. Type annotation forwards caller
Stops; `type_expr::is_required_type_boundary` already checks
`!type_chain_trivia` before initial parsing, at Error termination and post-run.
These are specific source predicates, not an assumption that every valid
ordinary slot must reject a physical newline.

## Fresh child owners retain activation at their own boundary

The final construction retains activation, rather than clearing it and
assuming the child is correct. Its scope changes are explicit:

| Child owner | Construction and discharge |
| --- | --- |
| Parenthesized/call/index/projection | `delimited_items_normalized` rebuilds local comma/semicolon/close stops, retains inherited closes and C, and computes its own baseline. Its loop accepts the local close first and owns internal explicit/implicit separators. A returned newline Item changes phase before its next local item parse. |
| Indented Statements | `indented_statement_block_normalized` retains Stops/C, derives block_indent, and sends that actual baseline through its Statement sequence and expression dispatch. `indented_statement_successor_normalized` owns a same-indent sibling and returns a dedent. Shared required recovery retains the Item long enough for this decision. |
| Braced Statements | Expression/For entry calls `braced_statement_block_with_recovery_normalized`; it builds local RBrace stops plus inherited C, derives local baseline and runs the existing Braced sequence. `braced_statement_successor_normalized` owns local newlines/items and closes. The older declaration wrapper supplies zero activation for its independent entry contract. |
| Indented Case/Catch and Catch braces | `arm_sequence_normalized` retains outer C; policy selects actual arm baseline, pattern/body stops and successor. Arm expressions receive `body_stops | outer_stops`. Their local sequence decides siblings/closing boundaries after guarded child returns. |

For the former dedent obstruction `\x -> if ok:\n  @\n  value + @\nnext`,
the block now carries C at block_indent=2. A same-indent next Statement is
returned to and claimed by the block's sequence; the dedented `next` likewise
returns from mandatory recovery but fails that sequence's sibling check and
propagates outward. It is not consumed before the sequence sees it. The outer
If then returns an unrelated `next` through its original baseline/Stops, and
the lambda's ordinary outer chain leaves it for the root owner. This directly
establishes the missing fresh-child operational premise.

The delimiter/Statement/CaseLike wrappers retain original outer arguments as
immutable values while calling children, then restore them by their existing
`continue_normalized_tail`/return calls. There is no mutable flag or BP stack
to repair after recovery. Nested lambda introduces C for its own body. Existing
literal/Rule opaque grammars retain their dedicated ownership and return to
`append_string_literal_nud` / `append_rule_literal_nud` with original outer
arguments; their internal text is not a prospective outer separator.

## Local composition, progress and limits

Induct over the actual finite construction trace of the expression and its
current-depth mandatory/accepting consumers. The lambda constructor supplies
activation and I; the three shared guards preserve each required slot; every
listed pre-emission/introducer/Pattern adapter preserves protected Item identity;
a fresh frame retains activation and uses its actual local baseline/stops;
its sequence claims local separators or returns the boundary; return restores
outer arguments. Recursive/nested lambdas repeat the same constructor. This
uses actual source transitions, including fresh child disposition, not a
checker assuming those transitions or an unproved child-boundary axiom.

Each continued lambda/shared lexical Error iteration emits a nonempty
already-scanned malformed payload before acquiring a successor. Boundary/EOF
or a retry exits; added guards only add exits. Inline/tail/Statement lexical
runs use the same nonempty-payload pattern, with local sequence phase/sibling
handling at the owners above. No same-Item non-consuming retry is introduced.
This proves the assigned local recovery progress, while global recursive
parser termination and resource behavior of unrelated grammar internals stay
outside scope.

Fence/active-stop Items retain their existing current-Item handoff, including
fragments and immediate line-entry fact. Ordinary EOF retains its established
trailing-leading publication rule; a fenced EOF remains a pending boundary.
All recognized header tokens precede recovery and never roll back. No path
reconstructs a binder, duplicates an Item or manufactures body input by
consuming a caller-owned boundary.

Consequently obligations 1/2/4 follow from the header/predicate derivation and
3 from the actual activated consumer/child sequence construction on this
snapshot. The producer submitted this as a local proof candidate; the primary's
independent review and adjudication are recorded below. Shared base
assumptions are I, the existing lexical transaction and physical Rowan emission
contracts; ordinary grammar meanings remain as approved. No additional
lambda-specific transition is assumed. Independent review assessed this
source correspondence and its coverage. No global parser, HIR or inference
claim follows, and no exhaustive malformed-diagnostic catalog was established.

## Compact failed-route history

- Original snapshot: baseline `71f649bbc1a856c6255e34decf2304edd52ed5af`
  plus the first parser diff. Public-source witness:
  `infix (<+>) 50 51 = 0\n\x -> y <+> @\nnext`.
  Header discovery and `effective_full_parse_operators` install the real infix
  table; root uses baseline0/STOP_SEMICOLON. Dangling infix is admitted before
  invalid `@`; cap-free required Error recovery retries newline-leading `next`
  into the body. The primary reports independent MAJOR confirmation and exact
  regression reproduction. The leaf ran no probe.
- Rejected unconditional-baseline repair: the primary reports failure of the
  established no-stops direct-helper retry `@\r\n界`. Final activation preserves
  that route. Tests were evidence for adjudication, not a source theorem.
- First capability repair retained initial/shared guards but cleared activation
  at fresh layouts and omitted structural consumers. The dedent witness above
  falsified its inherited-child premise; `\x -> if @\nnext` exposed leading
  emission during missing-arm handoff. Its attempted compositional closure was
  explicitly withdrawn. No parent gate was promoted.
- Rebased repair added actual child-local disposition and guarded structural
  introducers. Remaining Catch witnesses were `\x -> catch v: p\n, q -> value`
  and `\x -> catch v: p,\nq -> value` (LF/CRLF). Final CaseLike now checks the
  optional comma and handler entry before consuming/rebasing. Causal fixture
  corrections (`@label` not being SigilIdentifier; non-admitted infix before a
  shallow newline) never narrowed the theorem.

The proof-obligation-economy audit classified the repeated missing premise as
class-A actual boundary ownership. The work therefore moved to owning
construction/accepting consumers instead of adding another reconstruction
relation or restricting source. This history remains a failed-route record,
not an additional current proof prerequisite or competing semantic baseline.

The original 33-entry dependency snapshot is reconstructible from the current
manifest: use its first 33 paths and the five historical overrides below.
The first capability snapshot's 43-entry manifest SHA-256 is
`2691eff3bcf38f7f1aa09e6330325d338a83bc8910fbac18cac225abbc48196e`; it is historical and not a current premise.

```text
f0974df464e9f46a0cfbb8cc468cc49f7cec53cf63138c3e00ed24c49567eb0a  crates/yu-syntax/src/expression/lambda.rs
75fb0c1387d472091920a367b56b8ca55cc9f897798532ef504886d7cdf73111  crates/yu-syntax/src/expression/required_operand.rs
2d6f43b2b02a560d7ad1aa76929969908df34fe6d884783b34baa9edc5f81b08  crates/yu-syntax/src/expression/delimited.rs
e52a218dbf06f91f76ca6cf33edfb64183dcd02d0d34ee3757aff0f042403062  crates/yu-syntax/src/lexical/stops.rs
dc18a26663b4351b774a930bfcc8b343cf0c41651960b49ec2f2c6e744b0e89d  crates/yu-syntax/src/statement.rs
```

## Independent review and primary adjudication

Fresh compiler referee `lambda_handler_delta_review`, who did not produce this
note, reviewed the frozen candidate
`1b15e1cbee27067dc5cbe5e97d8cfb83dfb1b5f1995986f73ea58d73d4518fbd`.
It found no blocking, major or minor finding and confirmed all four original
local obligations, including actual child-local sequence disposition and both
Catch handler seams. It independently verified all 45 dependency hashes.
The present status/review text is the primary's later record-only addition.

The primary accepts that result for the original local construction scope and
has separately rechecked all 45 current hashes. M3 code/specification delta
reviews converged; final verification has 20 focused lambda passes, 1417 syntax
library passes with one existing manual measurement ignored, and a successful
playground package check. These checks support implementation correspondence;
they are not premises of the theorem. See the
[implementation record](../progress/2026-10-15-unary-lambda-parser.md).

This discharges the parser construction gate. Its inherited lexical/physical
emission/ordinary grammar contracts remain explicit. HIR, callback typing,
inference, runtime and whole-language soundness retain their separate owners
and OPEN status.

## Checks, resource use and historical handoff

Only `notes/theory/2026-10-15-unary-lambda-parser-preservation.md` changed under
this exclusive lease. Reads used cat/sed/rg and read-only Git status/diff/HEAD;
SHA-256 capture and static note integrity checks are recorded with the handoff.
This leaf ran zero tests/builds/parser/model probes/timing samples and spawned
no agents. The primary remains sole verification/Git owner. Work used bounded
static delta passes in response to explicit primary packets, no heavy or
background processes; exact CPU/RAM/wall time were not measured. Requested
Sol/high, observed model/effort unknown. Tests reported by the primary were
not rerun or certified by this producer.

The producer's next action at freeze was independent proof review against the
source manifest; that action and primary adjudication are recorded above.

Original producer commit packet (review status at handoff): exact leased path above; baseline
`77870d2078389d3ab6fb1961b42b5f261317ef24`; final dependency hashes below;
frozen unreviewed source-derived local proof candidate; no gate-status promotion.
Checks: source/authority correspondence, dependency hashes and static document
integrity only. Proposed message:
`research: derive unary lambda parser construction preservation`.
Shared-record deltas left to primary/curator: consume the reviewed proof at
original obligations 1–4, retain failed-route provenance and source snapshot,
and record the parser gate result only after independent review/verification;
keep HIR, inference and runtime owners separate. No shared record was edited.

## Final source dependency manifest (45 entries)

This is the single current manifest. Tests are not proof premises. Any change
requires checking its affected derivation; a design status-only amendment can
be classified separately from changed governing §§2–4.

```text
fdfeb76e0fef7f6725c7240a71f50cd63191c1eb6c5fdc0581f921e8fe447cfd  notes/design/2026-10-15-unary-lambda-parser.md
95f5a0d5ec9c70f506a907e7d44ae9e47bfcab990eb02147264ed6ae909669af  notes/design/2026-09-05-fenced-current-item-normalization-addendum.md
303d4dbcad1030b2a3f270a677b0cbfe697bf703c6cd39f159f88348da69bffe  crates/chasa-recover/src/input.rs
1fdc8ba6be46b8f34a6224f7687d1f192b086273180d5b7f593397b98df09bbf  crates/chasa-recover/src/parser.rs
f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142  crates/yu-syntax/src/cursor.rs
de091c117486f7990dc6872bf2ee7659c0e3e7e148e255f47b56b7836fe7c59d  crates/yu-syntax/src/cursor/recovery/emit.rs
05d874dd4c2874eb7b24038467c8a74b22fa6f7821a3980f3348683ad02743f1  crates/yu-syntax/src/expression/mod.rs
56357346a0f59330a202936f88337af1490b1839f339dc113b0b35f2d8c777b0  crates/yu-syntax/src/expression/lambda.rs
81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669  crates/yu-syntax/src/expression/operator_chain.rs
9dc7455b0e97e3d57194126d33d330bd85aaba123d43015894728598d6337714  crates/yu-syntax/src/expression/required_operand.rs
de8da369638545727b83fffaadbd487209275f8af9a5c00beb48d1695fbcf5ba  crates/yu-syntax/src/expression/tails/inline_slot.rs
a3ee107c996e028765570c7ba89b12857cd072eddc988b5b4c8eb66ffc753b8c  crates/yu-syntax/src/expression/tails/mod.rs
e65c4d500ce0878faf13f1a8d31da816e5db9b6af4690b505c8875d27b700f95  crates/yu-syntax/src/expression/delimited.rs
0a1dcbd84874f6abd571e0ce7035b9ba7682ebdf7c2348c030a1ba77deabcd25  crates/yu-syntax/src/lexical/item.rs
97c69c86888784ee4b3eb04d8e4685f6370dbf451631c83ec1838fe7abfc36e1  crates/yu-syntax/src/lexical/lexer.rs
887f1499fe63d870a70777626f0357c502a356d106c623d9a79e3596a17aba19  crates/yu-syntax/src/lexical/trivia.rs
41efcce2b737a0362484e854a8549bda5f7bf0d2b911499553f1e449c6782a84  crates/yu-syntax/src/lexical/current_item.rs
c981a994a11c539256ef34382c4ae154395e5d438371db4959e914df58aa8c7c  crates/yu-syntax/src/lexical/expression_item.rs
0ca1b4acb27904c28e62b950ae04ee114d992cdffa27accf6098793e73cbb766  crates/yu-syntax/src/lexical/position.rs
730e65947f889ef07014aa003eb846012d5cec6ae1434f77edf1cbd0e7096641  crates/yu-syntax/src/lexical/observation.rs
edcf37bbe061c0966ba786d9090361c6c3befdbe3f99aa79f29271bd5230bf5b  crates/yu-syntax/src/lexical/stops.rs
145002d4254aaf186fa5176d0c6c56d89c88235e29e2da9ab1d33790a31ca3a2  crates/yu-syntax/src/lexical/operator_scan.rs
21738dda1f64d27273983246f0f5d22b0a6da0025209132238a91154c38fcf75  crates/yu-syntax/src/lexical/yumark.rs
8ca2c50ae263986423eaf0f43e1a94de9fdf432366698118d6de75feb854d762  crates/yu-syntax/src/handoff.rs
26d2a0ddbe1862c95c503420ded0b0d35217bee5ba9f350be9163c065c6b488d  crates/yu-syntax/src/syntax_kind.rs
fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797  crates/yu-syntax/src/statement.rs
c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626  crates/yu-syntax/src/root_statement.rs
18709b87b1b761374b5b81f90fcbf37d001fd7d981597e889aef05ad3f230f93  crates/yu-syntax/src/lib.rs
cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad  crates/yu-syntax/src/header.rs
24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8  crates/yu-syntax/src/full_parse.rs
f1a5bd012f064d414d476acbc326c6a9804dc8128bf2e4f1800acb718a7d423b  crates/yu-syntax/src/operator_compilation.rs
369ce0a3a8f5ac39da9da572cfe4fab6f61dd4ca07c554848cfcc44aa7051643  crates/yu-syntax/src/operator_table.rs
021e79529445054e5d54bfccf93d2287e94221a99e1554fbd7c715cb0706edbd  crates/yu-syntax/src/declaration/operator_header.rs
509af68c34e11a2a2d5538df8bab84c599d68154a3f03d57c304bbfb04d8cd39  crates/yu-syntax/src/expression/if_expr.rs
550c70f27b9d96adeede70e33ca546e003747764a660cee1cd7c99a52b5a3a35  crates/yu-syntax/src/expression/case_like.rs
fd50ab8b049addc3c366a0eda5519fd38bda31a2b518ba139d90ad24949714ec  crates/yu-syntax/src/expression/for_decl.rs
8d5229ac9778d1bd5d84c739b2eeff582bb2807ab794c63aa49555ba28c62026  crates/yu-syntax/src/expression/tails/assignment.rs
df37d747f396e8b27c53b6785e4a26f5210162b14e65b4648d449495bf8f5982  crates/yu-syntax/src/expression/tails/colon.rs
4fdf57e9a19b8897871d666ab5ec8adaa7c9219fc775d6c54cddc4555f61c058  crates/yu-syntax/src/expression/tails/with_body.rs
9e88d7ce18d8bd2d3c3bfa6fbdd6cac7e37032a21fedc35774c71597ff7a21bd  crates/yu-syntax/src/expression/tails/fixed_access.rs
349fe2335e04a68da7d07803f2dd2eb185887d07bf8c9475ba09af089a76a2cf  crates/yu-syntax/src/expression/tails/delimited_tail.rs
edf609d719ffb7698b565e41cd6b76a0eae489703f017e70efd90f290e4c9c4a  crates/yu-syntax/src/expression/tails/type_annotation.rs
2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f  crates/yu-syntax/src/type_expr/mod.rs
1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883  crates/yu-syntax/src/pattern/mod.rs
eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544  crates/yu-syntax/src/declaration/binding.rs
```
