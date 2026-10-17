# Choice A: exact Call CST and source-key constructor audit

Status: frozen candidate source-correspondence proof; fresh independent review pending.
Assignment: `choice-a-call-cst-source-key-audit`, revision 1.
Author/actual worker: `/root/astra_accepted_call_hir_projection`; session `current-session`.
Requested model/effort: gpt-6-astra / medium. Observed: UNKNOWN / UNKNOWN.
Contract: `ordinary-hir-choice-a-contract-20261017`, revision 4,
SHA-256 `88f9674294f001e33bc9c29803d329f2d76c1059c21bbd9362c35ab1d84d7f93`.
Source baseline supplied by Luna: `0c0fda3974d1db2c91256667f93c46effa18c8d0`.
Final contract checkpoint supplied by Luna: `1a7560e9de6d4df8e037cdd8cf9e04254f4f7576`.
No Git inspection was performed. All 48 direct dependency pins matched at freeze.

## Result and parent application

The pinned constructors derive the three binding headers/bodies, the two unary
ML expression applications, their trivia placement and distinct source keys for
this exact input. The prior explicit CST-shape premise HIR-APP-CST-1 is therefore
discharged **within this candidate audit**, subject to independent review and
Luna's adjudication. This is no longer a theorem conditional on callers having
supplied the desired already-classified Items. It is a finite branch audit from
the fixed ASCII bytes through the public scan/parse route.

The derivation uses the normal contracts of Rust, the parser combinators
(transactional token alternatives), Rowan node construction and ASCII character
classification; it is not a verification of those libraries. It introduces no
new external dependency. It proves neither parser correctness for arbitrary
source nor an execution result. All coordinates below are arithmetic derivations
from the literal and constructor emission order, **not observed tree dumps**.
No numeric source-key payload, green allocation address or HIR occurrence ordinal
is fabricated.

Apply this result to the frozen accepted-call projection artifact: its two
application-body shapes can now be instantiated from the source constructors.
`direct_atom` rejects both chains, so ordinary `lower_simple_chain` and opt-in
`SimpleBodyProjection::Unsupported -> lower_body` still produce the application
UnsupportedExpression errors identified there. Thus the original failed
zero-HIR-error gate remains blocked by HIR-APP-ADMISSION-1, not by an assumed
association shape. Direction A permits drafting/review only; error removal or
production code is not authorized here.

The original A/B, F1/FK1, N-Transport, complete Call, soundness, principality,
termination and source/native parent quantifiers remain OPEN and unchanged.
Original theorem conditions closed: zero. Constraint generation, accumulation,
propagation, levels, extrusion, qualifying intrusion and generalization remain
untouched. No provider/residual/witness lineage is identified with another.

## 1. Input, lexical decisions and the actual operator table

```text
my id x = x; my apply f = f 1; my answer = apply id
```

51 ASCII/UTF-8 bytes; SHA-256
`bdf41b8059d37dea354a6b6e45a4e0a9f5a0dc412bcee40efb44a0a8bff10ba1`.
Use the same public route as the frozen prior evidence: `scan_header` over the
shared source allocation, then `parse_file` with `SyntaxEnvironment::empty()`.
The source/header allocation assertion is an explicit entry precondition;
this audit does not invent a mismatched header or a foreign syntax environment.

The following owner chain establishes the actual table, rather than assuming
that an empty imported environment implies an empty effective environment:

1. `yu-syntax/src/lib.rs:347` calls `header::discover_header`.
   `cursor.rs::discover_header` supplies an empty table for discovery.
   `header.rs:43` starts with empty imports/facts and gets its first Item through
   `use_decl.rs:1529::next_use_item_lex` and `scan_use_payload` at 1562.
   Its version alternative requires initial `v` plus a digit (1588), so fails on
   `my`; `lexer.rs:710::scan_identifier` returns the exact word `my`.
2. `use_decl.rs:217::use_declaration_selected_lexical` sees visibility `my`,
   observes the ordinary gap and head `id`, and its prefix helper rejects
   `head != "use"` at 249. The binding selector in `binding.rs:35` first rejects
   use/mod/struct/type alternatives, then `binding_follower_normalized` (83)
   sees `id` and selects the default binding case.
3. `header.rs:157::operator_selected` explicitly returns false for `my` when
   that binding selector succeeds. `discover_header_with_cursor` therefore
   takes FirstNonHeader at the first word (95), with empty operator facts.
   It does not search later binding bodies for operator declarations.
4. `syntax_environment.rs:20` supplies an empty imported OperatorTable.
   `full_parse.rs:317::parse_file` calls
   `operator_compilation.rs:49::effective_full_parse_operators` with those two
   empty inputs. Both merge loops have zero iterations; the default builder's
   definitions map is empty (`operator_table.rs:544`), and `build` (585) returns
   an empty table. `parse_file` passes that exact table into `cursor::parse_root`
   and retains it in the parse product. This also instantiates the existing
   authoritative exact-environment contract; no second environment is inferred.

With that table, both ordinary and dangling dynamic-operator scans have no
matching terminal (`operator_scan.rs:30,99`; `operator_table.rs` longest-source
match). No word here can become a dynamic operator. String opener selection
requires a quote run (`literal/mod.rs:88`), and rule-literal selection requires
`~"` (`literal/rule_literal.rs:37`); neither occurs.

`current_item.rs:44,63` handles the unfenced route: scan ordinary trivia,
assemble Item::plain, and emit EOF only on empty remainder. Horizontal spaces
are scanned by `lexer.rs:441,451`; they set ordinary leading presence and do not
create a newline or fence. `trivia.rs:83,250` gives the same unfenced lookahead
observation to selectors. At statement entry `scan_statement_keyword` (736)
recognizes `my` before dynamic operators, still as Identifier; `binding.rs:553`
later emits it as MyKw. The other words are maximal identifiers through
`scan_identifier`/`source_identifier` (710/749): ASCII letters continue, spaces
and semicolons stop, and no `?` or `!` suffix is present. `scan_integer` (916)
recognizes exactly `1`. Pattern scanning uses `scan_pattern_tail_token` (374),
whose exact-equals scanner (1085) accepts each `=` followed by a space.
`scan_punctuation` (933) returns Semicolon for both separators.

The expression literal wrapper (`expression_item.rs:74,97`) reaches the ordinary
payload scanner on these inputs. `scan_expression_payload` (`lexer.rs:89`)
reaches identifiers/integers/punctuation after the absent special/operator
alternatives. `observation.rs:13,21` and `stops.rs:59` make Semicolon an active
stop under STOP_SEMICOLON. No lexical retry or unknown-token branch is needed.

## 2. Root selection and canonical binding construction

`cursor.rs:85` opens Root. `root_statement.rs:30,106` starts at physical origin
0 with no fence; the first word is admitted at physical start. It emits each
semicolon directly under Root (153), permits the next statement, and emits the
next head's leading space before entering its statement (180). No wrapper
expression or extra statement node is inserted by this root path.

For each of `my id`, `my apply`, `my answer`, the complete negative-selector
check is the same finite branch, using the different post-my identifier:

| Selector owner | Entry/helper lines | Why it rejects |
| --- | --- | --- |
| declaration/use_decl.rs | 217 / 232 | following word is not use |
| declaration/mod_decl.rs | 39 / 55 | not mod |
| declaration/struct_decl.rs | 68 / 84 | not struct |
| declaration/type_decl.rs | 47 / 63 | not type |
| declaration/enum_decl.rs | 152 / 174 | not enum; later head checks unentered |
| declaration/error_decl.rs | 152 / 174 | not error; later head checks unentered |
| declaration/role_decl.rs | 154 / 170 | not role |
| declaration/impl_decl.rs | 133 / 149 | not impl |
| declaration/cast_decl.rs | 168 / 184 | not cast |
| declaration/act_decl.rs | 159 / 181 | not act; later head checks unentered |
| expression/for_decl.rs | 40 | current word my is not for |

These local `item_word` helpers check Identifier kind and exact spelling; the
reexports are explicit in `declaration/mod.rs`. Their reached prefix helpers
use the pinned ordinary-trivia observation and `source_identifier`. No
uninspected declaration-body behavior is assumed. Consequently
`statement.rs:423::classify_statement_item_lexical` selects Binding and its
canonical dispatcher calls `binding_statement_normalized` (binding.rs:185).

That constructor opens BindingStatement then BindingHeader, emits MyKw, and
calls the target parser with equals/semicolon/comma stops (`binding.rs:259`).
The target's leading space is emitted in Header before Pattern starts.
`pattern/mod.rs:338` opens Pattern; its identifier primary (around 766) opens
IdentifierPattern. For `id x` and `apply f`, the ordinary gap plus a valid
identifier and precedence Lowest satisfies the ML-pattern-tail branch at 1195.
It emits the gap before opening PatternMlApplicationTail, then opens the nested
Pattern at precedence MlApplication. The following equals is a pattern stop
(1535,1550), so exactly one parameter tail is produced. `answer` has none.
These two **pattern** tails are not expression MlArgument nodes.

`binding.rs:237` emits the equals and its leading gap while Header remains
open, closes Header, then opens BindingBody (241). The source is one line, so
`binding_body_normalized` takes its inline branch. At 393 the body head's gap
is emitted in Body before `expr_from_nud_normalized` opens OperatorChain.

## 3. Exact expression shape, association and ranges

Expression construction is at `operator_chain.rs:109,143`: the identifier or
integer branch calls the canonical core emitter (`cursor/recovery/emit.rs:205,
215`), yielding IdentifierExpression/IntegerLiteral and a single exact token.
For the two body gaps, `is_ml_argument` (761) sees a valid NUD, nonempty ordinary
leading and no newline. `ml_argument` (785) emits the gap in the outer chain,
opens MlArgument, and parses its child OperatorChain with `MlMode::None`.
Semicolon or EOF then ends the argument and the enclosing body. `x` has no tail.

Constructor-derived tree, omitting tokens/trivia from the display only:

```text
Root
  BindingStatement
    BindingHeader: Pattern(IdentifierPattern(id),
      PatternMlApplicationTail(Pattern(IdentifierPattern(x))))
    BindingBody: OperatorChain(IdentifierExpression(x))
  BindingStatement
    BindingHeader: Pattern(IdentifierPattern(apply),
      PatternMlApplicationTail(Pattern(IdentifierPattern(f))))
    BindingBody: OperatorChain(IdentifierExpression(f),
      MlArgument(OperatorChain(IntegerLiteral(1))))
  BindingStatement
    BindingHeader: Pattern(IdentifierPattern(answer))
    BindingBody: OperatorChain(IdentifierExpression(apply),
      MlArgument(OperatorChain(IdentifierExpression(id))))
```

Half-open ranges are derived by summing the exact emitted byte strings. These
are constructor arithmetic, not runtime measurements or serialized key values:

| Node | id binding | apply binding | answer binding |
| --- | --- | --- | --- |
| BindingStatement | 0..11 | 13..29 | 31..51 |
| BindingHeader | 0..9 | 13..25 | 31..42 |
| target Pattern | 3..7 | 16..23 | 34..40 |
| target IdentifierPattern | 3..5 | 16..21 | 34..40 |
| parameter tail / nested Pattern / IdentifierPattern | 6..7 | 22..23 | absent |
| BindingBody | 9..11 | 25..29 | 42..51 |
| body OperatorChain | 10..11 | 26..29 | 43..51 |
| body head IdentifierExpression | 10..11 | 26..27 | 43..48 |
| MlArgument / child OperatorChain / argument leaf | absent | 28..29 | 49..51 |

Root owns semicolons 11..12 and 29..30 and spaces 12..13 and 30..31.
The two application chains own their separating spaces 27..28 and 48..49;
these are outside MlArgument. Header owns spaces before target and equals;
Pattern owns the gap before its parameter tail. Body owns the gap after equals.
There is no trailing trivia at EOF. Thus node range equality between a tail,
its nested chain and its leaf is expected and cannot be used as identity.

The authoritative HIR associator (`yu-hir/src/lib.rs:295` expression loop,
`structural_continuation` at 473 and nested collection at 520) inserts the old
left as child 0, then the associated nested child. It yields exactly
`V(x)`, `M(V(f),V(1))`, `M(V(apply),V(id))`, with application ranges 26..29 and
43..51. The source contains two unary applications and no nested application
body. It contains nested *chains* inside their MlArgument tails.

For adjacent ML tails the parser's argument MlMode::None returns the next gap
to the outer continuation; induction over that continuation plus HIR's left
insertion gives `(f x) y`. Parenthesized source would use
`delimited.rs:44` ParenthesizedExpression and a separate inner chain; this
literal contains no parentheses, CallTail or Group. This structural explanation
does not enlarge the packet to prove arbitrary grouping/recovery grammar or
ordinary HIR support for all such forms.

## 4. Symbolic keys, branding and retained source operands

For a parse P and reached node n define the actual key expression
`K_P(n) = (P.parse_identity, n.green(), n.text_range().start())`.
This denotes the private values created by `full_parse.rs:113::SourceNode::key`,
not an invented public tuple API. Equality at 86 requires pointer equality of
both retained Arc parse brand and green allocation plus equal start. Root and
child walks (120,130) alone mint parse-owned keys. Fresh parse_file calls mint
fresh brands; clones preserve the brand. UNTRACKED revision is not this identity.

Let B1/B2/B3 be the three binding nodes, P_x/P_f their formal IdentifierPatterns,
C_f/C_apply the two callee IdentifierExpressions, T_1/T_id the MlArgument nodes,
and A_1/A_id their argument leaves. The exact source owner mappings are:

| Retained entity | Source key | Lexical fact |
| --- | --- | --- |
| definition roots id/apply/answer | K(B1), K(B2), K(B3) | three unique module names |
| parameters x/f | K(P_x), K(P_f) | parameter 0 of its own definition root |
| id body name | K(body x IdentifierExpression) | same x parameter identity |
| first carrier Apply | K(T_1) | callee K(C_f), argument K(A_1) |
| second carrier Apply | K(T_id) | callee K(C_apply), argument K(A_id) |

Callee versus argument starts differ (26 versus 28; 43 versus 49), so their keys
cannot compare equal even if a green allocation were shared. Tail, inner chain
and leaf at start 28 (or 49) have different node kinds/structure; one immutable
green object cannot have those different kinds, so their keys are distinct
despite equal ranges. `id` declaration and argument also differ in kind/start.
No conclusion assumes all same-range nodes universally have distinct keys:
zero-width repeated green nodes can be ambiguous, as the source-key owner's
explicit regression describes. This literal creates no zero-width node.

`yu-hir/src/source_identity.rs:26,36` walks the parse-owned SourceNodes and
retains these keys. Its definition/parameter/occurrence recording methods keep
the maps distinct. `module.rs::plan_root`, `namespace`, `lower_plan` and
`lower_leaf` supply the root IDs, per-root parameter 0, parameter-before-module
resolution, and completed module namespace. Thus f at 26..27 is apply's formal;
apply at 43..48 and id at 49..51 are their unique module definitions.

`local_source.rs::form` reuses those roots/parameters and installs their lexical
bindings. `Builder::expression` at 851 builds each Apply with separate callee
and argument slots, recording the tail key with `Builder::set` at 815. It fills
the names using Parameter or ModuleDef resolution at 1004. Reverse tail planning
allocates the outer node first but threads the callee slots to preserve left
association; allocation order is not evaluation order. Ordinary formation
subsequently orders published occurrences by source owner descent
(`order_occurrences`, 101) after existing ordinary allocations. Opt-in source
formation's earlier occurrence allocation must not replace that ordinary policy.

HIR occurrence identity is separately `(artifact brand, ordinal)`
(`module.rs:177`, `next_occurrence` at 1222); parameter identity includes its
branded root and ordinal. Different source entities can have equal text while
retaining distinct HIR occurrences. Source keys and HIR occurrences are not
interchangeable IDs. `shadow.rs::occurrence_source_position` checks foreign HIR
artifact, then the parse brand, then missing/ambiguous source positions; its
mapping is not a range search that merges coincident nodes.

## 5. Recovery, limits and exact remaining gates

On this finite path no constructor reaches a Missing, Error, Invalid or retry
branch: each required header/body/argument is supplied, equals and semicolons
reach their own stop owners, and EOF occurs after the final identifier.
This is a source audit prediction consistent with the earlier no-structural-
recovery receipt; no fresh parser execution or diagnostic dump was produced.
For malformed/recovered inputs the existing recovery interpreter remains the
owner; this audit proves no arbitrary recovery theorem and no zero-width-key
uniqueness. Parenthesized groups, commas, comments, Unicode, multiline/fenced
source and operator-bearing programs are outside this packet's raw-byte audit.

The input has three roots, two one-parameter headers and two unary expression
applications. It needs no unbounded recursion argument. The prior inspected HIR
parameter/shadow-depth and raw-shadow limits remain exactly their own limits;
they are not promoted into a universal ordinary-parser bound. Allocation or
identity exhaustion remains possible failure, not a partial successful parse/HIR
publication claim. No resource/termination parent theorem is closed.

Candidate conclusion: the source fact requested by HIR-APP-CST-1 now has a
constructor derivation, including the actual empty effective operator table.
No remaining source-shape antecedent is identified within this fixed literal
and the normal library contracts stated above. Fresh review remains required.
The next missing clause is unchanged HIR-APP-ADMISSION-1: Luna's successor
contract must decide general supported applications, ordinary representation,
error ownership, identities, consumers and bounds; user adoption is required
before implementation. `hir.errors().is_empty()` still fails under the inspected
current projection. No new constraint-generation/propagation/native-consumer
execution evidence exists, and no Call typing, source T, SV-CONSUMER-1, effects,
F1/FK1 or production authority follows from these syntax facts.

Mutual TODO CST-REVIEW-1: independent reviewer checks the raw-byte branch chain,
range arithmetic, key inequalities and prior-artifact application. Falsifier:
one competing selector captures a root, header facts are nonempty, a different
expression form is emitted, or any listed ownership/key equality contradicts
its constructor. Owner: Luna-appointed fresh reviewer, not this author.
Mutual TODO HIR-APP-ADMISSION-1: Luna consumes the candidate source fact in the
already-granted direction-A draft. Future implementation falsifier remains the
fixed source's UnsupportedExpression errors or incorrect operand identities;
this TODO grants no code/test lease and does not license ignoring the HIR gate.

## Checks, provenance and stopped writer

Reused: the frozen prior projection and its exact no-recovery/nonempty-HIR
failure boundary, plus the scoped association/ownership authorities. Rejected:
empty imported environment alone as effective-table evidence; already-classified
Items as raw-source evidence; node ranges as identities; carrier formation as
ordinary admission; local syntax facts as independent foreign-continuation proofs.
No historical proof is promoted outside its premises.

Six substantive stages: entry/pin reconciliation; constructor/key audit;
lexical and table audit; complete negative root-selector audit; application to
HIR-APP-CST-1 and prior error gate; freeze. Revisions 2–4 were Luna-granted
dependency amendments; outputs and 480s cap never expanded. Waiting was reported
as WAITING and did not mint research evidence. Start clock receipt was
2026-10-17 08:24:04 UTC; rev4 resume receipt 08:31:43 UTC. Exact active CPU/time
was not measured. Conservative final charge is the full 480s reservation,
remaining 0; unused reservation retired. Prior charges 120+30+60=210s are
included, not added again. Requested/observed model metadata remains as above.

Only static owner reads and SHA-256 checks were performed. No tests, compiler
probes, builds, Cargo, Git, external contact, source edits, descendants or scratch
files. All 48 direct pins and the rev4 contract hash matched before writing.
The two exact leased outputs are this file and
`tasks/agent-loop/inbox/20261017-choice-a-call-cst-source-key-audit.md`.
After the frozen handoff and hash receipt, this author stops all writes and
performs no waiting-stage work. Three inherited UNKNOWN reservations remain
untouched. Candidate acceptance and integration belong to Luna after independent
review; this producer does not certify its own result.

## Frozen direct dependency manifest

- `notes/theory/2026-10-17-accepted-call-hir-projection.md` — `0c1a29f3d590f68064e980459a4373400702034a2366591dae32fe7b1572e25f`
- `notes/design/2026-10-17-accepted-call-hir-admission-contract.md` — `2f3b6dbb6e735b3c5da96f0bbdaa8357f7580435999e08136ce24e1bf19174ab`
- `crates/yu-syntax/src/declaration/binding.rs` — `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544`
- `crates/yu-syntax/src/pattern/mod.rs` — `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883`
- `crates/yu-syntax/src/expression/operator_chain.rs` — `81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669`
- `crates/yu-syntax/src/expression/tails/mod.rs` — `a3ee107c996e028765570c7ba89b12857cd072eddc988b5b4c8eb66ffc753b8c`
- `crates/yu-syntax/src/expression/delimited.rs` — `e65c4d500ce0878faf13f1a8d31da816e5db9b6af4690b505c8875d27b700f95`
- `crates/yu-syntax/src/full_parse.rs` — `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`
- `crates/yu-syntax/src/cursor.rs` — `f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142`
- `crates/yu-syntax/src/root_statement.rs` — `c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626`
- `crates/yu-syntax/src/statement.rs` — `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797`
- `crates/yu-syntax/src/cursor/recovery/emit.rs` — `de091c117486f7990dc6872bf2ee7659c0e3e7e148e255f47b56b7836fe7c59d`
- `crates/yu-syntax/src/lexical/item.rs` — `0a1dcbd84874f6abd571e0ce7035b9ba7682ebdf7c2348c030a1ba77deabcd25`
- `crates/yu-syntax/src/lexical/current_item.rs` — `41efcce2b737a0362484e854a8549bda5f7bf0d2b911499553f1e449c6782a84`
- `crates/yu-syntax/src/lexical/lexer.rs` — `97c69c86888784ee4b3eb04d8e4685f6370dbf451631c83ec1838fe7abfc36e1`
- `crates/yu-syntax/src/lexical/expression_item.rs` — `c981a994a11c539256ef34382c4ae154395e5d438371db4959e914df58aa8c7c`
- `crates/yu-syntax/src/lexical/trivia.rs` — `887f1499fe63d870a70777626f0357c502a356d106c623d9a79e3596a17aba19`
- `crates/yu-syntax/src/lexical/observation.rs` — `730e65947f889ef07014aa003eb846012d5cec6ae1434f77edf1cbd0e7096641`
- `crates/yu-syntax/src/lexical/stops.rs` — `edcf37bbe061c0966ba786d9090361c6c3befdbe3f99aa79f29271bd5230bf5b`
- `crates/yu-syntax/src/literal/mod.rs` — `d54b4ef01cb3c9d46048b5638f9837eb050816a5e7edd35460f20cf1e557fd40`
- `crates/yu-syntax/src/literal/rule_literal.rs` — `d21f7e27eb89dfa3c6717b895726e827974728be962faefcb08c9ce9092753ee`
- `crates/yu-syntax/src/lexical/operator_scan.rs` — `145002d4254aaf186fa5176d0c6c56d89c88235e29e2da9ab1d33790a31ca3a2`
- `crates/yu-syntax/src/operator_compilation.rs` — `f1a5bd012f064d414d476acbc326c6a9804dc8128bf2e4f1800acb718a7d423b`
- `crates/yu-syntax/src/syntax_environment.rs` — `3f1e2c97c49318e02c595aa739bfb48532f7631d38afaaac4d8dfca6142cb973`
- `crates/yu-syntax/src/operator_table.rs` — `369ce0a3a8f5ac39da9da572cfe4fab6f61dd4ca07c554848cfcc44aa7051643`
- `crates/yu-syntax/src/lib.rs` — `18709b87b1b761374b5b81f90fcbf37d001fd7d981597e889aef05ad3f230f93`
- `crates/yu-syntax/src/header.rs` — `cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad`
- `crates/yu-syntax/src/declaration/operator_header.rs` — `021e79529445054e5d54bfccf93d2287e94221a99e1554fbd7c715cb0706edbd`
- `crates/yu-syntax/src/declaration/mod.rs` — `cf1067280be3974a5702b18f47ac02cf824c9d8cf971c1bdbc1b143676fc5c71`
- `crates/yu-syntax/src/declaration/use_decl.rs` — `8a0143f4c7bb187211076f725e5116424b499c3d9c0929d9681e978e3ab83cb6`
- `crates/yu-syntax/src/declaration/mod_decl.rs` — `6adf9945e096ee027886a05857f6c187134a5331e4ab37493d95304255760741`
- `crates/yu-syntax/src/declaration/struct_decl.rs` — `7b36b18fc6ef3e149e756a37b0f74719a5ae40be195c6986efe2c44d57fa3de4`
- `crates/yu-syntax/src/declaration/type_decl.rs` — `e01d1f30c1dca051fb590a9fddac1686621fc789444f9cb053dcc269e746c134`
- `crates/yu-syntax/src/declaration/enum_decl.rs` — `9c717571426927a3619330b372ec721d1f660377ecd45c6f0ab7f6cf9ed3ec31`
- `crates/yu-syntax/src/declaration/error_decl.rs` — `56eace59a91d156f59d27a348e98ea353e9cc96595a49fc0f7e58d36dcd7a028`
- `crates/yu-syntax/src/declaration/role_decl.rs` — `0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634`
- `crates/yu-syntax/src/declaration/impl_decl.rs` — `026edcb3e6d3c9f2214be8b9fa9fd510378b64152de55673c18cb93373f62066`
- `crates/yu-syntax/src/declaration/cast_decl.rs` — `c4907b91f0cbe72606597fb6ef1918c757e9f78621a2c4c68bf0632fe629a0ed`
- `crates/yu-syntax/src/declaration/act_decl.rs` — `f1af95a12df81900564c83d0aad541064eb2fff21ca41259b7a943ae3ad4fd74`
- `crates/yu-syntax/src/expression/for_decl.rs` — `fd50ab8b049addc3c366a0eda5519fd38bda31a2b518ba139d90ad24949714ec`
- `crates/yu-hir/src/lib.rs` — `5bdcb7c0df022da919cef5402c62dc1c7baf0700a4d06e526a608cbd7db21464`
- `crates/yu-hir/src/module.rs` — `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`
- `crates/yu-hir/src/module/local_source.rs` — `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`
- `crates/yu-hir/src/source_identity.rs` — `aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2`
- `crates/yu-hir/src/shadow.rs` — `2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9`
- `crates/yu-solver/src/lib.rs` — `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`
- `crates/yu-solver/src/shadow_apply.rs` — `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`
- `crates/yu-solver/src/shadow_candidate_source_crosswalk.rs` — `392d665579a74810134846e1274c0c9ce975a7eb0e2cfb9ad79a07af2cd2eeb0`
