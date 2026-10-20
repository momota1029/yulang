# R147 braced-if source audit and conditional singleton representation

Status: **conditional candidate and read-only source evidence; pending independent review**.
Author: `/root/r147_proof`; no coauthors or descendants.
Contract rev2 SHA-256: `87ec019b57a2e885bff6aab5e7cf16929526ebb07df593646f495442184ff281`.
Baseline commit: `4d9c9c74e0c56b8e34b60d521b68bcf8504946b2`.
Baseline complete tree: `e2baa5de4a9796b56fa1a2c85e581346bd54886f`.
Requested routing: prover default Sol/high; observed effective model/effort: UNKNOWN.

## Parent application and boundary

The original product objective remains proof-backed inference and evaluation of a broad
unchanged Yulang2 sample domain. This packet supplies the source distinctions needed
for a user decision about braced `if` arms. It grants no Yulang3 syntax or semantic
approval, implementation, sample execution, reviewed theorem, source/native
correspondence, or parent A/B closure. R64/R65 and all original Simple-sub/evaluator
parent claims and quantifiers remain OPEN. Their proofs are not dependencies silently
discharged by the local representation argument below. R146 supervisor conformance
remains UNVERIFIED; no R146 observation is reused as evidence here.

The pinned 388-byte `web/playground/examples/yulang2-ordinary-islands.yu` includes
`my countdown flag = if flag { 8 } else { countdown true }`, then exports
`countdown_result = countdown false`. Its desired selected result is `8` (tool text
`8\n`), conditional on the still-open parser, HIR, inference, recursive binding,
runtime schedule and Web integration premises. No execution took place in R147.

## Yulang2: parser, classifier and constructor are separate owners

All Y2 paths below are relative to `../yulang2-oracle-capture/`.

1. `crates/parser/src/expr/control.rs:425-481` stops the condition at colon or
   left brace. A brace arm calls `delimited(BraceGroup, BraceR, ...)` directly
   (471-473). Else has its own OpenBrace branch (484-518, especially 508-510).
   These are expression-list arm groups, not the ordinary statement-block
   entrypoint. `expr/group.rs:13-27,48-118` enables spread for BraceGroup,
   parses ordinary items with `parse_expr`, wraps spread items as ExprSpread,
   and recognizes comma and semicolon as group separators. This inspection
   does not establish every textual/malformed/newline case of the unlisted
   common list-machine owner. In particular, lowering's acceptance of a
   direct Binding child does not prove that this expression-list parser emits it.
2. `crates/infer/src/lowering/control.rs:14-70,120-124` sends each selected arm
   node through ordinary `lower_expr` with local restoration. `expr/chain.rs:593-596`
   first tests `brace_group_is_record_literal`; true calls `lower_record_literal`,
   false calls `lower_expr_block`. It does not fall back to a block after record
   construction returns an error.
3. `expr_syntax.rs:115-149` examines direct child nodes. Each Expr must have a
   name and a value and only ApplyColon child nodes. Name lookup rejects PathSep
   (151-169). Each ExprSpread must contain some direct Expr child. Separator is
   allowed, another node kind rejects. Predicate return is `has_item || !saw_child`.
   Therefore an empty child sequence is record-routed, but a nonempty sequence of
   only Separator children is not. This is a CST predicate, not proof that either
   sequence comes from a specific source spelling without diagnostics.
4. `record_lit.rs:55-147,151-169` validates and lowers items after routing. A
   second spread returns UnsupportedSyntax::ExprSpread (72-79), despite the
   predicate permitting multiple valid ExprSpread children. Field child lowering
   can also fail. One spread's placement before any lowered field chooses Head;
   otherwise it chooses Tail. Effects of every lowered field and spread flow to
   result_effect (102-107), and spread expansiveness participates in computation
   classification (84-93). The returned Expr::Record retains RecordSpread::Head
   or Tail. This is construction evidence, not verified runtime record behavior.
5. For non-record routing, `expr_syntax.rs:171-179` keeps only direct Binding,
   Expr and ForStmt children. Direct ExprSpread children are **omitted**; even
   their nested expression is not passed to block lowering by this filter.
   `expr/block_local.rs:69-158` then sequences the retained items. No retained
   items gives unit; a final ordinary Expr returns its lowered computation;
   earlier ordinary expressions become Stmt::Expr. `prepend_block:1284-1306`
   retains their effects and the tail value. Local binding/ForStmt cases exist
   at the lowering level but their source reachability in these braced arms
   is not established by the pinned expression-list parser.

The resulting distinction is shape dependent:

| Direct BraceGroup child shape, ignoring separator nodes where appropriate | Predicate / next owner | Construction consequence under explicit well-formed-child premises |
| --- | --- | --- |
| no child nodes | record / lower_record_literal | zero-field record construction, not unit block |
| only inline field Expr children | record | lower all fields; child failure still possible |
| only valid spread children, or fields plus spreads | record | zero or one spread can construct; second spread errors; include spread effects |
| one ordinary nonfield Expr | block | return that expression's computation |
| multiple ordinary nonfield Expr children | block | sequence retained expressions; return last value |
| field Expr plus a nonfield Expr | block | all retained Expr children are ordinary expression lowering, not record field construction |
| ordinary nonfield Expr plus valid ExprSpread | block | retain ordinary Expr; omit direct spread and its child computation |
| Separator children only | block | retained list empty, unit; source reachability unestablished |
| malformed spread/other child shapes | predicate may be false | filter/child errors depend on actual CST and diagnostic gate; no successful-source claim |

For example `{ ..r, ..s }` can satisfy the *predicate* when both spreads have
Expr children and still fail record construction. `{ e, ..r }` with a nonfield `e`
is block-routed and the direct spread is omitted. These examples describe
conditional CST shapes; no parser or runtime observation was made. A blanket
“braces mean block” rule would change empty/field/spread cases. A blanket “reject
all spreads” rule would restrict Y2's one-spread record case. A blanket “lower all
items” rule would change Y2's mixed non-record spread omission. Each choice needs
an explicit user decision rather than an unnoticed generalization from countdown.

## Yulang3: exact current arm boundary and retained consumers

The pinned syntax reference defines colon-introduced if/elsif arms and colon or
bare OperatorChain else arms; it explicitly leaves brace-arm bodies and semantics
outside its scope. The pinned architecture's if addendum (5473-5504) defers brace
arms; its braced-primary separation (6145-6173) distinguishes ordinary statement
blocks from the old expression-list owner. These historical prose sections do not
authorize R147 to extend the grammar.

`crates/yu-syntax/src/expression/if_expr.rs:187-258` stops the condition at
LBrace as well as colon/arm companions (203). Only colon takes the body-construction
branch (232-246). A retained condition followed by brace uses
`missing_if_arm_normalized:310-342`, emitting Missing and returning the item.

Bare else is also **not** a generic brace-primary success. At 346-405, an else
without colon sends its current item to `inline_body_item_normalized`. That
function checks `inline_boundary` before `is_nud_item` (495-506).
`inline_boundary_lex:597-603` explicitly treats LBrace as a boundary. The path
emits a zero-width Missing via `emit_inline_missing` and `emit_if_missing:611-624`
and hands the brace outward. Thus the arm itself does not construct a braced block
child. Later outer recovery or brace ownership is outside the pinned manifest;
this note makes no claim about a complete recovered root CST or every diagnostic.
Colon then brace reaches the same inline boundary check under this owner too.

The downstream map is already visible but is not a new-source coverage proof:

| Owner | Actual retained behavior | Missing braced-arm premise |
| --- | --- | --- |
| `crates/yu-hir/src/module/local_source.rs:1327-1375` conditional | Requires IfArm direct Condition plus OperatorChain/IndentedStatementBlock body; ElseArm has one such body; allocates distinct child slots and restores lexical environment for each | Chosen new CST must be admitted and every arm item accounted for; a direct new brace kind is currently rejected |
| same file 1136,1378-1504 block | BracedStatementBlockExpression enters block builder, requiring a final OperatorChain; earlier statements must be private BindingStatement; retains Block bindings/final_expression | Empty/record/spread and multiple ordinary expression sequencing are not supplied by this builder; expression-list arms cannot be equated to it wholesale |
| `crates/yu-solver/src/candidate_source.rs:994-1002,1050-1057,1240-1272,1501-1514` | Visits if children and empty-binding block final child; condition endpoint gets Bool upper bound (slot50), condition/body effects flow to result (slot51); with else branch values constrain result, without else Unit result; block retains CandidateRelation::Group to final child | Prove source occurrence/endpoint/level/effect lineage preservation for chosen representation and its actual relation consumer; consumer implementation outside manifest remains uninspected |
| `tools/inference-playground/src/runtime/program.rs:537-557` | Maps HIR Block and If to labels/instructions | Chosen source must produce the expected HIR/labels under resource limits |
| `runtime/machine.rs:668-688,1179-1221,1936-1973` | If evaluates conditions in order, requires Boolean, evaluates only selected body, discards body value to Unit without else; empty-binding Block immediately sets Evaluate(final_expression, same environment) | General source/runtime correspondence and resource/diagnostic equivalence are not supplied by these dispatch cases |

## Conditional singleton representation argument

Fix any ordinary expression `e`, arbitrary enclosing lexical environment Gamma and
continuation K. Restrict here to a successfully parsed singleton braced arm whose
sole direct semantic item is that nonfield ordinary expression; no bindings, record
fields, spreads, do marker, missing/error children, extra sequence or hidden item.
Assume all of the following independently at their owning boundaries:

- P1 (construction): the approved parser emits the chosen arm tree, the HIR builder
  retains exactly `e` or `Block { bindings: [], final_expression: e }`, and `e`'s
  name resolution, captured environment, source identity and body occurrence are
  transported faithfully; no selection/validation step drops an item.
- P2 (inference): added Group/result variables and scope occurrences are conservative
  extensions of `e`'s value/effect constraints under projection, preserving all
  external constraints, levels, extrusion/intrusion, generalization and consumer
  lineage. An extra subtype edge alone does not prove this equivalence.
- P3 (operational): construction retains the same child code and environment and
  wrapper entry adds only silent administrative transitions, without changing
  handlers, continuation licensing, requests or values. For finite budget APIs,
  compare completed runs with sufficient respective budgets, not identical fuel.
- P4 (context): if/elsif/else ordering, Boolean condition, present-else value join,
  no-else Unit discard, enclosing evaluation schedule and recursive definition
  lookup remain unchanged. Resource and diagnostic policy is separately preserved.

Under P1-P4, the empty binding-list wrapper makes one administrative transition
from Evaluate(Block([],e), Gamma) to Evaluate(e,Gamma), carrying the same K. Child
behavior therefore supplies the same completed value and ordered observable effects
under the assumed simulation, and P2 supplies the same projected external inference
constraints. In the Y2 source, the successfully lowered singleton nonfield group is
already returned as its child computation (`block_local.rs:130-134`), subject to
its block-local state restoration. In the Y3 source, `begin_local`'s no-binding
branch supplies precisely the local administrative step just cited. These facts
motivate the argument but do not establish P1-P4 for a new Y3 syntax.

Apply to countdown: both `{ 8 }` and `{ countdown true }` have the intended
singleton nonfield shape. Conditional on P1-P4 and correct existing literal,
application, recursion and module schedule behavior, false selects the recursive
call with true, then the integer arm supplies 8. This is a conditional reduction,
not an executed sample or a theorem that inference accepts the unchanged module.
The argument does not cover empty arms, record fields, spread, multi-expression
sequencing, bindings, malformed source or general effectful continuations.

## Exact remaining premises, options and falsifiers

These are requests for a later authorized contract, not write or execution grants.

- **R147-ARM-CONSTRUCTION-1**, parser `if_nud_normalized`/`if_arm_normalized`/
  `else_arm_normalized` plus HIR `conditional`/`block`: select semantics, construct
  each accepted body, preserve colon behavior, source order and companion recovery.
  Required evidence is chosen CST-to-HIR mapping for unchanged bytes and sibling
  forms. Falsifier: an accepted body loses, duplicates or misattributes an item, or
  else brace still emits Missing; ordinary colon CST/expectations change.
- **R147-SINGLETON-CONSERVATIVITY-1**, HIR `conditional` and candidate Block/If
  constructors then actual CandidateRelation::Group consumer: establish P1/P2
  with source keys, constraints/effects and scope/level transport. The unlisted
  relation consumer needs a new pinned dependency before inspection. Falsifier:
  fresh wrapper changes an external bound, generalization, effect or licensed
  consumer lineage. R64/R65 remain OPEN and are not bypassed by this request.
- **R147-SHAPE-PARTITION-1**, Y2 expression-list and Y3 future construction owners:
  narrow option accepts singleton nonfield expression arms sufficient for countdown,
  and explicitly rejects/defers all other brace-arm shapes in the new syntax;
  this is a narrow feature boundary, not full Y2 compatibility. Falsifier: a
  deferred item is silently dropped or an allowed singleton is actually record
  routed. Broader option needs an explicit row-by-row mapping for empty records,
  fields, one Head/Tail spread including effects, second-spread error, non-record
  expression sequencing and mixed-spread omission. For mixed non-record spreads,
  choose explicit legacy omission or explicit rejection/defer; neither decision
  follows from singleton equivalence. Falsifier for exact shape compatibility:
  result/effect differs from a successfully constructed Y2 shape, or Y2's failed
  multiple-spread construction becomes accidental success. All malformed and
  binding-reachability cases need defined boundaries rather than classifier guesses.
- **R147-COUNTDOWN-PIPELINE-1**, playground `prepare`/`execute` and runtime
  program/machine: after approval and implementation, unchanged 388-byte input
  must pass parse diagnostics, HIR, ordinary candidate solve/conflict gate,
  recursive lookup and selected source schedule. Expected completed selected
  output is `8\n`. Falsifier: any admission failure, type conflict, wrong selected
  value, unavailable recursion/evidence or bounded exhaustion. A parse success or
  direct hand-built instruction does not discharge this pipeline premise.
- **R147-WEB-INTEGRATION-1**, WASM exports, browser `main.ts`/`index.html`, CLI
  identity fixture and smoke script: current UI imports/maps only the identity
  island and other examples; the ordinary-islands fixture is not imported,
  selected or invoked by current UI/smoke. `main.ts:65-76` defaults non-identity
  selection to definition main, while this fixture needs countdown_result.
  `smoke-test.mjs:48-65` and `cli_demo_identity.rs:7-31` read the separate identity
  island and call its three definitions, so their expectations cannot prove this
  sample. Later integration must explicitly load unchanged ordinary-islands and
  select/invoke countdown_result, preserving existing examples. Falsifier: the
  old identity fixture or a rewritten colon sample is executed instead, main is
  selected, or Web run is never invoked.

`tools/inference-playground/src/lib.rs:266-342` makes diagnostics nonempty a hard
prepare failure, then lowers HIR, solves the candidate and withholds output on
candidate conflicts. `execute:165-201` builds RuntimeProgram with default evidence,
selects the named definition, runs the source schedule with a step budget and emits
completed values. `main.rs:74-79` calls execute only for --run; inference reporting
alone does not exercise evaluation. `apps/yulang-wasm/src/lib.rs:3-21` forwards infer
and run to these same APIs, using scoped=false. The pinned Cargo manifests connect
WASM to yu-playground and enable HIR shadow/solver candidate features in the tool;
`web/playground/package.json` defines wasm-pack/Vite build and smoke commands.
Those static connections do not prove a built artifact, ABI success or browser run.

## Evidence manifest and checks

Only the two leased output paths were written. No scratch paths, compiler/source
changes, tests, builds, CLI/WASM/runtime execution, descendants or Git operations.
Historical R135/R146 results are leads/limitations only; no historical theorem or
observation is used to certify this candidate. All 26 direct pins and contract hash
were checked before the audit; the exact direct manifest follows. Policy/startup
files were read as instructions, not additional mathematical evidence. Full outer
recovery, common list-machine implementation, actual relation consumers and native
backends remain uninspected because they are outside the source manifest.

```text
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1  rules/design-authority.md
2b929dcdd31587c1ed5f0b0569cfc41e2f2bc29bf04a5f21be06bf24620718f3  syntax-reference/en/src/expressions/if-expression.md
08beb9711c2373e161a408b19a6ccd6c08e24e0b41791e7fac2ea0a332dec1ed  notes/design/2026-08-20-yu-syntax-chasa-architecture.md
509af68c34e11a2a2d5538df8bab84c599d68154a3f03d57c304bbfb04d8cd39  crates/yu-syntax/src/expression/if_expr.rs
d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442  crates/yu-hir/src/module/local_source.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7  crates/yu-solver/src/candidate_source.rs
28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d  tools/inference-playground/src/runtime/program.rs
4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd  tools/inference-playground/src/runtime/machine.rs
f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487  web/playground/examples/yulang2-ordinary-islands.yu
0102f9e8c6ded9c03c51a71356a1532a9db8742de181d649f642ad9d325f4e5b  ../yulang2-oracle-capture/crates/parser/src/expr/control.rs
bb58bd49ec272003e69d4675c2d6ee1de470e3c1ebaed0f632b6f117629acf38  ../yulang2-oracle-capture/crates/parser/src/expr/group.rs
4253ea5e94b671271fe64b5d1956bb961215e2e5c1278c56d88f0c67caaa7963  ../yulang2-oracle-capture/crates/infer/src/lowering/control.rs
661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898  ../yulang2-oracle-capture/crates/infer/src/lowering/expr/block_local.rs
e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6  ../yulang2-oracle-capture/crates/infer/src/lowering/expr/chain.rs
3390673e476923c817512cc4f0705a71245f530143e6e814cdd03ffaa5da5085  ../yulang2-oracle-capture/crates/infer/src/lowering/expr_syntax.rs
88ce8e06f83884fd825402565c52ab1f19e8b9932500036eae495d392a5c990c  ../yulang2-oracle-capture/crates/infer/src/lowering/record_lit.rs
75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100  tools/inference-playground/src/main.rs
a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473  tools/inference-playground/src/lib.rs
87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56  tools/inference-playground/Cargo.toml
09fecc7c8b8a152ec49d939517d3dcd4951fad48a2909c1faee15bf95cc7a773  tools/inference-playground/tests/cli_demo_identity.rs
c00101fa1b063622a9826a7971add7396e0f73b614d408f2e962a006799966f6  apps/yulang-wasm/Cargo.toml
2fc9feb353b3130c4efc888270cec14cba8b2bbcc2fca03d3780c676e0468f8a  apps/yulang-wasm/src/lib.rs
f4e8dfaf3f089fbee63abac9cc69506cfdd280ad5bdcb980096dbfa83e689a5b  web/playground/src/main.ts
4abce089ada2822578df4dcefa023d0ad83929b2d7188fe4527ee29f80b47d9a  web/playground/smoke-test.mjs
ff870bfa1ba5cbb139a5a0b1d34673684eed9984f821548703ad648d0c9d1caf  web/playground/package.json
68ffb6b9c064dc6b0d6047a70acec19c11b55e3082873af640336aad509e587b  web/playground/index.html
```
