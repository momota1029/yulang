# R132: ordinary identity and countdown source-to-consumer bridge

Status: **candidate source/native evidence and conditional completed-path derivation**. No reviewed theorem, inference soundness/principality, production authority, or parent closure.

Sole author: `/root/r132_ordinary_proof`, current tool-backed assignment from `/root`; no descendants. Requested Sol/high; observed model/effort UNKNOWN/UNKNOWN. Contract R132 revision 1, SHA-256 `5335bbb4e6d0bdcd1f0e46e947990d1e61cdde1e23e53045abbe8e0760e5efe6`; baseline `9fab033a27390ac12f7553a9d6af11a82ad66e1b`, supplied by Luna, no Git inspection. The contract's status text is DRAFT_FOR_PRE_EXECUTION_REVIEW; Luna explicitly granted this bounded proof assignment. This grants no implementation activation or semantic authority.

## Exact source and result claim

The source is the identity block at Yulang2 sample lines 46–53 and countdown block at lines 60–63, including the pinned whitespace. Extract bytes from the first comment up to the factorial comment, append one LF, then append bytes from the countdown comment up to the effectful-role comment. The result is **388 bytes**, SHA-256 `f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487`. The first slice already ends in two LFs; the added separator produces three LFs between blocks, and the second slice ends in two LFs. Whitespace normalization produces a different artifact.

```yu
my identity x = x
our int_identity = identity 7
our bool_identity = identity true
our string_identity = identity "ok"
int_identity
bool_identity
string_identity

my countdown flag = if flag { 8 } else { countdown true }
our countdown_result = countdown false
countdown_result
```

The display omits comments and exact extra LFs for readability; the byte recipe and hash are authoritative for this packet. The read-only Yulang2 test `runs_web_playground_example` lists values `7`, `true`, `"ok"`, and `8` and the four corresponding definition types at lines 185–189,207–211. Reading that test is oracle provenance, not a claim that it ran here.

**Conditional local claim.** If the exact fixture parses and forms authentic retained carriers, `prepare` completes conflict-free candidate inference, RuntimeProgram construction succeeds, the called literal/receiving primitives preserve their advertised values and view identities, and the machine has enough resources and steps, the inspected ordinary control path yields selected results:

| Selected definition | Completed value | `execute` output |
| --- | --- | --- |
| `int_identity` | integer 7 | `7\n` |
| `bool_identity` | Boolean true | `true\n` |
| `string_identity` | string ok | `"ok"\n` |
| `countdown_result` | integer 8 | `8\n` |

The first hypotheses are not proved by this control derivation. No parser, solver, machine, WASM or test was executed by this author. In particular, the actual candidate's conflict-freedom and all emitted native transitions are not inferred from an assumed source tree.

## Authentic construction and candidate constraints

`local_source::form_ordinary` stages an authentic source carrier and original occurrence mapping; `form` constructs named parameter Lambda chains and installs actual parameter identities before constructing their bodies (`local_source.rs:531–660`). Identifier construction consults lexical binding identities before the module namespace (`:1043–1077`). Thus `x` and `flag` resolve to their original parameters, while top-level `identity`, `countdown` and the four result Names resolve to ModuleDef identities. A top-level private `my` function is not a nested `Local` binding. The nested-local self-link/install machinery is not the recursion proof for this fixture.

Application tails construct distinct callee/argument indices and retained Apply occurrences (`:887–1011`); integers, Booleans and strings retain their own literal constructors. `conditional` constructs both body children and the condition, restoring the enclosing lexical environment for each (`:1314–1363`). It does not select a branch during inference. `countdown` therefore retains both `8` and `countdown true`, even though the later runtime control is finite.

`candidate_source::emit_candidate_source` validates pointer identity against the original HIR carrier, owner/receiver correspondence and occurrence ownership (`:827–846`). It allocates an expression component per occurrence and a formal recipe per actual Lambda. The unannotated formals have Value role (`:870–884`); their Name value endpoint is the exact parameter endpoint (`:893–902`). This joins identity's result Name to its formal without creating a computation-role permission or a replacement provider.

At `:1165–1184`, each literal generates positive-leaf-to-value and value-to-negative-leaf bounds plus bottom/empty effect bounds. At `:1240–1268`, countdown's condition endpoint is constrained to Bool; both then and else body endpoints contribute to the same conditional result, with distinct child occurrence slot-50 bounds and effect slot-51 bounds. This is accumulation from both branches, not constant folding. At `:1391–1435`, each Apply retains its actual callee, argument, effects, result, level, cause and source-input recipe. At `:1482–1500`, each Lambda retains its formal registration, parameter position and actual body value/effect endpoints. Unannotated definitions link their body endpoint to their own definition root (`:1523–1543`).

`execute_candidate_action` (`:1731–1770`) sends Facts to `admit_collected_fact`, value links/constraints to `admit_candidate_value_link`, Apply recipes to `admit_candidate_fact`, and Lambda recipes to `admit_lambda_fact`. `admit_candidate_value_link` records the source occurrence/cause and invokes ordinary `constrain_live_value` (`candidate_scheme.rs:1989–1996`). These are actual source-owner dispatch sites; this note does not invent their downstream solver behavior. The bodies of the general native Apply/Lambda admission and propagation owners are outside the frozen owner pins and are not new proof dependencies here. Their complete source/native adequacy remains an explicit missing case.

## Generalization, three uses and recursion

`execute_candidate_graph_plan` runs dependency-first definition SCCs. It registers active roots/internal uses, executes every member's source schedule, captures all member graphs at boundary zero, and only then publishes the component's graphs (`candidate_scheme.rs:1361–1445`). Countdown's self-reference takes `Action::Module` -> active-use `route_candidate_open_use` -> `route_internal` (`candidate_source.rs:1752–1757`; `candidate_scheme.rs:1465–1472`). Its recursive root is observed while open. It is not repeatedly freshly generalized inside its own body.

Uses from the three distinct identity applications take the published incoming graph route. `route_candidate_graph` captures the target's live graph and `instantiate_candidate_graph` reconstructs it for the exact DefinitionUse occurrence, level and cause (`:1474–1495,1911–1965`). `prepare_candidate_fresh_use` creates a distinct `context_use`, reconstructs terms with one canonical row map, and freshens only rows satisfying `row.local && level > graph.boundary && !metadata.non_generic` (`:1557–1627`). Older/nongeneric coordinates may remain shared. This is not a proof that all coordinates are disjoint, nor that the exact identity graph's coordinates satisfy that guard after every propagation event.

Every captured bound is mapped through that same FreshUse and driven through bound restoration (`:1536–1555,1863–1910`); source-bound, antecedent, mapped relation and use-origin evidence are retained. The final route retains graph, rows and maps, rather than equating the original provider root with each copied root. This supplies the current owner path needed to investigate cross-use contamination. It does not discharge the older universal mapped-admission/consumer-correspondence premise in computation-forwarding §6. No extrusion is undone merely because countdown is in a definition SCC: the distinct occurrence-qualified Value-reference SCC criterion remains governing. No new extrusion/intrusion semantics or bypass is introduced.

## Runtime schedule and constructive control trace

WASM `run` calls `yu_playground::execute` with `scoped=false`. `execute` first calls `prepare`; syntax diagnostics, unsupported lowering, solver availability errors or candidate conflicts prevent runtime construction (`lib.rs:167–201,280–342`). Runtime construction receives the same HIR and default evidence; this is not a candidate proof certificate for runtime hygiene.

`RuntimeProgram::from_hir` iterates authentic HIR items and obtains their retained LocalSource, compiling original identities into labels and SourceSites (`program.rs:262–315,435–570`). Every formal here has Value role and its Names use Observe. Each top-level definition has its own global cell. Computed Apply roots are scheduled in source order; Lambda definitions materialize on first Name demand. All four bare expression roots are scheduled unconditionally and discard their results (`:613–657`). No synthetic main or module-result consumer is added.

For each identity application: Name lookup demands or reads the one cached identity closure; Lambda construction captures body/parameter/lexical environment without evaluating the body. Apply evaluates the callee first, allocates an inert whole argument Delay, creates an actual invocation, then ValueEntry forces that Delay and binds the resulting value to the original parameter. The body Name observes precisely that invocation's bound cell. ReceiverReturn restores the previous owner and returns the value (`machine.rs:561–669,898–1010,1089–1126,1294–1342,1975–1981,2017–2057`). Distinct calls allocate distinct argument cells; reading the cached identity closure does not cache its previous argument or result.

For countdown false, the outer invocation binds false to flag. Condition observes false and enters the else branch. The recursive Name reads the already-materialized countdown Lambda cell: that cell was populated when callee lookup finished, before its body invocation began. Therefore this path does not re-enter an unfinished countdown definition initializer. The recursive call binds true in a second invocation; Condition chooses the then branch, evaluates 8, and both ReceiverReturn frames return in nesting order. The recursive else branch is not executed again. This is a two-call control derivation for this source, not a general recursion-termination theorem (`:1190–1221,1247–1277`).

Root completion caches each result in its own cell. ExpressionReturn discards the expression value and advances the root cursor. After the complete source-order schedule, `begin_root` returns the selected cell (`:1247–1277,1851–1902`). Each fresh `execute` starts a fresh machine/cache. The output decoder prints integers and Booleans directly, strings using debug quotation, then one LF (`lib.rs:190–201`). Literal decoding and Receiving helper internals are called but are not newly imported frozen proof dependencies; their current executable correspondence is reserved for the approved smoke evidence. Exhausted budget, unavailable view/owner, wrong condition type or missing binder gives no completed result.

## Application to original parents and historical reuse

R65-CURRENT-OPERAND-1 still requires the completed symbolic operand of the original **annotated computation-formal Lambda** under the original joint context and prior evidence. R64-SRC-ANN-ARG-1 still requires its distinct whole-ascription negative argument-position interpretation, with its own permission/scope and correlated result evidence. This fixture has no computation formal, whole annotation, io family, negative annotation row or corresponding shared context. The Value identity Name path is useful current-constructor evidence, but its hypotheses do not instantiate either missing owner premise. Both remain **OPEN**, with no reduced premise claimed.

The original computation-forwarding §§1,6–7 quantify over every finite typed prefix, arbitrary finite forwarding chains, repeated/simultaneously live entries and a shared satisfying assignment; their mapped admission and dynamic source/native joins remain open. Ordinary identity supplies no nonempty protection schema. F1/FK1 and foreign-continuation obligations are independent and unchanged. Simple-sub A/B, R85, R99, all six effect-hygiene, source-law and production gates remain OPEN.

Reused within premises: R64/R65's exact premise mismatch; forwarding's original/copy distinction and explicit native admission hypothesis; ordinary-runtime simulation's closure/Delay/environment/control invariant. The latter is a historical independently reviewed theorem over its **frozen constructed-program envelope**; this note checks current owner correspondence for this finite ordinary case and does not inherit its old source hashes as current proof. Rejected: old line numbers as current evidence; green tests as generalization soundness; lexical roots as typed annotation arguments; fresh context IDs as runtime receiver identities; definition SCCs as qualifying intrusion; one local action as foreign-continuation closure. No withdrawn bypass is restored.

## Handoff, falsifiers and freeze

**R132-EXEC-1**, owner Luna/implementation and fresh reviewers: use the unchanged pinned fixture through existing `run`, then perform only the contract's single post-review smoke command. Required output is all four exact strings through the same fixture/API. Falsifier: any fixture hash difference, source refusal/conflict, cross-use contamination, recursive initialization failure, incomplete schedule, wrong selected cell, budget exhaustion or output mismatch. This is approved finite executable evidence, not proof of the assumed admission premise for all source programs. No compiler edit or new instrumentation is requested.

**R65-CURRENT-OPERAND-1 / R64-SRC-ANN-ARG-1**, owner Luna/source typing supplier: retain their exact annotated source, original component context, formal/whole-annotation positions and prior-evidence requirements. Falsifier: replacing that computation-formal case by this Value-formal identity, assuming joint xi or using native inequality/row equality as source formation. No new source dependency or semantic solution is proposed.

All eight compiler/runtime pins checked by this author match the R132 contract. Full source and oracle hashes match their pins. Dependency manifest/provenance and check receipt are frozen in the one assignment inbox. Code authors are not inferred from files; historical R64/R65 author is `/root/r63_whole_ascription_formation_proof`; original forwarding/runtime review provenance remains in those documents. Static reads and byte hashing only; one byte-extraction attempt failed because `python` was unavailable, followed by successful `python3` extraction. No tests/builds/compiler/formatter/CLI/Git/probes, external contact, source edits, scratch files or descendants. New paths are this note and `tasks/agent-loop/inbox/20261020-r132-proof.md` only. Finite assignment ends at this freeze; fresh independent review and any further owner/dependency allocation belong to Luna. **STOPPED / WRITES_STOPPED / NO_DESCENDANTS** after the inbox is frozen.
