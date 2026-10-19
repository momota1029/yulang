# R133: the unchanged three-use identity island

Status: candidate source/native correspondence and conditional finite operational derivation. Independent review NOT_RUN by this author. No polymorphic soundness, principal scheme, reviewed theorem, parent closure or production authority.

Assignment R133 revision 2: `tasks/agent-loop/sprints/yulang2-identity-island-20261020-r133-rev2.md`, primary-supplied SHA-256 `01a057ed44d4d0e2d58e74bb515e750762aff18c17350d3f18b19be031127539`. Sole author `/root/r132_ordinary_proof`; new exact R133 lease from `/root`. No descendants. Requested model/effort Sol/high; observed UNKNOWN/UNKNOWN. Numeric session identifier and R133 baseline not exposed: UNKNOWN. The no-command boundary prevents local contract/dependency rereads; scope and current pin equality are conditional on Luna's current explicit assignment and pin receipt, not independently revalidated here.

## Exact source and claim

The primary supplied the unchanged external sample lines 46-53, including two final LF bytes:

```yu
// one generalized function used at three types
my identity x = x
our int_identity = identity 7
our bool_identity = identity true
our string_identity = identity "ok"
int_identity
bool_identity
string_identity

```

The exact supplied string is 210 ASCII bytes, SHA-256 `b4d68db12c1845f23b5c8a3231249952470868d22d9489a8590270a57de77a3f`, recomputed in process from that supplied string without a shell command or file read. No countdown or other sample block belongs to this packet. Projection to this explicitly selected witness does not narrow any original language or parent-theorem domain.

**Conditional finite claim.** For this exact source, if authentic constructor formation succeeds, the actual candidate admits it without conflicts using the retained per-use scheme routes described below, and the runtime constructors/helpers execute successfully within their finite budget, selecting the three definitions yields respectively `7\n`, `true\n`, and `"ok"\n`. No parser, candidate, runtime or test is run by this author. The three outputs below are derived control observations under stated premises, not an execution receipt.

## Constructor and retained binder premise

Reuse R132's inspected identity constructors only at unchanged pins. `local_source::form_ordinary` stages original source occurrences and `form` builds the named Lambda chain, retaining the original parameter identity before constructing its body (`local_source.rs:531-660`). Identifier formation consults lexical identities before the module namespace (`:1043-1077`). Thus the body `x` denotes the parameter of this actual identity Lambda; the three callee Names denote the same top-level identity ModuleDef. The three result definitions and their bare expression reads retain their own identities.

The top-level private `my identity` is a definition, not a nested local scheme. No nested-local publication or self-recursive-link premise is used. Application construction retains separate callee/argument indices and original Apply occurrences (`:887-1011`). The three argument literals are distinct Integer, Boolean and String constructors. These claims are construction consequences conditional on successful authentic parsing/admission of the supplied syntax, not observed allocated IDs.

## Candidate constraint and admission premise

`candidate_source::emit_candidate_source` validates original HIR-carrier pointer identity, source receiver/owner and occurrence ownership (`candidate_source.rs:827-846`). It allocates components and registers the actual formal. The unannotated formal has Value role (`:870-884`); its body Name endpoint is precisely that parameter endpoint (`:893-902`). This is a value connection, not a computation-formal permission schema.

For each actual argument literal, the source owner generates its positive primitive-to-value and value-to-negative primitive bounds, with bottom/empty effect bounds (`:1165-1184`). Each Apply retains its own original callee/argument endpoints, levels, effects, result, cause and source-input recipe (`:1391-1435`). Identity's Lambda recipe retains the actual formal registration and body endpoint (`:1482-1500`); its unannotated body links to the definition root (`:1523-1543`). No generation-time satisfiability test, source special case, search or weakened inference is introduced.

The actual dispatch path is Facts -> `admit_collected_fact`, Apply -> `admit_candidate_fact`, Lambda -> `admit_lambda_fact`, and links -> `admit_candidate_value_link` (`:1731-1770`). The last records the original constraint occurrence/cause and invokes `constrain_live_value` (`candidate_scheme.rs:1989-1996`). General native Apply/Lambda admission and propagation helper internals are not new read dependencies in this no-command packet. Their source/native adequacy is an explicit premise, not proved by naming these dispatches.

The tool entrypoint `prepare` must actually finish syntax checking, retained-source lowering and `CandidateInference::solve`, with no candidate conflicts (`lib.rs:280-342`). A plausible set of source constraints is not proof of that acceptance. If the actual constructor or solver refuses any of these three uses, the executable witness fails at that owner.

## Scheme and FreshUse premise: all three uses

`execute_candidate_graph_plan` finishes dependency-first SCC member schedules and captures every member before publishing its graphs at boundary zero (`candidate_scheme.rs:1361-1445`). There is no recursive identity use in this fixture. Each of the three distinct incoming identity-use occurrences consumes the published graph through `route_candidate_graph` and `instantiate_candidate_graph` (`:1474-1495,1911-1965`), using its own DefinitionUse occurrence, cause and use level.

`prepare_candidate_fresh_use` creates a use context and one coherent canonical reconstruction map. It copies a coordinate only when the actual guard `row.local && level > graph.boundary && !metadata.non_generic` holds (`:1557-1627`). Older/nongeneric coordinates may remain shared. Reconstruction restores each captured bound through that same FreshUse, retaining its source bound, antecedent, mapped relation and use origin (`:1536-1555,1863-1910`). It retains graph/rows/maps with the route.

Consequently the constructor route does not identify all three callee occurrences with one shared instantiated argument variable. It also does not prove that every coordinate needed by this exact source satisfies the freshening guard after real propagation. The essential candidate premise is that the actual completed capture/reconstruction/admission gives each use the required generic instance, preserving all legitimate shared dependencies, with no illicit cross-use contamination. No assertion of fully disjoint graphs, inferred principal type, universal capture coverage, qualifying intrusion or mapped-bound activation follows from this finite source audit.

In particular, literal argument int/bool/string constraints must reach their own reconstructed identity instance and its actual Apply result. Equal spellings, a stored graph, or three context IDs alone do not establish these consumer joins. Simple-sub levels, extrusion, occurrence-qualified Value-reference SCC intrusion and accumulated constraints remain the governing operations; a definition SCC is not substituted for the intrusion criterion.

## Runtime consumers and constructive observations

WASM `run` delegates to `execute` with `scoped=false`. After `prepare` succeeds, `execute` constructs RuntimeProgram from that same HIR with default evidence, selects the requested definition and starts the retained source schedule (`lib.rs:167-201`; `apps/yulang-wasm/src/lib.rs:11-21`). Candidate acceptance is a gate to this experimental evaluator, not a proof certificate of runtime hygiene.

`RuntimeProgram::from_hir` compiles authentic SourceSites and labels; all parameters here have Value role and their Names use Observe (`program.rs:262-315,435-570`). It allocates separate definition cells. The three computed application definitions enter the source-order schedule, while the identity Lambda materializes on first demand. Every bare expression root is scheduled and its result discarded (`:613-657`). There is no synthetic main, final module result or new API.

At the first application, the identity ModuleDef Name demands its Lambda, obtains the closure and caches it. Each Apply evaluates that callable first, then allocates an inert Delay for its own argument and starts a fresh actual invocation. ValueEntry executes the Delay, binds the resulting value to the original parameter in this invocation's environment, and runs the body. The body Name reads that bound cell with Observe. ReceiverReturn checks/restores the previous owner and returns the same received value (`machine.rs:561-669,898-1010,1089-1126,1294-1342,1975-1981,2017-2057`).

Apply this path separately:
- integer argument 7 -> parameter cell containing integer 7 -> body Name -> int_identity result cell;
- Boolean argument true -> a new parameter cell containing true -> body Name -> bool_identity result cell;
- string argument ok -> a new parameter cell containing that string -> body Name -> string_identity result cell.

Reusing the cached closure preserves its lexical environment and code; it does not cache a previous argument or application result. Each call allocates its own parameter cell. Root completion caches the three results separately, bare ExpressionReturn discards only the expression value, and `begin_root` returns the selected definition after completing the schedule (`:1247-1277,1851-1902`). Each separate `execute` starts a new private machine/cache. The output decoder prints the selected primitive value, quotes strings, and appends LF (`lib.rs:190-201`).

This finite control argument assumes successful literal decoding, Receiving view checks, owner checks, allocation and step budget. Their helper bodies were not newly read here. Missing/incorrect binders, conflicts, source refusal, invalid views, unavailable construction or exhausted steps withhold completion; they do not produce one of the claimed outputs.

## Parent application, reuse and remaining ownership

R132's identity-only constructor, Value-entry and cache/control reasoning is reused under primary-confirmed unchanged pins. Countdown's recursion, conditional inference and two-call termination argument are excluded. R132 was a candidate conditional packet; neither that packet nor the current no-command derivation is independent certification. The source-audit agreement is Luna-reported, not a new independently read proof dependency.

R65-CURRENT-OPERAND-1 still asks for the original annotated computation-formal Lambda's completed symbolic operand under its original joint context/prior evidence. R64-SRC-ANN-ARG-1 still asks for the distinct whole-ascription negative argument-position interpretation with its own permission/scope and correlated result evidence. This unannotated Value-formal identity supplies neither premise. Both remain OPEN; no reduced premise is claimed.

Original computation-forwarding every-finite-prefix, arbitrary finite-chain, repeated/simultaneously live entry and joint-assignment quantifiers remain unchanged. F1/FK1 and foreign-continuation cases are independent. Simple-sub A/B, R85/R99, all effect-hygiene/source-law, implementation-adoption and production parents remain OPEN. Original/copy endpoints, provider identities, receiver entries and evidence lineages are not collapsed. Historical operational invariants are used only under their actual ordinary-constructor premises; historical proof status or tests cannot establish current inference admission.

**R133-SELECTED-EXEC-1**, owner Luna/implementation and fresh reviewers: obtain the authorized finite execution evidence from this exact 210-byte fixture through existing `run`, requiring all three exact outputs and unchanged selection behavior. Falsifier: wrong source hash, candidate refusal/conflict, cross-use type contamination, incorrect callee/argument/result join, wrong selected cache cell, scheduler interruption, budget exhaustion or output mismatch. No compiler edit or instrumentation is requested. A failure returns the exact owning constructor/consumer to Luna.

**R65-CURRENT-OPERAND-1 / R64-SRC-ANN-ARG-1**, owner Luna/source typing supplier: retain the original annotated source and context; replacing it by this Value-formal identity, assuming xi/endpoint, borrowing a permission, or treating native comparisons as source formation remains a falsifier. Fresh reviewers and any larger native-owner proof allocation belong to Luna.

Freeze, dependency provenance, in-process hashes and resource/stop receipt are recorded in `tasks/agent-loop/inbox/20261020-r133-proof.md`. Only these two exact leased paths are written. No shell commands, tests/builds/compiler/formatter/CLI/Git, implementation edits, external contact, scratch files or descendants. This finite assignment ends with STOPPED / WRITES_STOPPED / NO_DESCENDANTS after handoff freeze.
