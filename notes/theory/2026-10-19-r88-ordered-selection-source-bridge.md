# R88: exact U/O/S source construction bridge

Date: 2026-10-19. Revision: 1. Sole author: `/root/r88_proof`.
Status: **candidate source/native evidence; independent review pending Luna**.
Sprint: `ordered-selection-source-bridge-20261019-r88`, revision 1,
SHA-256 `56708a4a531bb55b996632bdce3e5fb1e06b8ce4b4903ca5988a4f6f368bb195`.
Baseline supplied by Luna: `acb4366cfd901fe286d692a04336e7ace2c8c949`;
not independently observed through Git.

## 1. Parent and exact result

The original effect-hygiene/source-native parent preserves provider,
annotation position, receiver, request, residual and witness lineages under
the joint assignment `xi=(nu,K,D)`, with actual applicable receiving/selection
evidence and independent outward contributions. Soundness, natural inference,
complete Call and the original universal quantifiers remain OPEN 0→0.
R50 is NOT_ADOPTED. All six hygiene frontiers, P1–P4, F1/FK1, arbitrary foreign
continuations/resumption and native residual correspondence remain OPEN.

R78 §3–5 already derives the receiving, positive local Grant, ordered operation
selection and shallow outward behavior, conditional on authentic HIR. This
artifact supplies a constructive source-owner derivation for that HIR premise
for precisely R78's U/O/S strings. It does not re-prove R78's consumer chain or
promote that candidate to a reviewed theorem. On acceptance, the uninspected
parser/LocalSource seam `R78-SOURCE-HIR-1` is replaced by this finite construction
receipt; `R78-NATIVE-HYGIENE-1` and `R78-UNIVERSAL-1` remain separate obligations.

Governing source authority: top-level inference principles, especially §1/1.1,
and charter §21's outer annotation roles and whole inert argument. No inference
rule, effect cap, execution prerequisite, bypass, or new semantics is introduced.
Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying
intrusion and generalization retain their original obligations. R85 is unused.

## 2. Fixed inputs and identity convention

The three exact strings are R78 §2, with UTF-8 bytes and no final newline:

| Input | Length | SHA-256 | Formal / consumed Name / main byte anchors |
| --- | ---: | --- | --- |
| U | 139 | `d9f97c3a73925e86e1220011adbfd961679a786b0eec6cd39abc12163e761ed4` | 46 / 74 / 107 |
| O | 174 | `31adb9c858d845582fda0005437821af6d67ede26b824b1e0d089d4baebbcb1b` | 69 / 93 / 146 |
| S | 184 | `e0a1037879571d4360201fb66289b60102e3ef3aaf37719ee1ace9b14df939cb` | 69 / 93 / 156 |

Their common structural notation below is a description of actual constructor
outputs, not a replacement parser. For each input separately let `R` be its
relay definition root, `t` its original formal ID, `L` the retained named Lambda,
`a` the formal annotation position, `n` the Catch scrutinee Name, and `h` its
Catch. Let `F` and `op_m` be the family and member declaration IDs minted in
that program. Equal printed names across programs do not identify their IDs.

`SourceNodeKey` brands the parsed source; `source_identity.rs:22–31,145–163`
maps its actual nodes, definitions, parameters and occurrences. The opt-in
entry `shadow.rs:40–45` delegates to `module.rs:1141–1151`, initializes those
keys and enables LocalSource. `module.rs:2100–2138` mints `t` from the original
definition root and formal ordinal and passes that same parameter to `form`.
`local_source.rs:815–842` allocates a fresh occurrence and retains the actual
node key/range at each `set`. We make no numerical occurrence-order assertion:
this opt-in route calls `form`, not the ordinary-carrier `order_occurrences`.
An Apply and its synthetic Unit can share a CallTail key/range while retaining
distinct indices and occurrences. No static occurrence is a dynamic event.

## 3. Constructive parse and declaration path

Use exactly the existing helper's public inputs: one shared `Arc<SourceText>`,
`scan_header` on that allocation, empty `SyntaxEnvironment`, and empty semantic
imports (`runtime_receiving.rs:12–28`). `parse_file`, `full_parse.rs:317–340`,
checks source-allocation agreement and enters `cursor.rs:85–98`'s root parser.
Root statement progression (`root_statement.rs:106–223`) and statement admission
(`statement.rs:304–345,423–459`) route the initial `act` and subsequent `my`
bindings to their actual constructors. These strings have no imported or local
operator declarations requiring another precedence interpretation.

`act_decl.rs:223–295,615–707` constructs the Act head TypeExpression and colon
indented body. Indentation four retains each `our` operation under the Act;
the following column-zero `my relay` closes that body. Binding construction
(`binding.rs:185–257`) emits BindingHeader/Pattern/Equals and BindingBody.
Identifier, punctuation and arrow scans are owned by `lexical/lexer.rs`
(`scan_identifier`, `scan_pattern_nud_payload`, `scan_type_nud_payload`,
`scan_arm_arrow`, `scan_punctuation`); token emission retains ColonColon and
Arrow (`cursor/recovery/emit.rs:299–321`). All delimiters, type heads and bodies
required by these finite strings are present; the construction uses their
normal branches, without a recovery node or a missing slot.

Family formation (`source_annotation.rs:134–223`) reads the actual Act node,
uses default Our visibility, and creates `F=(module, Act SourceNodeKey)`.
It registers all family headers before member signatures. Member formation
(`:225–314`) reads the `our` BindingStatement, its original name and annotation,
and creates `op_m=(F, member BindingStatement SourceNodeKey)`. The per-family
member namespace stores these same declaration objects. Each family name is
unique; each member spelling is unique and nonprivate. In O/S, `op_tick` and
`op_other` are distinct because their declaration keys differ.

For U, `() -> int` parses a ParenthesizedTypeGroup with no inner expression,
followed by TypeArrowTail and result TypeExpression. For O/S, `int -> int`
has identifier argument and arrow result. These productions are
`type_expr/mod.rs:875–905,1780–1830,2198–2258` and its delimiter owner.
`source_annotation.rs:451–530` constructs respectively `Unit -> Int` and
`Int -> Int`, with no outer/argument effects. Thus U's declaration supplies
the Unit compatibility premise; empty arm-call syntax alone does not supply it.

## 4. Original formal, annotation and Name

The space before `(thunk:...)` chooses PatternMlApplicationTail, rather than
an adjacent PatternCallTail (`pattern/mod.rs:1049–1081,1194–1240`). Its sole
argument is a ParenthesizedPattern containing one Pattern with
IdentifierPattern `thunk` and PatternTypeAnnotation. The colon production is
`:1173–1193,1456–1499`; the parenthesized owner is `pattern/delimited.rs:74–105`.
`module.rs:3005–3062` accepts exactly this shape and retains both the original
identifier key and annotation node. There is one formal, below the existing
supported-depth limit, and no binding-level annotation to confuse with it.

Leading `[signal] int` / `[io] int` emits a BracketRow and the value head in
the same TypeExpression (`type_expr/mod.rs:781–800,1355–1452,1608–1628`).
`source_annotation.rs:359–386,409–433,531–587` retains `a`, owner `R`, outer
`effects=Some(row)`, value `Int`, one concrete `F`, and no row variables.
This is a source permission/schema, not inflow or a residual.

`local_source.rs:596–628` copies the already minted original `t` into the
LocalSource parameter, parses the retained annotation with owner `R`, pushes
`thunk -> Parameter(t)` into the lexical environment, and sets `L` to
`Lambda(parameter=t, body=h)`. It does not reconstruct an unannotated formal
or allocate a substitute formal. The Catch scrutinee parses as the identifier
expression `thunk`; lookup `:1004–1040` consults the live lexical entry before
module names and emits `n=Name(Parameter(t))`. No Catch binder shadows it.

RuntimeProgram consumes these same outputs (`program.rs:414–433,451–509`):
outer effects select Computation for `L` and Execute for `n`; `receiving.rs:21–43`
accepts `RootCompSchema` because annotation/formal ownership agrees with `R`
and the value is Int. This discharges the source/formal ownership and role
premises used in R78. It supplies no solved native endpoint or entry profile.

## 5. Ordered Catch construction and argument inputs

`operator_chain.rs:267–284` selects Catch syntax. `case_like.rs:116–233` emits
CatchScrutinee/OperatorChain and recognizes `{`; `:340–389` constructs its
CatchBlock. Its sequence loop `:441–516` calls `arm_normalized` in source order.
The first comma belongs to the operation/continuation pair (`:565–616`), the
arrow starts the body, and the later comma separates arms (`:1251–1320`).
CatchBraced body stops include comma and `}` (`:1068–1097`), so S's `other p`
body does not consume the next arm.

Each operation pattern is exactly Pattern with IdentifierPattern family,
PatternPathTail `::member`, and adjacent PatternCallTail. The path/call
productions are `pattern/mod.rs:1019–1081`. `_` is IdentifierPattern here;
the constructor recognizes its spelling as Wildcard, not a new binder.
`local_source.rs:1117–1180` iterates block children, skips separators, and
pushes each arm into a vector without sorting or deduplicating. It retains
arm key/range and operation-pattern key. Empty call produces one explicit
`LocalSourceCatchPayloadPattern::Unit`; a single `p` produces one Value/Binder.
Each `p` ID includes `(R, arm SourceNodeKey, ordinal 0)`. Equal spelling in
another arm does not merge binders. Continuation `_` produces Wildcard.

| Input | Ordered retained arms | Retained relay argument |
| --- | --- | --- |
| U | `(op_ping, [Unit marker], Wildcard) -> Integer("1")` | `Group(Apply(Operation(op_ping), Unit))` |
| O | `(op_other, [Binder(p0)], Wildcard) -> Integer("99")`; `(op_tick, [Binder(p1)], Wildcard) -> Name(CatchBinder(p1))` | `Group(Apply(Operation(op_tick), Integer("7")))` |
| S | `(op_tick, [Binder(p0)], Wildcard) -> Apply(Operation(op_other), Name(CatchBinder(p0)))`; `(op_other, [Binder(p1)], Wildcard) -> Integer("99")` | `Group(Apply(Operation(op_tick), Integer("7")))` |

The arm worklist is pushed in reverse solely to process bodies in source order;
each CatchArm installs only its own binders and restores the lexical depth
after its body (`:639–646,1173–1179`). O's returned `p` and S's argument `p`
therefore resolve to their selected arm's payload binder.

Expression path construction (`operator_chain.rs:688–710`,
`tails/fixed_access.rs:path_tail_normalized`) and LocalSource `:855–978` use
the same `resolve_operation` (`:1088–1100`) as Catch patterns. It looks up
the unique `F`, then `(F,member)`, and rejects private/ambiguous alternatives.
Thus the initial request and its matching arm carry the same resolved operation
ID; O's earlier `other` has a different ID. CallTail `()` emits distinct Apply
and Unit nodes; spaced `7` and `p` emit MlArgument applications. Parentheses
retain Group (`:1054–1083`). Module Name `relay` resolves through the unique
module namespace. These are the actual inputs to the whole inert argument
construction reused from R78; the source bridge allocates no receiver/event.

`RuntimeProgram::from_hir`, `program.rs:277–330,451–566`, validates child labels,
retains source sites and clones patterns/operation resolutions. Catch `arms.iter`
mapping preserves vector order. U's Unit marker is consumed by
`machine.rs:1641–1658` in the no-binding branch after declaration compatibility;
R78's phrase “lowers to wildcard” describes that consequence, not a literal
source enum variant. There is no constructor mismatch requiring new semantics.

## 6. Apply to the parent and preserve the remaining seam

Substitute §§3–5 into the authentic-HIR premise of R78 §3–5. The original
annotated formal, Name route, resolved declarations, arm order and patterns
now have source-producer evidence. Reusing R78's existing positive local Grant
and consumer derivation gives its candidate conclusions: U returns 1; O skips
other and returns its tick payload 7; S's selected tick arm requests other
outside the consumed shallow handler. S's arm operation occurrence is distinct
from the thunk tick occurrence; its future event `q2` is distinct from `q`.
Neither a source identity nor a same-family membership identifies these events.

No continuation is captured by the three Wildcard continuation patterns.
Their discard actions establish no F1/FK1, foreign-continuation or resumption
case. No successful ground result proves an empty residual. No outward runtime
request proves a constraint-derived native residual. The duplicate-match arm
contrast belongs to the separate implementation lane and is not evidence used
to prove this construction. No execution result was observed by this author.

`runtime_receiving::machine` also requires `CandidateInference::solve` success
and absence of candidate conflicts before building the runtime. This receipt
does not prove those general inference properties or substitute written test
assertions for execution. Native supplier/consumer closure remains at
`candidate_source.rs`'s formal registration / `Action::FormalEntry` / formal
Name and Catch paths, `shadow_apply.rs`'s solve/transport, and the downstream
mapped-bound/effect/lifecycle owners named in R78 §7. Only the first of R78's
two distinct seams is addressed here.

Mutual TODOs for Luna:

| Request | First missing evidence, owner and exact falsifier |
| --- | --- |
| `R88-REVIEW-1` | Fresh independent review of these frozen bytes and pins. Falsifier: any cited parser branch emits a different node/owner, identity, annotation, arm order or pattern for exact U/O/S. A producer/coauthor cannot certify it. |
| `R88-RUNTIME-ORDER-1` | Implementation lane plus Luna's one authorized verification command supplies same-operation duplicate-match reversal evidence. Falsifier: rejection, missing Grant, or identical results after reversing the two matching arms. No test result can repair a constructor mismatch. |
| `R78-NATIVE-HYGIENE-1` | Luna routes source annotation/formal and native lifecycle/consumer work: derive source-licensed entry profile, mapped original bounds actually admitted, inflow/residual and joint `K,D`, preserving FreshUse/provider/witness lineage. Falsifier: permission substituted for inflow, original endpoint substituted for copied endpoint, or an independent contribution lost. |
| `R78-UNIVERSAL-1` | Original parent owners supply remaining profiles, source/lifecycle cases, protected/unmatched contributions and independent continuation quantifiers. Falsifier: these ground discard examples offered as arbitrary foreign-continuation or all-source proof. |

No production implementation TODO follows from this constructor audit: no source
change is needed by the candidate result. A future need for native code evidence
requires Luna's separately bounded provisional TODO and exact consumer falsifier.
Next step in this envelope: freeze and stop; review/integration belongs to Luna.

## 7. Dependencies, checks, resources and stop receipt

The 103-path R88 manifest SHA-256 is
`c6321c23f92259a255098d1f7528ee532c899d12cb0fea70959e7dce95a65fe5`.
R78's exact dependency is
`a6fcf5c95169f7b71932476a5fff915e1ac450b7859755c595bf6d73a30af31c`,
sole author `/root/r78_proof`; its earlier reviewed dependencies retain only
their original premises, as recorded in R78 §6/8. This artifact adds no theory
dependency outside the frozen read domain. R78's unobserved-source limitation
motivated this changed method/input: authentic parser and HIR producer audit,
not another assumed-transition proof. Withdrawn bypasses, R50, R77, R85,
storage/fiber constructions and new semantic laws are unused.

SHA-256 inspection verified the contract, manifest, R78 artifact and all 102
manifest paths excluding the concurrently leased implementation test file.
That file's helper was read as a locator; its evolving added test is not a
frozen proof dependency. The pinned production source hashes all matched.
Checks were read-only source/branch inspection and byte hashing, with no parser,
compiler, runtime, model checker, probe, test, build, network or Git execution.
No concrete HIR IDs, runtime receivers, request ordinals or inferred residuals
were observed. No tests or source files were edited.

Sole author/writer `/root/r88_proof`, session
`current-conversation-2026-10-19-r88-source-bridge`; assignment received from
`/root`. Requested model/effort `gpt-6-sol` / `high`; effective observed
model/effort UNKNOWN / UNKNOWN. No descendants, coauthors or delegation.
Budget 600 seconds charged at grant, no renewal; exact observed elapsed/freeze
receipt is in the handoff. All new paths: this note and
`tasks/agent-loop/inbox/20261019-r88-proof.md`. Scratch/generated paths: none.
After the frozen handoff, writes stop; no unresolved descendant leases.
This is research preservation pending fresh review and Luna intake, not parent
closure, production approval, or a claim of continuing work while waiting.
