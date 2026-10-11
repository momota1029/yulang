# Approved Value references: source-to-consumer bridge audit

Status: frozen research-only static characterization; independent review pending
Baseline: `c2b38446c445f5f932aabe8253daf8fc1d0110d8`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this note only; no implementation authority
Parent construction, transport, SCC correspondence and equality gates: OPEN

## Objective and exact premises

Map the approved source owners to retained candidate inputs, extrusion,
use-time freshening, SCC qualification and parent equality. This complements
the constructive proof lane; it is not a new proof of compiler soundness or
principality, and does not repeat the exact odd/even admission audit.

Authority is the [parent-copy decision](../design/2026-10-10-parent-copy-scc-intrusion.md),
sections **Value-reference SCC clarification**, **Apply-result source-fragment
ownership**, **Nested Apply membership**, and **Definition-root Value ownership**;
the [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; and the accepted decisions recorded at `tasks/current.md:10903–11011`.
Relevant source contracts are [local self-recursion](../design/2026-10-10-local-self-recursive-binding.md)
**Selected source behavior / Proposed source-to-solver seam**, [source Generalize](../design/2026-10-08-source-generalize-definition.md)
§2, [nested block interpretation](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§2–3, and [body-to-definition subtyping](../design/2026-09-20-binding-body-definition-root-directed-subtype-draft.md)
**Evidence and boundary / Proposed gate**. The latter typing relation supplies
no source-reference edge.

Accepted premises, without additions:

- An Apply result owns resolved Names recursively through its callee/argument
  subtrees, including nested Apply operands. `f(0)(0)` requires both results
  to reference the original formal F. Containment alone supplies no R2→R1 edge.
- Each definition root owns Names in its source-owned initializer/body;
  nested declaration initializer Names belong to that nested definition root.
  The root is not semantically identified with its Lambda, Block or Apply rows.
- Cross-level references remain eligible for SCC membership. Comparisons,
  bound payload direction, Function ports and parent genealogy supply no
  replacement incidence.
- Apply membership through wrappers, Lambda, Block and local initializers
  remains unspecified. Definition-root ownership is separately selected;
  standalone Lambda-row or Block-row adjacency is not selected by that rule.

Operational characterization assumes an authentic recovery-free carrier,
resolved Names, successful checked allocation, and the private candidate graph
route. A missing premise or failed action prevents this characterization from
becoming an observed successful source history. No equality is assumed merely
because two bindings form a source-owner cycle.

## Constructor and owner matrix

All source locators below are under `crates/`. The matrix records existing
operations, not proposed implementation details.

| Owner / required incidence | Actual constructor and retained coordinates | Native action / publication | First missing bridge |
| --- | --- | --- | --- |
| Direct Apply result R→resolved binder B | `yu-hir/src/module/local_source.rs:99–152,636–657` retain occurrence, source key, scope and ModuleDef/Parameter/Local resolution. Apply retains operand indices at `:553–563`. `yu-solver/src/candidate_source.rs:187–217` allocates components and aliases parameter Names to actual formal endpoints. | `candidate_source.rs:394–411` retains Apply recipe and `ApplySourceInput(owner,expression,callee,argument,result,...)`, then emits Candidate action. `shadow_apply.rs:1335–1404` forms a negative Function demand and admits callee <: demand. | The Apply constructor does not emit a correlated R-owned resolved-Name incidence. Source inputs and typing ports coexist but are not that record. |
| Nested Apply outer R2→original F, inner R1→F | HIR retains nested operand trees. `candidate_source.rs:265–267` recursively visits argument and callee, then builds each Apply separately. | Outer Apply's callee endpoint can be inner result R1. `formal_names` recognizes a direct formal Name and forwards through Group/ascription/Block final; it does not aggregate nested Apply Name membership (`:238–245,394–411,414,439,463`). | No recursive incidence accumulation associates inner Name F with outer result R2. A retained R1 callee endpoint does not supply R2→F or authorize R2→R1. |
| Module definition root O→Names in its owned body | `yu-hir/src/module.rs:1411–1427` retains LocalSource keyed by separate `DefinitionRootId`; `local_source.rs:286–321` retains Lambda body structure and original parameter scope. Root components are separately indexed. | `candidate_source.rs:477–498` selects the actual module root and emits Annotation or body-endpoint Link. `:665–668` admits a Value subtype link. | Publication retains no definition-root Name incidence. L <: O does not transfer approved ownership by itself. |
| Local definition root E→Names in its initializer; enclosing O excludes those initializer Names | HIR records `HirLocalId`, initializer index, parameter scopes and `LocalInitializer` boundary (`local_source.rs:738–805`). Candidate walk enters each initializer and installs it afterward (`candidate_source.rs:288–327`). | Active recursive local Names use an open initializer endpoint (`:300–305,381–387`); published local Names freshen. Unannotated installation stores `LocalScheme(id,root,boundary)` from the actual initializer endpoint (`candidate_scheme.rs:1316–1335`). | No E-owned initializer incidence is installed. Module Name uses still record the enclosing module `parent_ordinal` at `candidate_source.rs:377`, including Names inside E's initializer. That module scheduling coordinate cannot substitute for nearest definition owner E. The current unannotated local root uses the initializer row; this constructor coincidence does not identify all definition roots with Lambda rows or supply their content. |
| Definition-root traversal through Lambda/body and Block final | Original child indices, local declaration boundaries and distinct expression components remain available. Lambda recipe retains parameter/root/body endpoints (`candidate_source.rs:445–459`); Block retains local initializers and final expression. | Lambda constructs Function typing (`lib.rs:11233` onward); Block emits Group(final,result) (`candidate_source.rs:462–470`), admitted as child <: result (`shadow_apply.rs:1331–1334`). | No retained definition-root ownership summary traverses these body boundaries. These typing forwards neither install root-owned Name incidences nor select independent Lambda/Block row adjacency. Apply traversal across these boundaries remains outside its approved membership rule. |

Parameter references need the actual formal endpoint, module references the
resolved module root, and local references the installed/open local root.
Name occurrence components, original roots, fresh description roots and Apply
result rows remain distinguishable. The current borrowed Call observer checks
authentic owner, operand indices, scopes and native demand ports
(`candidate_call.rs:282–341`); its pending supplier list (`:213–245`) explicitly
leaves complete Call construction unresolved. It does not certify graph edges.

## Retention, transport and consumers

| Stage | Existing producer → consumer | What is retained / missing |
| --- | --- | --- |
| Module source scheduling | `lib.rs:1124–1135` → `emit_candidate_source`; `candidate_scheme.rs:842–902` schedules module definition SCC members, activates internal roots/uses, then captures graphs. | Module dependency scheduling is distinct from Value-reference SCC qualification. It does not include E as a separate module member or recover E-owned initializer incidence. |
| Source Name transport | Module action → `route_candidate_open_use`/incoming (`candidate_source.rs:672–676`); internal route uses target-root and Name-use components (`lib.rs:15765–15782`). Local action → `route_candidate_local` (`candidate_source.rs:680`). | Original binder identity can be joined from retained HIR and binding maps. The resulting subtype admission/fresh use does not emit the approved Apply or definition owner reference. |
| Extrusion | `candidate_extrusion.rs:90–162` snapshots the selected bound side, allocates a polarity/target-specific row, calls `retain_extrusion_parent`, and copies that side's payload. | Actual parent provenance is retained at creation. No selected source-incidence payload exists to transport. Bound copying therefore establishes no source-reference target law for either original or copy. |
| Shared anchors / fresh descriptions | `candidate_scheme.rs:36–108` Graph retains rows, Function nodes, bounds and contextual evidence; `:307–321,567–574` marks eligible rows above boundary and stops expansion at older anchors; `:1008–1020` remaps canonical rows once; `:1500–1518` restores bounds before final root-to-use admission. | Existing freshening coherently transports its retained algebra and contextual evidence. Graph has no approved source-owner incidence field. The original resolved binder and a per-use description root are not interchangeable; no source-incidence transport theorem follows. |
| Contextual attachment transport | `candidate_context.rs:650–659` retains source bundles and relation↔attachment-bundle incidence. | This is typed effect/checking attachment evidence, not owner-Value→resolved-binder incidence. Similar terminology supplies no graph bridge. |
| SCC qualification | `candidate_intrusion.rs:358–488` scans direct/exact lower and upper Value/Effect bounds, Function ports and Effect algebra tails, then checks retained parent endpoints in computed components. | It never reads LocalSource, ApplySourceInput or definition-owned Name incidence. Parent metadata supplies no edge. No level-equality qualification filter appears in this check, but that does not establish the correct graph. |
| Parent equality | `candidate_intrusion.rs:513–605` merges copy into actual parent, transfers both bound sides/origins, combines level/non-generic metadata, canonicalizes and replays lower bounds. | Equality affects live solving. Its trigger uses the scanner graph above; qualification against the approved graph and equality preservation remain unproved. |

The first gap is construction, before extrusion, capture or SCC discovery.
Later operations cannot establish a missing pre-dispatch incidence merely by
successfully transporting their different retained payloads.

## Smallest source-shaped evidence and supported portions

For `my invoke f = f 1`, let F be its actual formal and R the Apply result.
Under successful authentic formation and the normal same-level prefix with no
prior bounds/equalities on F/R, the retained typing is F <: Function−(...,R).
The earlier [Apply transport audit](2026-10-12-apply-reference-transport-audit.md)
already derives a scanner path F→demand→R while R has no outgoing payload at
that cut. The approved incidence is R→F. This audit reuses that finite
discriminator; it runs no additional toy model and claims no executed
counterexample or actual parent merge.

For nested membership, `my use f = f(0)(0)` gives a stronger construction
check: require R1→F and R2→F with F's original resolution, rather than checking
only outer callee R1. Static HIR CallTail/Apply constructors support the shape;
this exact text was not parsed or solved here.

The supplied carrier-shaped analogue
`my odd n = { my even n = odd(n); even(n) }` additionally requires E→O from
the local initializer and O→E from the outer final expression, as well as
inner Apply R→O,Q and outer Apply S→E,X. Q and X are distinct shadowing
formals. This is conditional on successful authentic formation; it is not
the user's exact conditional/indented source. The existing [native extrusion
audit](2026-10-12-odd-even-native-extrusion-audit.md) retains actual pairs
(cQ,Q) and (cR,R) in a prefix. O/E membership does not qualify either pair.

An exact current fixture can exercise a portion of the map:
`my id x = x; my first = id 1`. Existing code in
`shadow_apply.rs:1480–1496,1508–1556` forms this text through the explicit
shadow-applications HIR entrypoint and through LocalSource, solves the candidate,
and checks one authentic source Call on the latter route. It covers direct
formal Name identity, module root/Name use and direct Apply inputs. This is
static evidence from existing assertions, not a newly observed test pass,
default/public admission claim, nested-boundary coverage or graph correctness.

The exact odd/even admission obstruction is reused from the reviewed
[source admission audit](2026-10-12-odd-even-source-admission-audit.md) and
`tasks/current.md:10992–11011`; no parser/operator-environment experiment or
repeat admission investigation was performed.

## Evidence limits, resources and next owner

No executable oracle/checker was used, so oracle independence is inapplicable.
The hand characterization shares the actual candidate transition rules and
successful-carrier assumptions of prior notes. It locates missing source
records directly; it does not independently prove those rules sound. No seeds,
ranges, mutations, tests, builds, probes or heavyweight samples were run.
Abnormal paths, complete Call, exact conditional/infix admission, full later
histories, source-reference transport, parent qualification, soundness,
principality and public/F5 cutover remain unverified.

Four lightweight read/check command sessions were opened, sequentially. The
primary approved a one-session extension from the original three-session
budget after an initial broad read truncated and an unprefixed source path
failed. The fourth session served bounded reads and checks and is closed at
handoff; its dependency comparison uses read-only Git subcommands. Truncated
decisive windows were reread narrowly. Zero heavyweight processes/samples;
CPU, peak RSS and exact reasoning wall time were not measured. The 30-minute
assignment bound was not intentionally expanded. Requested role/method:
complementary source-correspondence researcher. Effective model/effort metadata
was not observable; no override or delegation occurred.

Recommended next action: the primary assigns the source-construction owner a
bounded packet for canonical owner/occurrence/scope/resolved-root incidence at
`emit_candidate_source`, including nested Apply operands and definition/local
initializer ownership. Keep separate the proof of its transport and the SCC
consumer change; the implementation gate needs explicit authorization and the
decisive invariant before dependent production work.

## Dependency snapshot and commit packet

All 21 direct dependency files compared byte-for-byte with the pinned baseline
matched. No dependency was edited by this worker. The compiler sources shared
with the preceding Apply audit have the same hashes. Relative to older odd/even
snapshots, `shadow_apply.rs` is `cbd2e0c4…` rather than `230ed70…`; its current
Apply admission and receiver windows were read directly. The parent-copy
authority is now `fd07ecc7…`, incorporating the later accepted nested-Apply
and definition-root decisions; older notes' remaining-decision claims do not
override those selections.

Direct SHA-256 snapshot:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-local-self-recursive-binding.md` | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-09-20-binding-body-definition-root-directed-subtype-draft.md` | `1c51fd38996eb8921eda36ff3c49f12e5c4b23b398b9c2b75de7db69954420a6` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `notes/progress/2026-10-12-apply-reference-transport-audit.md` | `e68af78c615b128fe419fbfa5d66a283c105f8770a8031b28dd514cb752995dc` |
| `notes/theory/2026-10-12-apply-reference-construction-proof.md` | `16d7c66828698992b36dcf1a6d8890303d10d6ed24809cd8da25ba8d1aa9e91a` |
| `notes/theory/2026-10-12-odd-even-native-value-row-bridge-proof.md` | `3812f87e7d0a83dcc6d65470a8274bdcb6d6c79f3f0655840c835d01a7802fc6` |
| `notes/progress/2026-10-12-odd-even-native-extrusion-audit.md` | `9c44f9220a43631b7bb7e6723b5f777c3f467242e68ff2dcbb19df73e846cec0` |
| `tasks/current.md` | `b7fafcdee4e091c3c337382331be8d841c7bbaf5213d7993acf91027f6ef509b` |

Checks: static constructor/consumer windows and locators; baseline branch/SHA;
SHA-256 plus `git show <baseline>:<path>` byte comparison for the 21 inputs;
local Markdown target existence; `git diff --no-index --check /dev/null` on
this exact note. No compiler/test command or Git mutation was run. Final
check results are reported to the primary with the frozen artifact.

Commit packet:

- Exact changed lease: `notes/progress/2026-10-12-value-reference-source-bridge-audit.md`.
- Baseline SHA: `c2b38446c445f5f932aabe8253daf8fc1d0110d8`.
- Changed dependency hashes relative to baseline: none; historical differences
  are explicitly recorded above.
- Claim/review: bounded static characterization; unreviewed research checkpoint;
  no theorem closure or independent self-review claim.
- Checks already run: the narrow static reads and dependency comparisons above;
  final local-link/whitespace outcomes accompany submission.
- Proposed message: `research: map approved Value owners to the first source bridge gap`.
- Shared-record deltas left to primary/curator: identify Apply incidence emission
  and definition/local owner retention as the first construction premises;
  retain original-root versus fresh-description identities; keep transport,
  correct SCC qualification, equality preservation and production gates OPEN.
  No shared task/index/authority/question record was modified.

Writes stop before submitting this artifact for frozen review.
