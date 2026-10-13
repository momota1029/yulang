# Native bulk bound owners: static construction boundary

Date: 2026-10-13
Status: independently reviewed bounded research characterization; no parent closure
Baseline: `9a30a208bd23b9b84cd601934b4b9697f051eca2`
Branch assigned: `research/simple-sub-intrusion`
Method: independent static constructor/consumer audit; no executable probe
Lease: this new note only

## Objective, authority, and result

Inspect the actual Rust bulk writes relevant to repaired Lemma 1 in
`notes/theory/2026-10-11-simple-sub-rebuilt-core-proof.md`, especially its
initial-coverage and bulk-coverage premises. This packet is complementary to
constructive proof work; it does not inspect or coauthor that producer's draft.
The governing sections are the rebuilt-core note's **Lemma 1**, **Source-relevant
bulk accounting**, and **Bounded repair of Lemma 1**; top-level inference
principles §§1–3 and successful-suspension clause; contextual attachment design
§§3–4, particularly Extrusion, Opposite replay, Capture/freshening, and SCC
intrusion; and compiler-engineering **Natural compiler behavior and
proof-obligation economy**. Research-lab and Git-concurrency rules govern the
lease and checkpoint, without adding semantic authority.

Result: the smallest inspected extrusion boundary retains the induced comparison
as a copied bound. Absence of a direct replay operation therefore is **not** a
bug, a source counterexample, or evidence of lost native work. The source does
not itself supply a proved joint disposition law for the original owner's new
incidence pair. This audit stops at that law boundary. It establishes the owner
matrix below, not impossibility of such a law, general coverage, or theorem
closure. No eager satisfiability check, all-pair registry, source restriction,
or new compiler architecture is proposed.

## Changed operational input and method

Bounded searches/readings used the existing contextual-bound-fiber replay
checkpoint (2026-10-10), mixed-replay observer construction (2026-10-10),
transactional retained replay foundation (2026-10-11), and inference-rebuild
native-spec proof (2026-10-11). Those respectively characterize activated
fiber products, observer construction, retained child completion, and the
repaired initial/bulk boundary. This packet instead starts at physical writes
that bypass opposite replay and follows their compensating retained-bound
consumers. It does not repeat detached mixed algebra, scheduler receipt
accounting, or a conjecture about persistent polar memo tables. The maps in
`candidate_extrude` are fresh invocation-local variables.

## Physical write and owner matrix

All citations below refer to the pinned source. Positive means lower storage;
negative means upper storage. A physical insertion emits an admission and
`PhysicalBoundSlot`; it does not automatically begin opposite replay.

| Write owner / source | New pairs and compensating route | Established boundary / remaining premise |
| --- | --- | --- |
| `lib.rs:10059,10075,10094,10156,10187`; `candidate_scheme.rs:675–688` | Collected/fresh rows use default empty bound stores; starting the candidate graph initializes its graph/context state. Empty individual allocations have no opposite pairs. | This covers those allocation owners, not every later initialized source graph or initialization route. |
| `candidate_extrusion.rs:96–162`, parent link at `:123` | Snapshot selected-side lengths, allocate target-level copy, retain actual parent/polarity/target, then insert the opposite-side copy link at the old parent. Every existing selected parent bound forms a new pair with that link. `Work::Bound` visits/extrudes each snapshotted endpoint and stores the result on the copy's selected side. | The induced comparison is represented at the copy. No explicit parent-pair replay is begun here. Its lawfully represented/transported disposition and dependencies require a separate argument. |
| `candidate_extrusion.rs:309–327`, `Work::Bound` | Stores selected-side copied bound and transfers individual origins/fibers. A newly allocated isolated copy has only this bound side. | No local cross product exists in that isolated case. An unconditional one-sided-copy claim is invalid when incoming allowance admissions also reach the copy or a shared row. |
| `candidate_extrusion.rs:164–176,293–307`, `IncomingAllowance` | Positive effect-tail traversal follows capture incidence, visits its source, remaps the view to the copied tail, inserts an upper Allowance at the mapped source, and transfers origins. | The mapped source may be an older populated shared row or the positive copy already receiving selected lowers. New local opposite pairs are possible. This branch has no direct replay; individual transport is not a joint mixed-context disposition proof. No failing source witness is established. |
| `candidate_scheme.rs:965–976,1006–1019,1221–1266`; local retained adapter `:1511–1515` | Fresh-use preparation allocates empty generic rows or shares canonical older/nongeneric rows. Both saved sides are admitted **sequentially** through `begin_candidate_fresh_bound` and `candidate_begin_bound_restoration`; this is not a Rust assignment of two populated sides. | Each admission owns a restoration handle and opposite snapshot. Per-use terms, rows, contexts, bundles, and evidence share one preparation. Full completion across reentrancy/redirects remains separate. |
| `candidate_extrusion.rs:659–678,694–760` | Restoration stores first, captures opposite count, and retains owner, side, bound, emission, index, active replay, occurrence and cause. The next step rereads canonical owner/endpoints and begins replay with ordered bound inputs. | This is an activation/continuation owner. Saved count with live index across mutation needs its own preservation argument; it is not blanket inherited-completion transport. |
| `candidate_intrusion.rs:513–606` | Merge appends both copy sides to parent, transfers individual origins, moves capture incidence, redirects the representative, canonicalizes third-owner fibers, then replays **every current parent lower against current uppers**. | A direct insertion alone is compensated by the subsequent explicit merged-owner product replay. Equality validity, third-owner prior-completion invalidation, and suspended-input conservation are not proved here. |
| `candidate_effect.rs:1465,1496,1567`, signature effect ports | Each direct Support/Allowance admission targets a newly allocated effect port. Tail/capture incidence is separately registered. | That fresh port admission has no local opposite side. Its tail relationship is not completion of an arbitrary opposite pair at the tail. Later source checks use ordinary owners. |

The common physical owner is `candidate_insert_bound_with_evidence`
(`candidate_extrusion.rs:406–567`): it canonicalizes endpoints, retains origin
and relation, appends one lane entry, registers capture incidence when requested,
marks intrusion dirty, and emits the physical slot. The macro does not deduplicate
physical bound emissions. `BoundKey` identifies owner/side/item; fibers and
physical slots provide additional incidence evidence. Endpoint equality alone
does not equate all physical incidences or prove processing completion.

Ordinary application is different: `candidate_apply_value` / `candidate_apply_effect`
(`candidate_extrusion.rs:808–865`) insert and immediately invoke
`candidate_replay_bound`. The latter snapshots opposite count, constructs ordered
lower/upper `BoundKey` inputs, begins replay and drives it. Driver return can mean
queued children rather than completed semantics (`candidate_context.rs:3108–3123`).
The retained parent and typed drain own actual completion, including successful
suspension. No abnormal full-rollback theorem is imported.

## Minimal constructor-boundary trace, with compensation

Hypotheses: a candidate-enabled private session with available allocations;
canonical distinct value rows `a` at level 1 and receiving row `b` at level 0;
no qualifying parent-copy intrusion event in this trace; and identity contexts
for this pure illustration. The real row allocator makes empty rows. An ordinary
`candidate_apply_value({ lower: IntPositive, upper: ValueRow(a) })` stores
`IntPositive` in `a.exact_non_variable_lowers`; its opposite count is zero.

Construct positive Function `F` through `positive_function_term`, with argument
`TopNegative`, argument effect `EmptyEffectNegative`, result effect
`BottomPositive`, and result `ValueRow(a)` in positive position. All leaf ports
are unchanged by extrusion. Dispatch the actual task
`Value({ lower: PositiveFunction(F), upper: ValueRow(b) })`.

1. The production dispatch branch at `lib.rs:12414–12427` invokes
   `candidate_extrude(PositiveFunction(F), Positive, value_levels[b])`.
2. The result port visits `(ValueRow(a), Positive, 0)`. Its selected bound
   snapshot is one exact lower, no direct lowers. Allocate `c` at level 0;
   retain `(copy=c,parent=a,Positive,target=0)`.
3. At extrusion `:123`, append `c` to `a.direct_upper_rows`. The new parent
   incidence pair is `(owner=a, old lower-slot IntPositive, new upper-slot c)`.
4. The sole `Work::Bound` stores `IntPositive` in `c.exact_non_variable_lowers`
   and transfers the old bound's individual fibers/origins to the new bound.
   The exact induced comparison `IntPositive <= c` is now a retained native
   bound. Its existence is the compensating route; there is no missing
   comparison endpoint in this pure trace.
5. Rebuild `F` as `F'` with result `c`. Dispatch records the original-to-rewritten
   diagnostic edge and queues `F' <= b` (`lib.rs:12445–12462`). That task stores
   `F'` at `b` and uses ordinary insertion/replay. There is no explicit replay
   operation for the original parent incidence pair in steps 2–4.

This embeds the row in an actual Function child; a naked call to private
`candidate_extrude(a,Positive,0)` would not establish production dispatcher
reachability. This is a static trace through real production constructors and
the candidate dispatch branch. It has not been executed. A parsed/HIR source
program reaching these exact rows/levels/ports through the public candidate
facade is **not established**. Removing the sole lower makes the tested parent
product empty; removing the level difference prevents the copy. Thus this is a
minimal nonempty parent-product illustration, not a minimized semantic failure.

The symmetric negative construction copies selected uppers and induces the
corresponding lower-copy link; this audit reads the shared branch, but does not
claim a separately source-admissible negative example.

## Consumers and precise stopping premise

The copied bound has concrete future consumers. Ordinary upper insertion at
`c` reads its lowers through `candidate_opposite_count/bound` and replays them
(`candidate_extrusion.rs:569–630,763–803`). Capture enumerates the copied row's
actual bound storage and fibers (`candidate_scheme.rs:523–565,569–666`), and
freshening restores it through the per-use restoration owner. Intrusion, if
independently qualified, also reads those stored bounds and explicitly replays
the merged product. These routes explain why lack of direct parent enqueue is
insufficient to diagnose a bug.

No inspected native consumer performs a global census requiring a distinct
completion tag for each original physical opposite pair. For the pure Int
example, insisting on such a tag may be reconstruction bookkeeping (class D),
not an established compiler requirement. Lemma 1's stated exact-pair premise
nevertheless remains unchanged; this audit does not weaken it.

There is a real joint-context consumer for **activated** replay. At
`candidate_context.rs:2911–2991`, each lower/upper fiber pair produces ordered
`ContextExpr::Replay`, or `IDENTITY` when both input contexts are identity,
and ordered `Dependency::Replay { lower,upper,lower_input,upper_input }`.
The zero-word filter consumer inspects both ordered Replay branches
(`:2668–2698`) before checks and retained discharge (`:2750–2811`). This shows
joint contexts can matter to actual checks; it does not show that the pure
trace needs an additional pair tag, nor exhibit a failure of its compensation.

Individual transport iterates each old bound fiber
(`candidate_effect.rs:563–605`), retaining a single-bound witness and dependency
(`candidate_context.rs:3182–3197`). The origin-table fallback explicitly records
`MissingOriginAssociation`. That declared evidence gap is not itself a lost
runtime obligation. Transport does not construct the joint Replay product.

**First unproved law / stop:** justify, for an actual extrusion event, when its
copied-bound representation supplies a valid disposition of the original
parent-link incidence pair, preserving all context/registration and consumer
dependencies that actually matter. Its premise must come from the construction
and consumer owners, not from assumed transition rules, mere copied origins,
or transitive semantic entailment. The pure trace is compatible with such a
law. The allowance branch identifies a further direct write seam but is not
used to spin another conditional theorem or claim a counterexample.

Canonicalization transports third-owner fibers before merged-owner replay;
restoration rereads canonical endpoints while retaining a saved opposite count.
These are inspected hooks, not a proved joint remap, reentrant scheduling,
suspension, or dependency-invalidation law. Those cases remain uncovered by
this packet's conclusion.

## Checks, resources, and exclusions

Checks performed: bounded `rg` inventories of all named insertion/extrusion/
restoration/replay call sites in the assigned modules; direct `sed` source
reads; bounded prior-note comparison; read-only `git rev-parse HEAD`,
`git status --short`, and `git diff --name-only <baseline> -- <dependencies>`;
SHA-256 dependency snapshots. HEAD matched the pinned baseline, and the
dependency diff inventory was empty when inspected. Test-module hits after
`candidate_effect.rs:1590` were excluded from production-owner conclusions.
An attempted `candidate_value.rs` lookup reported that no such file exists;
the actual value owners are in `candidate_extrusion.rs` and `lib.rs`.

No executable oracle, seeds, ranges, mutations, builds, tests, formatting,
measurements, Git mutations, or child launch occurred. Oracle independence is
not applicable: this is direct static source evidence, sharing the selected
authority and pinned source with the constructive lane while using an
independent write-to-consumer method. There is no differential executable
validation. Zero heavy processes; small read/hash commands only. CPU/RSS and
exact wall time were not measured; the assigned wall bound was 18 minutes.
Requested/effective model and effort were not exposed to this leaf as runtime
metadata and are unknown.

Complete source admissibility, Call, carrier construction, L4, global
termination, general contextual execution, mathematical soundness/principality,
and production/default/F5 cutover are excluded. No independent review of this
artifact has occurred.

Recommended next action: primary apply the independent constructive lane's
copied-bound disposition result to the exact constructor/consumer seam above;
require a separate owner-qualified bridge only for the context/registration
dependencies it uses. Preserve OPEN status where that bridge is missing;
do not introduce an all-pair runtime census from this static illustration.

## Frozen dependencies and commit packet

Content SHA-256 at source inspection:

```text
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
08f178b448c711c43938ec26dd438c18bbee5d47ee4d11f1a03d2e88839f6597  notes/theory/2026-10-11-simple-sub-rebuilt-core-proof.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b  notes/design/2026-10-10-parent-copy-scc-intrusion.md
```

- Exact leased/changed path: `notes/progress/2026-10-13-native-bulk-pair-owner-audit.md`.
- Baseline SHA: `9a30a208bd23b9b84cd601934b4b9697f051eca2`.
- Changed dependency hashes: none at inspection; primary rechecks before integration.
- Claim/review status: frozen unreviewed static characterization, no source counterexample or gate closure.
- Checks already run: the static inventories, cited owner/consumer reads, prior-note comparison, baseline/dependency diff and hash inspection above.
- Proposed commit message: `research: map native bulk bound owners and copied-bound consumer boundary`.
- Shared-record deltas left to primary/curator: link this source-owner matrix from `tasks/current.md` and the relevant theory dependency record if accepted; distinguish represented copied-bound disposition from activated replay; retain original Lemma 1/native bridge gates OPEN until actual missing premises and independent review close them. No shared file was edited.

## Primary review and consumption

One fresh independent `compiler_referee` reviewed this frozen owner audit and
the [constructive route](../theory/2026-10-13-native-bulk-bound-coverage.md).
There were no BLOCKING or major findings. The primary applied the sole minor
source correction: two identity contexts produce `IDENTITY`, while ordered
inputs remain retained in `Dependency::Replay`. Explicit Replay-node existence
is therefore not added as a proof premise. The original producer status and
commit packet above describe its pre-review handoff.

The actual copied-bound route is consumed as evidence for rebuilt-core Lemma 1's
bulk-construction seam. It does not discharge the original joint disposition
law, source admission, universal incidence coverage, Call, L4 or inference/F5
parents. No runtime registry, eager solve or replay change follows. Shared task
and research records are synchronized by the primary; checks of this minor
textual delta are whitespace, links, fences and unchanged dependency hashes,
with no repeated build, test, probe or measurement.
