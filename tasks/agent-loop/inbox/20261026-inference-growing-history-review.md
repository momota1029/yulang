# Independent review: completion through growing regular histories

Assignment: `20261026-inference-growing-history-review`, revision 1.
Reviewer: `/root/regular_decision_review`, fresh non-author of this integration
module; no contribution to its construction or repair. No descendants.
Producer: `/root`. Mode: M3, one assigned independent reviewer for this artifact.
Original dependency baseline: `eb3eef2f6a29d9c2a6132d648866c60900db276c`.
Branch: `yulang3`; primary reports first published checkpoint `458f5e2`.
Requested model/effort: inherited runtime settings; observed launch metadata:
UNKNOWN. This is a new integration review, not a repeat or repair review of
Decision or Completion.

## Verdict

**ACCEPT. No BLOCKING, major, or minor findings.** Acceptance covers the exact
frozen growing-history construction, final-graph flattening, and conditional
store/publication applications. No repair or checker rerun is requested.
Original full source inference soundness and native correspondence remain OPEN.

## Frozen inputs and carried-forward reviews

All hashes were independently recomputed. Every source below is byte-identical
to its counterpart in the producer's isolated checked project at
`/workspace/scratch/f98087c7ac1a/inference-decision/YulangClosure/`.

| Source under `notes/theory/lean/YulangClosure/` | SHA-256 |
| --- | --- |
| `SimpleSubGrowingInference.lean` | `865b9eb4a64962182a22a9e507b98b1e7ab92ac143e4cbfea0b8570e39bb58ce` |
| `SimpleSubRegularDecision.lean` | `6b6e5e6f1c45140d935e1aa29fba4c1303ae89cd91fd6e1cde0d37387148db8d` |
| `SimpleSubRegularGraphExtension.lean` | `0b45d0e6d58701cba9f7df00d2a63897327e357ed3047b36e96d8fb6c49893d8` |
| `SimpleSubRegularCompletion.lean` | `d7231d0a3695dba7f3102e5fe235d4d26e34cad78870dbdbae9b7633c42787aa` |

The eight original inference modules (`BirthLevelSCC`, constraint syntax and
soundness, generalization, regular solutions and constraint soundness, scoped
publication, regular publication), plus `Contracts`, were compared against
`git show` at the original baseline and against the isolated copies. All remain
identical. No acceptance is transferred to changed dependency bytes.

| Receipt | SHA-256 |
| --- | --- |
| Producer `20261026-inference-growing-history.md` | `0d691daf8e533758719dc1417f7aaebebd5d058bacda482b1229d0afede505d0` |
| Accepted Decision review `20261026-inference-regular-decision-review.md` | `a4989ad9a3a71e4733860852230c2031ec18d7640db8666f9b40ca5371cfce44` |
| Accepted GraphExtension/Completion review `20261026-inference-regular-completion-review.md` | `3e89a2e669ea564003706e950288c79fa9ca5162e75308e769909ff00e91030c` |

Receipt paths are under `tasks/agent-loop/inbox/`. The unchanged dependency
proofs retain their previous independent acceptances. This pass read their
actual definitions and theorem interfaces where needed for the new composition;
it does not claim a second whole-module review of those dependencies.

The governing repository/Lean proof rules, top-level inference principles,
immutable-birth correction, and original source-preservation claim read in the
preceding Decision review continue to govern this packet without alteration.

## Integration proof review

### 1. The evolving history contains the claimed concrete operations

`GrowingHistory ref birth graph first target last` is a finite inductive trace.
Its `step` constructor requires the existing `Regular.ConstraintStep` on the
actual current graph and chains the exact resulting state into the tail.
Its `grow` constructor requires `RegularExtension.Extends graph next` and
leaves the entire constraint state unchanged. `ref` and immutable `birth`
remain fixed parameters for every step and allocation in the trace.

The inspected `Extends` definition is the literal per-kind list-prefix
relation `∀ k, ∃ suffix, target k = source k ++ suffix`. It does not admit
rewriting old nodes or references, changing their kind, or renumbering old
identities. It permits finite suffix allocation, including a no-op suffix.
The new trace does not contain a supplied preservation theorem, satisfying
valuation, terminal model, or separately assumed final-graph history.

### 2. Extension accumulation and flattening use the correct graph

`GrowingHistory.extension` derives `Extends graph target` by induction. A
constraint step leaves the graph unchanged; a growth step composes its prefix
extension with the tail's extension; the empty trace supplies reflexivity.

`GrowingHistory.flatten` proves the exact existing relation
`ConstraintHistory target ref birth first last`. In the `step` case,
`rest.extension` relates the graph on which `change` was actually constructed
to the final `target`. Applying the accepted `Extends.step` therefore creates
that same concrete step on the final graph, and the induction hypothesis
supplies the rest of the final-graph history. In the `grow` case, allocation
changes no constraint state, so the already-flattened tail is the required
history. The empty case is the existing reflexive history constructor.

The dependency's `Extends.step` preserves all eight concrete step constructors,
including all extrusion constructors through its helper; it retains actual
occurrences, selected pairs, qualification evidence, `ref`, and `birth`.
There is no semantic implication substituted for a missing concrete history.
`GrowingHistory.append` requires matching intermediate graph and state;
`of_fixed` embeds the original fixed-graph history without extra premises.

These structural transport theorems do not assert that every intermediate
graph is valid. They do not need that assertion: the semantic application uses
validity of the common final graph, obtained from the terminal decision. Initial
validity is separately required by the completion theorem. This distinction is
consistent with the actual audited statements and producer's scope.

### 3. Computed terminal evidence reflects the original demands

The audited type of `GrowingHistory.decided_sound` takes only the actual
`GrowingHistory` and `decideDemands target last.obligations = true`; it returns
`Extends graph target ∧ target.Valid ∧ Holds target first.obligations`.
It applies the accepted `decided_original_demands` to `history.flatten`.
The same final `target` supplies its checked graph and all original demands'
independent all-depth `RegularSub` interpretation.

No terminal certificate parameter is reintroduced. The computed decision's
success is still an explicit premise, not claimed to hold for an arbitrary
terminal graph or arbitrary constraints. In particular, whole-target validity
continues to be checked even when terminal obligations are empty.

### 4. Completion really supplies the decoder equation used at the end

`completed_growing_store_sound` begins with an initially valid graph and
`LawfulStore graph refs store`. Its `result` is definitionally the executable
`completedStore graph refs store`. The accepted `completedStore_correct`
derives extension, validity of the completed graph, and
`decodeStore result.1 refs store = some result.2`.

The inspected `LawfulStore` uses correctly kinded variable lookups, constructor
legality, exact tail/payload shapes and fresh labels/tags. It contains no
successful-decoding equation or subtype/model premise. The completion default
`getD (graph, [])` cannot silently discard a lawful store under the theorem's
initial-validity and legality hypotheses: successful execution is established
by the already accepted completion theorem.

`history.extension.decode_store` then transports the derived decoder equation
from `result.1` to `target` with the identical `refs` and comparison list
`result.2`. The accepted transport preserves exact first-match identities, not
merely the existence of some decoded endpoints. The flattened history starts
at exactly those pairs and the supplied occurrence list. Composing the initial
completion extension with the history extension yields the reported
`Extends graph target`. The remaining conclusion is
`target.Valid ∧ StoreSatisfied target refs store`.

### 5. Publication and clients retain one final interpretation

`completed_growing_publication_with_clients` completes the exact common store
`inventory ++ clients.map (Constraint.rename (publicationTransport ...))`.
Its legality premise is for that entire combined store. The main type retains
all original boundedness, inactive-image, stopped-closure, capture/current-use
implication, finite-use and target-publication inventory-coverage premises.
Neither inventory coverage nor metadata closure is inferred from graph growth.

The proof supplies the derived final-graph decoder equation, the constructed
flattened history, and the computed terminal-decision success to the existing
`decided_publication_with_clients`. The conclusions use one `target` for both
original publication and all clients, and exactly the same reference assignment
`fun k i => refs k (publicationTransport n count afterUse q k i)` in both.
There is no per-client or per-publication witness/reference selection.

Consequently this theorem removes supplied decoder success and a supplied
terminal certificate from this combined consumer, and replaces its fixed-graph
history input with the explicitly indexed growing history. It does not claim
to construct the growing trace from native inference, prove every terminal
decision true, or reconstruct the original source judgment by itself.

### 6. The example exercises allocation between real constraint steps

`interleaved_history` starts with the old cyclic Function comparison, decomposes
it into the exact four child comparisons (including both effect ports), appends
`.tuple [0,1]` at the old value-table length 2, inserts a self-comparison on
that fresh identity, and discharges it with the actual looked-up tuple node.
`interleaved_decided` uses kernel `decide` on the resulting final graph and
remaining cyclic demands. `interleaved_original_solved` applies the general
growing-history theorem. The example does not supply a final pair certificate
or rewrite the original cyclic identities.

## Complete theorem-type and axiom evidence

All 140 source lines and every complete printed type/axiom entry were inspected.
A read-only parser additionally matched each unique BEGIN marker, exact printed
declaration, single corresponding axiom report, and END marker; checked all ten
source theorem names; and verified the eleven-entry trailer. The generated
`GrowingHistory.brecOn` theorem was included and its full dependent type read.

`GrowingAudit.lean` enumerates all originating `.thmInfo` constants, rejects
project `.axiomInfo` declarations, checks the three named integration roots,
and rejects disallowed transitive axioms. No type introduces an extra hidden
certificate, decoder-success, model, or final-history parameter.

Names below are relative to `YulangClosure.SimpleSub.GrowingInference`.

| Theorem | Origin | Complete axiom list |
| --- | --- | --- |
| `interleaved_original_solved` | authored | `[propext, Quot.sound]` |
| `interleaved_history` | authored | `[propext]` |
| `GrowingHistory.extension` | authored | `[propext]` |
| `GrowingHistory.of_fixed` | authored | `[propext]` |
| `completed_growing_publication_with_clients` | authored | `[propext, Quot.sound]` |
| `completed_growing_store_sound` | authored | `[propext, Quot.sound]` |
| `GrowingHistory.brecOn` | generated recursor theorem | `[propext]` |
| `GrowingHistory.append` | authored | `[propext]` |
| `interleaved_decided` | authored | `[propext]` |
| `GrowingHistory.decided_sound` | authored | `[propext, Quot.sound]` |
| `GrowingHistory.flatten` | authored | `[propext]` |

Thus all 11 entries match the claimed distribution: 7 with `[propext]` and 4
with `[propext, Quot.sound]`. There is no `Classical.choice`, `sorryAx`, project
axiom, or native-evaluation axiom. A focused source scan of this module and its
three new dependency modules found no proof-hole or checker-bypass constructs.

| Isolated evidence | SHA-256 |
| --- | --- |
| `GrowingAudit.lean` | `c249379bb196915e82036a8942d11709a0502f93cc892f8bf7738a8277f5742a` |
| `growing-check-01.log` | `c73225aac117b13d0081d5640c6fc59401eecd6d93a07bf0b23cea5f33b681d8` |
| `growing-audit-02.log` | `83ec5f4630b6f6ad9dc95e04eaa98edaff80c7083d62cb1da2a5bc23b686e4b3` |

The retained build reports successful completion of 13 jobs, including the new
integration module and its extension/completion dependencies. The producer
reports exit 0, 4.940 seconds for the build, and exit 0, 1.021 seconds for the
audit, using the established Lean 4.35.0 toolchain, one thread, `-j1 -M1024`,
and 120-second timeouts. These are reviewed producer execution receipts;
**zero checker/build reruns** were made in this independent pass. No concrete
gap required one.

## Original parent and closure boundary

The original `YulangClosure.SourceProblem.InferenceSoundness` still requires
an original source derivation and the same source-scoped shared witness from
every supported generated solution. This integration supplies a stronger
finite structural intermediate result; its conclusion is still regular graph
store/publication satisfaction, not that original source judgment.

The represented interpretation retains atoms, bottom/top, all four Function
ports, exact finite record/tuple/variant metadata and constructor-guarded cycles.
Union/intersection, aliases, native open rows, ordinary coalescing, mutable
physical rows, actual activation/native trace correspondence and complete
source Call/effect reconstruction remain outside this theorem. Literal prefix
growth does not establish arbitrary old-node mutation. No separate lattice
extension is imported or silently used, no original source cases are removed
from the parent obligation, and no production algorithm/performance claim is
made.

The next source/native owners must establish an actual lawful initial inventory,
initial references/validity, required publication metadata/coverage, an adequate
prefix-growing graph trace with these exact concrete constraint steps, and its
terminal acceptance. Native histories that overwrite canonical graph nodes need
their own faithful realization/correspondence; this result cannot certify them
merely by calling their mutation allocation. The original source-reconstruction
owner must still produce the complete shared source/Call/effect witness.

## Resources, uninspected scope, and cessation

Budget: 600 seconds maximum, zero checker calls; review began
2026-10-26 02:41:11 UTC. This pass covers only the frozen new integration module,
its exact dependency interfaces/identity, and the stated proof applications.
Previously accepted unchanged dependency internals, native Rust code, unrelated
proof lanes, root/default-target integration edits, and full-source realization
were not newly certified.

Only this exact leased review file was written. No source, other review,
shared state, import, configuration, build/cache, Git index/ref, or other
worker's output was modified. No scratch artifacts, child workers or background
processes were created. **WRITES STOPPED** at freeze; primary `/root` retains
adjudication, integration and status duties. The exact review-file hash is
returned separately rather than embedded self-referentially.

Freeze time: 2026-10-26 02:43:14 UTC.
