# Independent review: regular graph completion and preservation

Date: 2026-10-26. Reviewer: `/root/regular_completion_review`.
Producer: `/root/regular_completion`; reviewer had no construction role.
Mode: M3, one assigned fresh reviewer, one review pass, 900-second ceiling.
Baseline: `eb3eef2f6a29d9c2a6132d648866c60900db276c`, branch `yulang3`.

## Decision

**ACCEPT. No BLOCKING, major, or minor findings.** This accepts the two frozen
modules' stated intermediate mathematical result and their application to the
existing regular-publication theorem. It does not certify the original
whole-source inference theorem, a native implementation, or the separately
owned `SimpleSubRegularDecision` module.

The substantive advance is established: from an initially valid finite regular
graph and actual variable-reference/row-shape/label-uniqueness evidence, the
executable construction adds the missing finite constructor inventory and
derives successful decoding by the original decoder. Existing graph identities,
cycles, successful decoding, and old semantic/history/certificate evidence are
preserved. The caller no longer supplies the desired successful inventory
decoding equation.

## Frozen review inputs

The hashes were independently recomputed and matched the issued packet.

| Input | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubRegularGraphExtension.lean` | `0b45d0e6d58701cba9f7df00d2a63897327e357ed3047b36e96d8fb6c49893d8` |
| `notes/theory/lean/YulangClosure/SimpleSubRegularCompletion.lean` | `d7231d0a3695dba7f3102e5fe235d4d26e34cad78870dbdbae9b7633c42787aa` |
| `tasks/agent-loop/inbox/20261026-inference-regular-completion.md` | `34ae025afa95994b5f2796ea78d72d12870fa32f2e267415be45a8e79bf59ed7` |

The complete ten-module local import cone (the two new modules and eight
pre-existing dependencies) was traversed from the actual import declarations.
Every source file was byte-identical to its checked isolated-project copy. The
eight dependency hashes also match the producer's frozen handoff. No dependency
on `SimpleSubRegularDecision` is present.

Governing material read: root `AGENTS.md` and `AGENTS.pre-sprint.md`; the Lean
proof skill and its source/execution references; goal-driven sprint, design
authority and review-budget rules; top-level inference principles; the selected
birth-level SCC correction; the original source-preservation statement in
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` section 1;
`docs/yulang-whole-proof-closure-ja.md` sections 1 and 4; the previous regular
publication handoff and current “Final connection” progress section. Review
used the actual `Contracts`, regular graph, decoder, and history definitions,
not their success receipts as semantic authority.

The unchanged parent remains `YulangClosure.SourceProblem.InferenceSoundness`:
for every supported source `s`, scope `x`, generated problem `d`, and solution
`a`, successful solving must produce one `e` satisfying both the original
`sourceJudgment s x e` and `sameScoped s x e a`. The new theorem does not supply
that source judgment or identify its graph interpretation with the complete
source witness.

## Mathematical and source-correspondence review

### Exact preservation, including cycles

`RegularExtension.Extends` is the literal per-kind list-prefix relation
`∀ k, ∃ suffix, target k = source k ++ suffix`. Its lookup theorem therefore
preserves the actual node at each existing identity, including back edges and
self cycles. The first-exact-match proof for `findList` preserves the original
returned identity even when the suffix contains duplicates. This is the
necessary stronger fact for the original decoder's search-based constructors.

`Extends.regular` transports successful expansion and applies the existing
coinduction theorem to the independently defined all-depth `RegularSub`.
It does not redefine regular satisfaction as certificate acceptance.
`Extends.step` covers all eight actual `ConstraintStep` constructors, and its
extrusion helper covers all three actual `Extrusion` constructors. The same
occurrence list, selected copy pairs, Value-reference relation, and immutable
birth function are retained. The type-graph extension does not change the
selected source-Value qualification rule.

`Extends.certificate` preserves one-step certificate closure. Its stronger
`Extends.accepts` and `Extends.check_store` correctly require target validity:
the acceptance predicate checks the entire target graph, including appended
nodes. The completion theorem derives this required validity. No converse
preservation or preservation of unsuccessful lookup is claimed.

### Completion premises and construction

`Lawful` contains actual correctly kinded variable lookups, inductive child
legality, the actual required tail/payload shapes, and fresh record labels or
variant tags. It contains neither decoder success nor subtype, certificate,
history, semantic model, or arbitrary preservation assumptions. Existing
row-tail and tuple-payload variables are admitted through their looked-up
nodes. `Shape` retains the exact ordered label/tag list needed by the cons
cases, while graph validity supplies uniqueness for an existing row node.

The duplicate-label/tag requirement follows the frozen `Node.uniqueLabels` /
`Node.Valid` definition. It is not an invented restriction presented as full
source coverage. Tuple elements and variant payloads remain ordered lists;
record optional bits are copied exactly. The Function construction sequences
all four ports in the correct value/effect/effect/value kind tables.

`intern` reuses the earliest exact node or appends one node to its own kind
table, returning the old table length. `intern_spec` proves extension, validity,
and successful exact search from this implementation. `completeTerm_correct`
uses the stronger induction invariant that its current graph extends the base
graph supplying variable witnesses. This allows sibling constructions to share
one accumulating graph. Each child's earlier successful decoding is transported
to the final graph before the original constructor decoder is applied.

The row cases obtain the actual tail/payload lists from `Built.represents`,
derive node validity from those looked-up nodes and freshness, and intern the
exact resulting whole node. This constructs the missing nil, finite suffix,
tuple payload, atom and Function nodes instead of assuming they already exist.
The private `intern_build` equation premise is discharged definitionally at its
six leaf call sites; it is not exposed as a caller-supplied completion premise.

### Exact main claim and joint application

The audited fully qualified theorem is
`YulangClosure.SimpleSub.RegularCompletion.completeTerm_correct`. For every
`base`, `refs`, kind `k`, term `term : Term k`, and shape, it takes
`Lawful base refs term shape`; for every current graph, `Extends base graph`
and `graph.Valid` then yield `target`, `identity`, the actual equation
`completeTerm graph refs term = some (target, identity)`, and
`Built graph refs term shape target identity`. `Built` explicitly contains
extension, target validity, original `decodeTerm` success, and the exact
resulting node shape. The printed type matches these source declarations.

`completeStore_correct` applies the same invariant to all lower/upper endpoints
and the entire finite list. `completedStore_correct` specializes it at the
initial graph and rewrites using the proved successful execution equation.
Consequently the `getD (graph, [])` failure default is unreachable under initial
validity and `LawfulStore`. There is no claim that arbitrary unlawful inputs
produce a valid graph or that the unguarded executable function rejects every
such input.

`completed_history_store_sound` directly supplies the derived decoding equation
to the unchanged `history_store_sound`. `completed_publication_with_clients`
completes exactly
`inventory ++ clients.map (Constraint.rename (publicationTransport ...))`.
It then supplies the derived equation to the existing
`publication_history_with_clients`, retaining all boundedness, inactive-image,
stopped-closure, capture/use guard, finite-use, and syntactic-coverage premises.
Both conclusions use the same constructed graph and the same composed
reference assignment `fun k i => refs k (publicationTransport ... k i)`.
No separately chosen model or reference assignment is introduced per use or
client. The actual regular history and terminal certificate acceptance remain
explicit inputs.

The independently lawful sparse example checks the intended missing-node
case and preserves the existing cyclic `function 4 0 0 4` node. The main proof
is general induction; the example is supplementary evidence, not its basis.

## Checker and axiom evidence inspected

Per the packet, no new Lean/build invocation was run: no concrete flaw required
a repeat. Review inspected the complete successful `check07.log`, the actual
per-origin audit driver, printed principal theorem types, and all 291 axiom
records in `audit02.log`. A read-only parser verified 291 unique begin/end
blocks in matching order, exactly one corresponding axiom record for each,
matching module totals, and no audit error. The audit enumerates constants by
environment origin module, including private helpers and generated declarations;
it rejects originating project axioms and disallowed transitive axioms.

| Module | Originating constants | Theorem constants |
| --- | ---: | ---: |
| `SimpleSubRegularGraphExtension` | 42 | 36 |
| `SimpleSubRegularCompletion` | 249 | 137 |
| Total | 291 | 173 |

Actual axiom distribution across all constants: 151 with no axioms, 119 with
`[propext]`, and 21 with `[propext, Quot.sound]`. The main completion/store/
publication theorems use `[propext, Quot.sound]`; no `Classical.choice`,
`sorryAx`, native-evaluation assumption, or project axiom occurs. A source
shortcut search over the entire local import cone found only the harmless
word “external” in a `Contracts` comment and no proof-hole/checker-bypass source.

The project files still pin Lean 4.35.0, `-j1 -M1024`, and no external packages.
The producer's final build receipt reports both target modules built
successfully. This is reviewed producer execution evidence, not a claim that
the independent reviewer reran the checker.

| Evidence | Independently recomputed SHA256 |
| --- | --- |
| `inference-completion/check07.log` | `2e9a9b0e6ac3d317673c566d3820a7fd743060202164ac60a7fb739eba05c1ed` |
| `inference-completion/audit02.log` | `22159635d6d34a1be7787afed73f0783e027fc9e88f06de299686d31c9f82d32` |
| `inference-completion/project/AuditCompletion.lean` | `b94896c2ab2b1f90ed77e65889d3ebbe5732c8cc54f11c605d03bf7613a89540` |

The evidence paths above are relative to `/workspace/scratch/f98087c7ac1a/`.
All match the frozen producer receipt.

## Closure boundary and cessation

Union/intersection completion explicitly returns `none`; there are no alias
nodes. Exact finite ordered row carriers do not establish full native
width/presence/matching or coalescing semantics. Existing cycles are retained;
the construction does not synthesize an arbitrary cyclic satisfying model.
Native reference/initial-validity extraction, `LawfulStore` for actual generated
inventory, publication metadata, the concrete history and terminal acceptance,
full constructor coverage, and the original contextual Call/effect/source
witness remain with their existing owners. The separately owned Decision
module and root/default-target integration were outside this review.

The producer's handoff states these limits accurately. No original source
domain or original parent quantifier was changed, and no production algorithm
or performance claim is inferred from this proof-side finite completion.

Only this leased review file was written. No source, shared status, import,
Git state, build/cache, producer evidence, or other worker output was changed.
No children or background processes were started. **WRITES STOPPED** after this
review receipt; primary owns adjudication, integration, and status updates.
