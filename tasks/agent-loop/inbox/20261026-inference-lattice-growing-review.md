# Independent review: lattice histories through graph growth

Date: 2026-10-26. Reviewer: `/root/lattice_growing_review`, fresh independent
nonauthor generic leaf, M3 single-reviewer packet. Producer: primary `/root`.
No child or coauthor contributed to this review. No effective model/effort
metadata is inferred from the generic role or repository configuration.

## Verdict and frozen scope

**ACCEPT. No mathematical, source-correspondence, axiom, or evidence findings
in the frozen packet.** This accepts literal-prefix transport, locally indexed
growing histories, and their conditional application to the original inventory
and publication consumers, including the computed-certificate wrappers.
Original `SourceProblem.InferenceSoundness` remains **OPEN**.

The parent supplied branch `yulang3` and integration baseline
`6545873f7262e9c3f3b1ef588a3c2ebca74ea83a`. This reviewer performed no Git
operation and makes no independent branch/ref-verification claim.

Reviewed in full:

- `notes/theory/lean/YulangClosure/SimpleSubLatticeGrowingInference.lean`,
  all 336 lines, SHA256
  `1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0`.
- `tasks/agent-loop/inbox/20261026-inference-lattice-growing.md`, SHA256
  `a9476d69c7f7f13056ce23e4c676b7a77d6c57e83455e8fcbe61202c14f7869a`.

The independently accepted direct dependencies retain their exact bytes:

| Dependency | SHA256 |
| --- | --- |
| `SimpleSubLatticeInference.lean` | `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3` |
| `SimpleSubLatticeDecision.lean` | `a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9` |
| `SimpleSubLatticeCertificates.lean` | `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b` |

Existing acceptance receipts are
`20261026-inference-lattice-inference-review.md` (SHA256
`55894b3fdda9fc77f6eac835eb81fac0c553b019f339701c5887f70f3c497416`)
and `20261026-inference-lattice-decision-review.md` (SHA256
`63f0e97332eec81732b23ade5b727a143d86c69721a95b75c0dc86e2b8c022a9`).
This review checks their relevant definition/consumer interfaces and carries
forward their accepted unchanged internals. It does not recertify the entire
dependency tree, native implementation, or later integration changes.

## Governing claim and review method

Read `AGENTS.md`, `AGENTS.pre-sprint.md`, the Lean role, the complete
`yulang-lean-proofs` skill and its source/execution guides, active sprint and
design-authority rules, and the M3/review-budget rules. The original claim is
`2026-10-13-intrusion-source-preservation-proof.md` sections 1, 3 and 5, read
with the Authoritative top-level inference principles and immutable Value-birth
qualification correction. The original closure statement and actual
`Contracts.lean` definition of `SourceProblem.InferenceSoundness` were checked.
The foreign R63/UNKNOWN state grants no lease and was left untouched.

The original theorem still ranges over supported original source programs,
lawful histories, all actual retained occurrences and lawful uses, with the
original lexical/type/event scopes, recursive sharing, complete Call/effects,
hygiene and one jointly scoped source witness. The finite graph component is
not substituted for that domain or for `sourceJudgment`/`sameScoped`.

I compared the entire new source with the owning definitions of `Extends`,
`Layer`, `Approx`, `RegularSub`, `Extrusion`, `ConstraintStep`,
`ConstraintHistory`, the actual decoder and `LawfulStore`, the existing
publication clause-image theorem, and `constructCertificate`/`decideDemands`.
I read the complete final audit driver and all 30 printed theorem types and
axiom results, including generated/private declarations.

All twelve entries in the producer's `frozen-source-manifest.json` match both
the repository and isolated-project source bytes. A focused source scan of
those twelve files found no `sorry`, `admit`, project-axiom, `native_decide`,
`unsafe`, `implemented_by`, or kernel-bypass tokens. This source scan supplements
the transitive axiom audit; it does not replace it.

## Prefix transport preserves the original operations

`Completion.Extends` is literally `forall k, exists suffix,
target k = source k ++ suffix`. It is not an abstract semantic-preservation
assumption. Existing successful lookup and first-match decoder results keep
their exact kind, node, and index under the extension.

The new observation lemmas preserve successful union/intersection lookup,
bottom/top tests, existence, and structural expansion. `Extends.layer` covers
all thirteen original `Layer` constructors. The structural case preserves the
same child list and supplied recursive relation; finite transitivity and
lattice premises use their induction hypotheses. No new rule consults an
arbitrary recursive hypothesis at the current lattice depth.

`Extends.approx` is induction on finite depth, with the original `Layer.mono`
moving the recursive child relation. `Extends.regular` applies it at every
depth. Neither theorem uses reverse all-depth unfolding, assumes intermediate
validity/guardedness, or infers final validity/guardedness from prefix growth.

`Extends.extrusion` preserves all five actual extrusion constructors, including
structural expansion and both lattice traversals. Copy coordinates, polarity,
ordered copy lists, and endpoints are identical. `Extends.step` covers all ten
original lattice-aware step constructors: reflexive discharge, structural and
lattice decomposition, both bound insertions, opposite-bound replay, both
directed extrusions, and intrusion. The `ref`, `birth`, state obligations,
occurrence identities, origin/receiver Values and selected copies remain
unchanged. Intrusion retains the original event-membership, actual-copy and
`Occurrence.Qualifies ref birth` evidence; that predicate still delegates to
the immutable-birth induced-path definition in `Contracts.lean`.

`Extends.history` lifts the actual graph-indexed history by constructors.
`Extends.decode_store` transports the whole actual decoder equation using
the accepted constraint-decoding transport. `Extends.store_satisfied` combines
that decoder result with independently defined all-depth `RegularSub`.
Neither assumes a semantic preservation law or casts an incompatible old
graph history.

## Growing histories derive the final history

`GrowingHistory` has only `nil`, an actual `ConstraintStep` at the current
graph, and a literal prefix `grow` that leaves the state unchanged. Its graph
and state indices expose every intermediate boundary.

`extension` composes the actual growth steps. In the `step` case of `flatten`,
`rest.extension.step change` lifts that exact earlier step through the entire
remaining growth. The induction then produces a `ConstraintHistory` indexed
by the single final graph. The `grow` case uses the tail induction result;
no state transformation or already-flat history is supplied. `append` and
`of_fixed` retain the precise intermediate indices.

`accepted_sound` applies the unchanged original-demand reflection theorem to
that derived history. The semantic direction remains backward reflection
from final accepted obligations. It does not claim arbitrary-model
preservation, principal coverage, or that an intrusion equality can be added
without affecting solvability.

## Completion, publication and the computed witness

`LawfulStore` is independent formation evidence: actual variable lookup, row
and payload shape, and fresh labels/tags. It contains neither semantic
satisfaction nor successful decoding. `completedStore_correct` derives the
decoder equation for the executable completion result. The growing consumers
transport that exact equation to the final graph before applying history
reflection. No final decoder equation is an external argument.

The publication consumer retains all original premises: lawful joint
inventory/client formation, bounded original bounds, inactive images,
stopped-dependency closure, capture stopping implying allocation stopping,
use indices below `count`, and syntactic inventory coverage of target
published clauses. It invokes the original
`ScopedPublication.publication_clause_image` through
`publication_history_with_clients`. There is no substituted publication law.

Both published clauses and all clients use the same final `target` and the
single reference pullback

```lean
fun k i => refs k (publicationTransport n count afterUse q k i)
```

No separate graph, reference assignment, or transport is chosen for individual
uses, clients, kinds, or Function ports. This is the shared graph interpretation
component; it does not establish the remaining whole source witness.

The three decided wrappers use exactly
`LatticeDecision.constructCertificate target`. `decideDemands` definitionally
is the original `Lattice.accepts` with this constructed certificate. The final
publication wrapper supplies no certificate, terminal model, final decoder
equation, or already-flat history. Its genuine remaining terminal premise is
the executable `decideDemands target last.obligations = true`.
The independently accepted decision construction is exact for the frozen
finite valid graph relation. No new semantic predicate or source restriction
is introduced by this application.

Final `Valid` and `Guarded` follow from the original acceptance checker. They
are not consequences of completion or prefix extension. The graph guard
remains the existing component interface; no assertion that all original
source programs satisfy it is made.

The concrete example really interleaves an earlier Function decomposition
with allocation: all four original ports are retained, a tuple containing
union/intersection references is appended at new value index 9, and a demand
on index 9 is inserted and reflexively discharged. The terminal certificate
retains both effect comparisons and the recursive lattice result comparison.
It is not merely a fixed history injected by `of_fixed`.

## Verification and the stale-artifact event

The project pin is Lean 4.35.0 with no external packages and `-j1 -M1024`.
The frozen producer reports native Lean commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, one thread and 120-second call
bounds. This reviewer did not execute Lean or claim an independent version run.

I inspected the actual check04 build success, check05 required-root failure,
and check06 absence diagnostics. Check05 loaded 27 theorem constants and
failed on the missing new `GrowingHistory.decided_sound`; check06 found all
three newly required constants absent. Those are material failed evidence,
not successful verification of the frozen 336-line revision.

The producer then reported the exact-source direct rebuild in check07 and a
successful check08 final audit. The current isolated `.olean` hash is exactly
the reported rebuilt hash below. The final audit contains all three new
required roots with the intended complete types. This resolves the acceptance
evidence discrepancy for this review. The cause of the earlier stale-artifact
retention is not established or asserted.

| Independently inspected evidence | SHA256 |
| --- | --- |
| `inference-lattice-growing/frozen-source-manifest.json` | `b47e6e68b72c13945ef293dfe942a9933bddb1968b6f9a6099c795b241ae2a16` |
| `inference-lattice-growing/project/AuditLatticeGrowing.lean` | `6863bdbac232b4d7a36f60f835b74a9a79fc6657b5b81d57261089a5a475d3de` |
| `inference-lattice-growing/check08-audit.log` | `42d2ce50661cfb83f96c914c63bd0d802bd18451af1b989b89c5ed399b5f43c0` |
| Rebuilt `SimpleSubLatticeGrowingInference.olean` | `ad17c3875365a3bbe73176e314f2b8c59ecf52e317e159117a31512b28b66e5a` |

Independent parsing of the complete final audit found 30 distinct theorem
begin/end/axiom records, matching in order. These comprise 27 explicit theorem
declarations plus `GrowingHistory.brecOn` and two private generated structural
match equations. The audit rejects project axioms and checks transitive
dependencies of every originating theorem.

| Actual axiom set | Theorems |
| --- | ---: |
| None | 1 |
| `propext` | 12 |
| `propext`, `Quot.sound` | 17 |

There is no `sorryAx`, project axiom, `Classical.choice`, or unchecked native
evaluation assumption in these results. No concrete unresolved risk warranted
another compiler invocation: reviewer focused checker calls were **0 of 2**.
Only bounded read/hash/log-inspection commands were used; no compiler/cache,
native test, benchmark, network, or dependency operation was run.

## Parent application and remaining owners

This component removes the need to supply an already-flat final-graph history
and an external terminal certificate, while carrying the computed lawful
decoder through real interleaved graph allocations. It establishes the stated
original inventory/publication conclusions under the retained concrete inputs.

The next source/native bridge must produce those actual inputs from native
generation and successful inference: a faithful graph/reference assignment,
lawful complete inventory, original metadata and coverage, the indexed
constraint/allocation history, and the successful final decision. Mutable row
rewrites, representative changes, later occurrence activation and open
row/width/presence behavior are not literal prefix allocation by definition.
Their faithful interpretation remains with the native/source correspondence
owner under primary coordination.

Original full source reconstruction, complete contextual Call/effects and
`sameScoped` with its one correlated source witness remain with their source
proof owners. Principality, ordinary inference progress, termination and
production promotion are not closed by this component. The final source and
handoff state these limits accurately.

## Write cessation and integration boundary

The only written path is this new review receipt. No review scratch was
created. Proof sources, dependencies, producer evidence, shared status,
imports, caches, Git and foreign leases were not written. Review writes stop
with this receipt; there are no children or running checker processes.
Primary adjudication, shared-record synchronization and integration remain
primary-owned. No repair round is requested.
