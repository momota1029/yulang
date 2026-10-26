# Inference soundness: source-grounded incremental proof work

## Goal, authority and ownership

The user's continuing instruction explicitly prioritizes type-inference
soundness and authorizes small commits and pushes along the way. Initial
baseline: `0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3` on `yulang3`.
The original full source theorem remains the one in
`docs/yulang-whole-proof-closure-ja.md` §1 and
`SourceProblem.InferenceSoundness`; no smaller component theorem replaces it.
The inference top-level principles and the authoritative 2026-10-24 immutable
Value-birth/induced-SCC correction govern the work.

This is an isolated primary-owned checkout. Foreign R63/UNKNOWN leases,
`tasks/agent-loop/current.json` and the reserved `YulangClosure.lean` remain
untouched. Only the primary stages, commits and pushes exact reviewed paths.
Generic workers use the repository proof/review role instructions; effective
custom-role/model execution is not inferred from role names. All are leaves.
Each coherent proof receives one non-author semantic review, bounded pinned
Lean checks and full originating-module type/axiom inspection. Rust corrections
to adopted semantics additionally require focused tests and independent review.

## First checkpoint: the actual birth-induced qualification contract

`YulangClosure.BirthLevelSCC.finite_helper_qualifies_iff` proves that executable
finite eligibility on the filtered helper graph is equivalent to the unchanged
`Contracts.Qualifies` on semantic Value incidence. Its local helper invariant
requires only that edges entering a helper preserve its actual planning level.
Whole-path projection/filter commutation is derived, not assumed.

The proof preserves raw cross-level references, includes singleton SCCs, and
rejects both a cross-birth cycle and equal-birth endpoints whose connecting
path requires a different-birth intermediate. The latter shows why comparing
endpoint births after one global SCC computation is insufficient.

The finite reference algorithm is a Warshall specification. Native Kosaraju
correctness, actual source births and exact incidence remain separate owner
obligations. Qualification does not establish lawful equality publication,
source-scoped coverage, principal inference or the inference-soundness root.

Frozen source SHA-256:
`2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0`.
Fresh isolated Lean 4.35.0 checking accepted all 32 named theorems and all
57 module-originated theorem constants: 37 empty axiom lists, 19 with only
`propext`, and one generated congruence theorem with only `Quot.sound`.
The complete source, all printed types/axioms and input hashes received a
CLEAN non-author review. No new warning or unapproved axiom occurs.

- [Proof handoff](../../tasks/agent-loop/inbox/20261026-inference-birth-scc-proof.md).
- [Independent review](../../tasks/agent-loop/inbox/20261026-inference-birth-scc-review.md).

`InferenceProofs.lean` is an additional default-build glob, leaving both
previous roots intact. `AuditInferenceProofs.lean` enumerates exact originating
modules, rejects project axioms, requires the named application roots and checks
all private/generated theorem constants. Reproduce from `notes/theory/lean`:

```sh
lake build
lake env lean -j1 -M1024 AuditInferenceProofs.lean
```

The integrated default build passed **60 jobs**, exit 0 (1.536 seconds with
unchanged dependencies cached). The final complete audit passed **57** records,
exit 0 (1.487 seconds), log SHA-256
`f883ec8d08d9637b1c8c8c35aa49f7a05b1def8f7329a81753d158b940811b16`.
An initial audit elaboration failure from an unannotated mutable counter was
repaired by giving it the intended `Nat` type; both logs remain in task scratch.
No proof source changed for that audit-script repair.

## Current critical path

The native graph still used global SCC qualification at the initial baseline;
the existing nested loop/helper fixture encoded that superseded expectation.
Actual source planning assigns the outer definition birth 1 and nested local
initializer birth 2. The accepted rule makes both reciprocal events
nonqualified. This is an evidenced qualification/coverage mismatch, not by
itself a proof of unsound acceptance: faithfully retained equality constraints
restrict the solution set.

The constructive forward-soundness lane therefore separately targets the
one-sided extrusion links, concrete retained-constraint transformation, and
solution pullback through quotienting and finite independently freshened uses.
A successful native return must still supply an actual solution, and generated
constraints must reconstruct the original source judgment with the same scope
and shared witnesses. Complete source/Call/effect interpretation, recursive
solution existence, actual occurrence attribution and general native trace
correspondence are still OPEN; this checkpoint supplies none of them by
assumption or reclassification.

## Native correction checkpoint

The four-file Rust correction now supplies immutable births from the existing
source planning walk, never from a later Name occurrence or mutable row level.
The existing fragment-index allocation is handed to that walk; semantic/helper
levels are retained once, and inconsistent or missing assignments fail safely.
Before SCC construction, seal checks every actual edge entering a helper against
the local invariant consumed by `BirthLevelSCC`. Both Kosaraju traversals filter
cross-level edges without deleting them from raw adjacency. Work/storage added
by the census, validation and edge filtering is O(V + E), without per-level scans.

The source-owner traversal also includes the actual FieldTail receiver and
OperatorApplication operands, fixing the corresponding nested initializer
ownership omissions. The original nested loop/helper source remains intact.
Its superseded cross-birth qualification/equality assertions were corrected
only after fresh pre-write specification review against the adopted October 24
rule. Independent equalities are still permitted; no blanket parent/copy
inequality assertion was substituted.

Exactly three focused, serial `cargo test --locked` invocations passed:

| Gate | Tests passed | Wall time |
| --- | ---: | ---: |
| `--lib candidate_value_graph::` | 24 | 110.70 s, cold build |
| `--lib candidate_intrusion::tests::` | 17 | 0.42 s |
| `--test candidate_intrusion_observation` | 3 | 20.28 s |

All use `-p yu-solver --features shadow-apply-candidate`, one build job and
`-- --test-threads=1`. The approved process limit was 6 GiB, with a 600-second
cold-build bound and 120 seconds for each subsequent gate. Official Rust 1.99.1
components were installed only in task scratch after SHA-256 verification
against the official 2026-10-15 manifest. CI selects stable; the repository has
no Rust pin, and no manifest, lockfile or dependency was changed. No full
workspace suite or repeated performance experiment was run.

Frozen implementation hashes and complete command/exit evidence are in the
[native handoff](../../tasks/agent-loop/inbox/20261026-inference-birth-native.md).
The [fresh non-author review](../../tasks/agent-loop/inbox/20261026-inference-birth-native-review.md)
found no blocking, major or minor issue in this correction and inspected the
linear resource behavior. The prior [source map](../../tasks/agent-loop/inbox/20261026-inference-native-map.md)
records the actual construction/consumer seam.

This supplies the implemented birth/filter criterion on the represented graph.
It does not prove complete source graph coverage, Imported identity resolution,
`any`-support receiving attribution, native Kosaraju correctness in Lean,
BL-JOINT, or full inference soundness. Those are separate original obligations.

## Constraint reflection checkpoint

`SimpleSubConstraintSyntax` gives an independent kind-indexed structural
derivability relation. `SimpleSubConstraintSoundness` derives the directed
extrusion approximation from the links actually emitted by its structural
traversal, with the two contravariant Function input ports and two covariant
result ports. Positive/negative demand reflection reconstructs the removed
original comparison from the copied comparison and its links. Actual bound
replay preserves the entire solution set.

Concrete `Step` and `History` constructors cover structural decomposition,
bound insertion/replay, extrusion and equality insertion for copies belonging
to an actual retained qualified occurrence. `History.quotient_sound` pulls
one terminal valuation back through the exact renaming of every retained
clause, then reflects it through the whole history. It does not choose
independent witnesses for separate fields or occurrences. The backward
implication for added equality does not imply preservation of all solutions
or model existence.

The frozen modules received a CLEAN independent review against both the
governing source-preservation argument and actual candidate extrusion lanes.
Isolated Lean checking accepted all **186 originating-module theorem constants**
(90 Syntax, 96 Soundness), including generated/private helpers: 145 have no
axioms, 26 use only `propext`, and 15 use `propext, Quot.sound`.

- [Construction, exact scope and audit](../../tasks/agent-loop/inbox/20261026-inference-constraint-soundness.md).
- [Independent semantic and implementation correspondence review](../../tasks/agent-loop/inbox/20261026-inference-constraint-review.md).

Finite-Term valuations remain a premise of this reflection theorem. Native
success is not identified with an empty retained store or with an existing
valuation. General recursive solutions, actual selected-bound/memo/worklist
simulation, full native optional/width/tag matching, original source generation,
generalization and complete contextual Call/effect meaning remain OPEN. The
regular-solution and original-source lanes attack those explicit next bridges.

Default integration passed **62 jobs**, exit 0. The expanded complete audit
passed **243** records (57 birth + 90 syntax + 96 constraint soundness), exit 0,
log SHA256 `e3d407a980f6fdec73d9a68d390ab801196a07d632829807364c0844e985834e`.
No proof source was changed after independent review; only the exact import and
audit inventories were extended. Existing foundation warnings are unchanged.

## Generalization and constructive regular solutions

`SimpleSubGeneralizationSoundness` constructs one finite row transport for the
base store, every requested fresh use, shared low anchors, and arbitrary later
client constraints. The substitution/renaming square is proved for every
existing structural Term constructor, not supplied as a preservation premise.
The canonical specialization proves exact finite class minima and separation
of allocated use coordinates from the later client region.

Independent review found a minor interpretation error in the first version:
an arbitrary row map need not have an in-range fixed representative, so its
seeded level fold need not be an exact class minimum. The literal broad
pullback was sound. The correction preserves that broad theorem, adds the
precise finite-range/idempotence conditions, and proves their minimum/allocation
consequences. The original finding and a narrow independent delta review remain
separate receipts. This is a proof clarification, not a compiler semantics change.

The model copies every clause of a supplied finite store for each use. Actual
reachable-high native publication, non-generic/captured-local metadata and
bound/scope correspondence are still required before applying it to Rust
freshening. A complete-store premise is not silently ascribed to native success.
All **71 originating-module theorem constants** passed Lean and axiom audit:
35 empty, 10 `propext`, 26 `propext, Quot.sound`.

- [Generalization construction and repair](../../tasks/agent-loop/inbox/20261026-inference-generalization.md).
- [Initial independent review](../../tasks/agent-loop/inbox/20261026-inference-generalization-review.md).
- [Narrow repair review](../../tasks/agent-loop/inbox/20261026-inference-generalization-delta-review.md).

`SimpleSubRegularSolutions` independently defines structural subtyping by all
finite unfoldings of a finite guarded graph. Its executable checker validates
all graph references and metadata, all child comparisons of a finite table,
and coverage of every demanded root. From acceptance,
`accepted_joint_relation` constructs one postfixed relation covering all roots;
`accepted_demands_sound` proves their regular subtyping without any supplied
terminal valuation or solution. Cycles genuinely run through Function, Record,
Tuple and Variant nodes. Both Function effect ports and their variance remain.

The independent review accepted this stated model and all **134 theorem
constants**: 45 empty, 64 `propext`, 25 `propext, Quot.sound`. Rejection examples
cover missing effect evidence, reversed comparison, optional metadata mismatch
and dangling graph references even under an immediate bottom comparison.

- [Regular construction and exact native boundary](../../tasks/agent-loop/inbox/20261026-inference-regular-solutions.md).
- [Independent review](../../tasks/agent-loop/inbox/20261026-inference-regular-review.md).

The graph language has no alias-only or lattice cycles. This regular relation
is not the finite-Term valuation used by the earlier history theorem. A new
graph-indexed reflection construction attacks that connection explicitly.
Faithful native graph/demand decoding, successful-certificate extraction,
ordinary coalescing and full source Call/effect interpretation remain OPEN.
`SolvedModule::solve` returning `Ok` is availability completion; the actual
export/fresh-use consumer additionally rejects final errors. No native theorem
uses the weaker availability result as its semantic-success premise.

The integrated default build passed **64 jobs**, exit 0. The complete audit
passed **448** records, exit 0: 262 empty axiom sets, 119 `propext`, one
`Quot.sound`, and 66 `propext, Quot.sound`. Audit log SHA256:
`1a34e88d035a077387fa4c0f88867ef0e924147a5171ccd34e51a283700c42c2`.
All five inference modules were frozen at their independently reviewed hashes.

## Applying regular solutions to original demands and scoped publication

`SimpleSubRegularConstraintSoundness` now directly applies finite certificate
acceptance to a concrete graph-indexed constraint history. Regular reflexivity
and transitivity are proved from the existing all-depth interpretation.
Structural decomposition, retained opposite-bound replay, extrusion from exact
signed copy links and equality insertion for actual retained occurrences then
reflect the accepted final comparisons back to **every original demand**.
`accepted_original_joint` uses one common graph/relation for all original and
final comparisons. No final model, valuation, subtype-preservation law or
original-demand solution is an input.

The original Function comparison is absent from the entire final certificate
in one checked example, so this result does reconstruct a removed obligation.
Other examples cover genuine cycles with both Function effect ports and a
non-injective structural quotient. The latter uses a concrete exact lookup
equation; arbitrary native union-find merging is not asserted to satisfy it.
All **169 module theorem constants** passed audit (43 empty, 83 `propext`,
43 `propext, Quot.sound`). Independent review accepted the module. Its only
minor finding was the handoff phrase "forward preservation" for added equality;
the primary corrected it to the actual backward solution-reflection direction,
without changing any Lean source or theorem.

- [Regular history construction](../../tasks/agent-loop/inbox/20261026-inference-regular-constraint-soundness.md).
- [Independent review](../../tasks/agent-loop/inbox/20261026-inference-regular-constraint-review.md).

`SimpleSubScopedPublication` removes the earlier requirement to copy every
clause for every use. It retains the complete base and copies only bounds of
reached local owners. Capture traversal and allocation have separate predicates,
matching native stored-local versus current-level/non-generic checks.
`publication_clause_image` derives forward clause inclusion by reachability
induction. When a mapped owner becomes inactive, dependency closure proves
that its whole copied clause is fixed and already occurs in the retained base.
This direction needs neither reverse coverage nor quotient-class saturation.
`metadata_publication_with_clients` then pulls one solution back for all uses
and arbitrary clients from concrete level/non-generic conditions.

The **82 theorem constants** passed audit (51 empty, 13 `propext`,
18 `propext, Quot.sound`). Fresh independent review accepted the stated scope.
Two checked finite counterexamples show that numeric level closure alone does
not justify non-generic stopping, and exact canonical class minima alone do not
preserve dependency closure. They are not source-qualified intrusion examples
or claims of an accepted ill-typed native program.

- [Scoped construction and actual guard mapping](../../tasks/agent-loop/inbox/20261026-inference-scoped-publication.md).
- [Independent review](../../tasks/agent-loop/inbox/20261026-inference-scoped-publication-review.md).

The remaining native owners must establish metadata/dependency closure through
all actual merging/replay paths, canonical first-image coherence, complete effect
incidence and faithful shared-graph/history/certificate extraction. The regular
history fragment still excludes lattice/alias cycles and complete native open
row/width/presence/variant matching. Scoped publication currently transports a
supplied finite-Term solution; connecting its exact syntactic clause inclusion
to the constructed regular interpretation is the next bounded proof packet.
No whole-source inference, principality or termination gate is promoted.

Default integration passed **66 jobs**, exit 0. The seven-module audit passed
**699** matched records, exit 0: 356 empty axiom sets, 215 `propext`, one
`Quot.sound`, and 127 `propext, Quot.sound` (including wrapped reports).
Log SHA256: `7a95262052fa057b077ee51dee7b3cf036d9000da646d048dadedd9f144e5c78`.
Reviewed proof source bytes were unchanged at integration.
