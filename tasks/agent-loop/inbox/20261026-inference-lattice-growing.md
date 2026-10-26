# Growing lattice histories with computed terminal evidence

Date: 2026-10-26. Producer: primary `/root`, no coauthor. Branch `yulang3`;
integration baseline at freeze `6545873f7262e9c3f3b1ef588a3c2ebca74ea83a`.
Status: kernel-checked component, frozen for independent nonauthor review.
Original `SourceProblem.InferenceSoundness` remains OPEN.

## Scope, authority and frozen outputs

The user's renewed instruction authorizes continuing original inference
soundness and small commits/pushes. The unchanged parent retains all supported
original source constructors, lawful finite histories, lexical/type/event
scopes, recursive sharing, all lawful generalization uses, full Call/effects
and one jointly scoped witness. This packet constructs a concrete history
bridge; it does not narrow or instantiate that parent.

Applied the root instructions, existing `yulang-lean-proofs` skill and its
source/execution references, original inference principles and immutable-birth
qualification. Foreign UNKNOWN/R63 state and the reserved original root remain
untouched. The primary lease and finite verification budget are recorded in
`notes/progress/2026-10-26-inference-evidence-construction.md`.

Only the new proof and this handoff belong to this producer packet. Integration
imports/audit/navigation are separately primary-owned. No native code, original
source rule, old proof dependency, global toolchain or dependency changed.

- Proof: `notes/theory/lean/YulangClosure/SimpleSubLatticeGrowingInference.lean`,
  336 lines, SHA256
  `1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0`.
- Handoff: this file.
- Isolated project and evidence:
  `/workspace/scratch/f98087c7ac1a/inference-lattice-growing/`.
- Frozen direct inputs:
  `SimpleSubLatticeInference.lean`, SHA256
  `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3`;
  `SimpleSubLatticeDecision.lean`, SHA256
  `a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9`.
- All twelve source files in the isolated dependency cone byte-match current
  repository sources. Exact path/hash inventory:
  `frozen-source-manifest.json` in the scratch directory.

Proof writes stop at the stated hash; only this handoff follows. Both direct
dependencies were frozen by their producers. The consumer is independently
accepted and integrated; the decision producer's independent review reports
ACCEPT, with its receipt pending at this handoff's preparation.

## Actual construction

### Prefix transport without unproved unfolding

The first namespace extends the existing
`LatticeInference.Completion.Extends`, which means literal per-kind table
prefix extension. It reuses the established successful-lookup preservation.
No old identity or constructor is rewritten.

`Extends.present`, `union_at`, `intersection_at`, `bottom_at`, `top_at`, and
`expansion` preserve actual successful node observations. `Extends.layer`
inducts over all original finite `Lattice.Layer` constructors. Structural
children use the same supplied recursive relation; finite lattice/transitivity
premises use their induction hypotheses.

`Extends.approx` then inducts on the finite approximation depth and applies
`Layer.mono` to the transported layer. `Extends.regular` follows pointwise at
every depth. **No reverse all-depth unfolding theorem is used**, and target
validity/guardedness are not inferred from prefix extension.

`Extends.extrusion`, `step`, and `history` translate the concrete lattice-aware
constructors. Both directed extrusion cases, union/intersection traversal,
structural ports, opposite-bound replay and retained occurrence-qualified
intrusion are preserved with identical coordinates, `ref`, `birth`, and
origin/receiver identities. No old incompatible graph history is cast.

`Extends.decode_store` applies the existing actual decoder-constraint transport
to the whole joint store. `Extends.store_satisfied` additionally transports the
independent regular relation. Neither uses supplied semantic-preservation laws.

### Locally indexed growing histories

`LatticeGrowingInference.GrowingHistory` has only three constructors:

1. `nil`: same graph/state;
2. `step`: the actual `ConstraintStep` indexed by the graph at that point;
3. `grow`: literal graph-prefix extension with the state unchanged.

`extension` composes all prefix extensions. `flatten` derives a single
`ConstraintHistory` on the final graph by lifting each earlier exact step
through the remainder's proved extension. It has no already-flattened history
or semantic law among its inputs. `append` and `of_fixed` preserve exact
intermediate graph/state indices.

`accepted_sound` obtains the initial obligations' interpretation from the
flattened history and the original final certificate checker. Validity and
guardedness come from **final acceptance**. No assertion about the validity
or guardedness of every intermediate graph is required or made.

### Completion, computed witnesses and original clients

`completed_growing_store_sound` starts from the consumer's independent
`LawfulStore` formation evidence. Executable `completedStore` derives the
initial decoder; prefix transport carries that exact equation into the final
graph; the flattened history reflects final acceptance back to that inventory.

`completed_growing_publication_with_clients` applies the unchanged original
publication theorem to the same final graph. It retains exactly these premises:

- lawful term/row/reference formation for the joint inventory;
- original bounds bounded by `n`;
- original inactive-image and stopped-dependency closure conditions;
- capture stopping implies allocation stopping;
- the original supplied use-index bounds;
- syntactic inventory coverage of the target published clauses;
- actual locally indexed growing constraint/allocation history;
- final certificate acceptance.

The two decided corollaries replace that last external certificate with
`LatticeDecision.constructCertificate target`. In particular,
`completed_decided_growing_publication_with_clients` requires only the computed
`LatticeDecision.decideDemands target last.obligations = true`. It has **no
externally supplied finite certificate, terminal satisfying model, successful
decoder equation or fixed-graph history**.

Its conclusion includes literal extension from the initial graph, final
`Valid` and `Guarded`, and both `PublishedSatisfied` and `StoreSatisfied`
under the single shared pullback

```lean
fun k i => refs k (publicationTransport n count afterUse q k i)
```

All original uses and clients share that graph, assignment and transport.
The decided wrapper consumes definitionally the original acceptance check,
with the exact constructed certificate; it does not introduce a new semantic
predicate or prove success by assuming the target interpretation.

## Concrete example

The example begins at the accepted genuinely recursive lattice Function.
It decomposes all four Function ports, then appends a fresh tuple containing
the union/intersection result nodes. It inserts and discharges a comparison on
that newly allocated tuple. Terminal acceptance retains both original effect
comparisons and the recursive result comparison. `interleaved_original_solved`
reconstructs the original Function demand in that one final graph. This
example exercises actual graph growth after an earlier step; it is not merely
a fixed history wrapped in `of_fixed`.

The separate frozen decision module checks its own computed examples, including
the same recursive graph. No additional native fixture or performance claim is
made by this proof integration.

## Verification and material failures

Pinned native Lean **4.35.0**, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; one thread, `-j1 -M1024`, maximum
120 seconds per call, isolated project/cache. Eight of twelve focused calls
were used. No timeout or memory-cap failure occurred.

| Check | Result and action |
| --- | --- |
| 01 build | Failed only at three dependent case-pattern `state` binder references. Replaced those inaccessible names with the already indexed state metavariables; no statement changed. |
| 02 build | PASS, 12 jobs, original 27-theorem growth proof. |
| 03 audit | PASS, all 27 originating theorem constants, including the generated recursor theorem. |
| 04 build | PASS, 13 jobs after importing frozen decision and adding the three decided consumers. No warnings. |
| 05 audit | Failed its required-root gate: the loaded `.olean` still exposed the earlier 27-theorem inventory, despite the updated source/`.ilean` and successful build report. No acceptance was inferred from this audit. |
| 06 diagnosis | Confirmed all three newly required constants were absent from the loaded environment. This was a concrete stale-artifact discrepancy, not a proof or axiom finding. |
| 07 direct rebuild | Verified exact source hash in the compiler process and regenerated only this owned isolated `.olean` via pinned `lake env lean … -o …`; exit 0. Artifact SHA changed from `5ad09f877b21fa15aefe0206defa765e22233b4c8e20b843ea5a8e1fb2fdef44` to `ad17c3875365a3bbe73176e314f2b8c59ecf52e317e159117a31512b28b66e5a`. The cause of the earlier artifact-retention discrepancy is not asserted. |
| 08 final audit | PASS with all three required new constants and **30** originating theorem types/axiom lists. No missing or duplicate begin/end records. |

Complete final audit:
`check08-audit.log`, SHA256
`42d2ce50661cfb83f96c914c63bd0d802bd18451af1b989b89c5ed399b5f43c0`.
Driver: `project/AuditLatticeGrowing.lean`.

All 30 constants, including private/generated declarations, have only:

| Axiom set | Count |
| --- | ---: |
| None | 1 |
| `propext` | 12 |
| `propext`, `Quot.sound` | 17 |

No project axiom, `sorryAx`, `Classical.choice` or native-evaluation assumption.
All failed and successful logs remain available. The independent reviewer
must check the final 30-theorem audit, not the superseded 27-theorem artifact.

## Parent application and retained boundary

Literal append-only allocation is the proved graph operation. Mutable native
row rewrites, representative changes and later activation histories still need
their faithful interpretation/trace bridge. The algorithm needs the actual
graph, variable references, lawful row shape, complete inventory and original
metadata/coverage evidence. Native no-error success has not been proved to
produce that graph/history or make the computed decision true.

The finite lattice acceptance fragment still requires the existing guard
check; this is not a restriction imposed on all original source programs.
Native open rows/width/presence, ordinary coalescing, complete contextual
Call/effects, original full-source reconstruction and the shared source witness
retain their owning obligations. This packet does not close the original root,
source principality, progress, termination or production gates.

No worker/checker process remains for this producer. Proof writes are stopped
at the recorded source hash; independent review and final integration follow.
