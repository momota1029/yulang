# Independent review: lattice inference consumers

Date: 2026-10-26. Reviewer: `/root/lattice_review` (independent nonauthor,
M3 single-reviewer packet). Producer: `/root/lattice_certificates`.

## Verdict and exact scope

**ACCEPT. No mathematical, source-correspondence, axiom, or evidence findings
in the frozen consumer packet.** This accepts the stated proof-side decoder,
concrete fixed-graph histories, constructor completion, and conditional scoped
publication results. It does not close the original whole-source inference
obligation or establish native correspondence.

The parent supplied accepted base/root
`e87556fbdf53962bcccecd72756f5518acab3fc1`. This review performed no Git
operation. The separately developed `SimpleSubLatticeGrowingInference.lean`
and any later consumer or integration changes are outside this receipt.

Reviewed output:

- `notes/theory/lean/YulangClosure/SimpleSubLatticeInference.lean`, all 1,461
  lines, SHA256
  `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3`.
- `tasks/agent-loop/inbox/20261026-inference-lattice-inference.md`, SHA256
  `3328afac9b30d914429c44bc36c412b25943cc31387330ee6f3831f05d3c87b5`.

This is a new receipt for the consumer packet. It does not amend the earlier
independent certificate receipt, `20261026-inference-lattice-review.md`.
The certificate dependency remains frozen at
`55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b`.

## Authority and review method

The governing `AGENTS.md`, `AGENTS.pre-sprint.md`, Lean role/skill and execution
guidance, top-level inference principles, birth-level correction, and original
source-preservation obligation were read in the preceding continuous review
and remain governing. The original obligation is the all-supported-source A/B
obligation of `2026-10-13-intrusion-source-preservation-proof.md`, especially
sections 1 and 3; this packet does not replace it with a smaller source domain.

The preceding review also inspected the actual primary reference paper,
Fig. 10 and sections 5.1–5.3, the pinned reference implementation, the original
finite `Sub` semantics, and the frozen regular/lattice interpretation. That
source boundary is retained here: the paper permits unguarded recursive
syntax; the accepted guarded-graph interface is a proof fragment, not a proved
restriction or characterization of the supported source language.

For this packet I read the complete new source, full producer handoff, complete
originating-module audit program, all 275 printed theorem types and axiom
results (including private/generated declarations), and the final build/audit
evidence. I revisited the actual original publication clause-image theorem and
metadata guards, freshening transport, copy/occurrence qualification, and old
graph-dependent extrusion/history definitions. The comparisons below are to
those definitions, not solely to the producer's prose.

All ten isolated-project source inputs byte-match the repository files and
the supplied frozen manifest. The source cone has no proof-hole, project-axiom,
unchecked native evaluation, unsafe implementation, or kernel-bypass tokens.
No concrete unresolved risk justified rerunning the checker: reviewer compiler
invocations were **zero**, within the assigned maximum of two targeted checks.

## Decoder, metadata, and one shared reference assignment

The executable decoder at lines 24–110 covers every existing `SimpleSub.Term`
constructor. `findList` chooses the first exact node and `findNode_sound`
establishes the actual lookup equation at its returned index. A variable
reference must exist in the correct kind table. Union and intersection decode
both children and find the exact same-kind lattice node; they are not silently
erased or delegated to an old decoder that rejects them.

Function decoding preserves all four distinct ports in their original kinds:
argument value, argument effect, result effect, and result value. Record
decoding preserves the exact label, optional bit, child, and complete finite
structural tail. Tuple decoding preserves order. Variant decoding preserves
the tag, complete tuple payload sequence, and complete structural variant tail.
The exactness theorems at lines 232–258 and 599–641 expose those equations.
Lattice terms may be children/payload elements; lattice nodes cannot pretend
to be structural row tails or tuple payload spines.

`decodeTerm_rename`, `decodeTerm_congr_bounded`, and
`decode_freshen_transport` prove transport of this actual decoder. The latter
uses the existing boundedness and anchor-preservation conditions and
`Generalization.transport_freshen`. It uses one reference map throughout,
including both kinds, all four Function ports, all lattice children, all
published uses, and the clients. It does not select independent semantic
witnesses for different uses.

`ClauseSatisfied` and `StoreSatisfied` at lines 272–280 use successful actual
decoding and the frozen independently defined all-depth `Lattice.RegularSub`.
Their definition does not contain `accepts`. `checkStore_sound` obtains graph
validity, guardedness, and satisfaction from the executable decoder/checker
result, without a supplied model or preservation law.

## Actual graph-indexed extrusion, histories, and intrusion

The new `Extrusion`, `ConstraintStep`, and `ConstraintHistory` are indexed by
the actual `Lattice.Graph`. Reused Copy, Occurrence, Comparison, and
ConstraintState data are graph-free. No old graph-indexed soundness theorem is
cast to the extended graph type.

`Extrusion` has the actual polar copy cut, present same-node rule, structural
expansion, and union/intersection traversal. The structural case consults
`Lattice.structuralExpand`, hence the unchanged original structural variance
and exact metadata. Lattice traversal preserves the actual ordered child copy
lists. `Extrusion.sound` proves the result by induction from the copy-link
obligations; there is no assumed extrusion-soundness premise.

The step constructors at lines 465–505 retain concrete obligations for
structural decomposition, left-union/right-intersection decomposition,
reflexive discharge, bound insertion, opposite-bound replay, and both directed
extrusion forms. Intrusion requires an actually retained occurrence, the
unchanged `Occurrence.Qualifies ref birth` predicate, and membership of each
selected copy in that event's actual copies. Added equalities are the actual
two directed comparisons from those copy coordinates. Qualification is not
redefined through a type-bound graph or a numeric surrogate.

The soundness direction is honest: step/history soundness reflects final
satisfaction backward. `accepted_intrusion_equalities` applies this to the
history after adding selected equalities. It proves both the earlier demands
and those selected equalities from terminal acceptance. It does not claim that
adding equalities preserves every previously satisfying assignment or prove
principal coverage. Occurrence retention is separately proved.

`ofRegular_extrusion`, `ofRegular_step`, and `ofRegular_history` are real
constructor-by-constructor translations through `Lattice.ofRegular`, retaining
all state and occurrence coordinates. `decodeTerm_ofRegular` and
`decodeStore_ofRegular` prove exact decoder equality for every original
Term/Store on an embedded old graph. In particular, a union/intersection Term
still fails there because an all-structural embedded graph has no such node.
`old_store_solution_embeds` then uses the established semantic embedding.

## Original publication assumptions are retained

The publication theorems invoke the existing
`ScopedPublication.publication_clause_image`; they do not replace that theorem
with a supplied clause-image law. Their original premises remain explicit:

- `BoundsBounded n bounds`;
- `InactiveImages n beforeUse afterUse q`;
- `StoppedClosed (bounds.map (Bound.rename q)) afterCap`;
- capture stopping implies allocation stopping;
- every selected use is below `count`;
- the target inventory syntactically covers the original target `Published`
  clauses.

`metadata_checked_publication_with_clients` retains actual capture/live
metadata transport, bound-level closure, and non-generic dependency closure,
then applies the existing guard lemmas. These are not replaced by weaker
numeric tests.

Both original published clauses and clients are interpreted in one final graph
under the single map
`fun k i => refs k (publicationTransport n count afterUse q k i)`.
The history version uses the new concrete history before applying the same
publication theorem. These are conditional source-syntax consumer results;
native derivation of their premises remains a separate obligation.

## Completion constructs decoder success; it does not supply new guards

The append-only completion code at lines 920–1356 handles every original Term
constructor. `Extends` is literal prefix extension of each kind table. The
preservation lemmas retain actual lookups and first-match decoder indices.
`intern` either returns the existing exact node or appends it at the old
length. Sequential completion transports earlier child decodings through
later extensions before interning the exact parent.

`Lawful` is an independent sufficient formation judgment. Its premises are
actual base-variable lookups, finite row/tuple-payload shape, and fresh record
labels/variant tags. It contains no successful completion run, decoder
equation, subtype proof, semantic assignment, final validity, or guardedness.
Both lattice constructors accept lawful children of their own kind and return
plain shape. Existing invalid or unguarded base graphs are not excluded by
this definition.

`completeTerm_correct` constructs a successful execution from `Lawful` and
prefix extension. `Built` contains exactly input-prefix retention, the actual
target decoder equation, and a target lookup with the promised shape.
`completeConstraint_correct` and `completeStore_correct` extend the result to
the joint original store. `completedStore`'s fallback is proved unreachable
under `LawfulStore`; no successful run or decoder equation is demanded from
the caller.

**Neither prefix extension nor completion alone establishes final validity or
guardedness.** The source and full printed types preserve this boundary.
`completion_alone_does_not_check_guard` exhibits a lawful empty inventory whose
completion leaves the frozen unguarded base unchanged and whose guard check
is false. This is a concrete counterexample to inferring an unconditional
guard guarantee from the completion result.

`completed_history_store_sound` and
`completed_publication_with_clients` obtain final `Valid` and `Guarded` from
terminal `Lattice.accepts`. Their history starts from the **computed** graph
and comparison list. The strongest publication theorem therefore assumes the
unchanged publication premises, syntactic `LawfulStore` for the joint
inventory/transported clients, a concrete history on that computed graph, and
successful finite certificate acceptance. It concludes prefix retention,
final validity/guardedness, and the original publication/client satisfaction
under one pulled reference map. No model or preservation theorem is hidden in
those premises.

The sparse-constructor instance meaningfully exercises construction: its
initial decoder fails, an independent Lawful derivation exists, and completion
creates the missing lattice, tuple/payload, variant, nil/suffix, and optional
record constructors. The original publication instance also exercises two
fresh uses, a cross-use client, and actual four-port decomposition. The
negative examples retain optional metadata and reject wrong-kind references
and lattice structural tails. These examples demonstrate the stated graph
representation results, not full source inference.

## Kernel evidence and immutable dependency receipt

The final producer build used the pinned Lean 4.35.0 toolchain and passed with
exit 0 in 9.920 seconds, without warnings. The complete audit passed with exit
0 in 1.457 seconds. The evidence uses the isolated owned project, a 120-second
limit, one Lean thread, and the reported `-j1 -M1024` resource bound.

| Evidence | SHA256 |
| --- | --- |
| `inference-lattice-inference/check07.log` | `e69f6f42bca3fb87f81e8fedf1680e38d1f92c88bf07ce5749b708b9f94a31cd` |
| `inference-lattice-inference/check08-audit.log` | `137193f4f3a88dda1fdee5e54100122311afb4adb0627f4230e966b7f1f3c68b` |
| `inference-lattice-inference/project/AuditLatticeInference.lean` | `4255c118b133e543471969c3b025aea02fa0dc2b191f6260ea925d55d17bedcb` |

The audit enumerates actual originating-module theorem constants, including
private and generated declarations. I independently checked matching begin,
end, and axiom-result names/order: **275 unique theorem constants**, with 275
begins, 275 ends, and 275 axiom results. I inspected every printed full type and
axiom result. Actual dependency sets are **109 empty**, **124 `[propext]`**, and
**42 `[propext, Quot.sound]`**. There is no `Classical.choice`, `sorryAx`, project
axiom, or unchecked native-evaluation dependency. Generated constants whose
names lie in an older namespace are correctly included by originating module.

The nine frozen dependency copies were compared byte-for-byte, with hashes:

| Source | SHA256 |
| --- | --- |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `SimpleSubRegularConstraintSoundness.lean` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |
| `SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| `SimpleSubRegularPublication.lean` | `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99` |
| `SimpleSubLatticeCertificates.lean` | `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b` |

## Parent remains OPEN; findings and write cessation

There are **no actionable findings for this frozen packet**. The following
are retained parent obligations, not defects disguised as assumptions:
deriving real graph/reference formation and LawfulStore from native/source
construction; original inventory coverage and guard invariants; extraction of
concrete extrusion/replay/intrusion and interleaved graph-growth traces;
construction of accepted finite lattice certificates from successful native
inference; correspondence with ordinary/unifying coalescing; full native
width/open-row/optional/cast behavior; and the jointly scoped original Call,
effects, lawful use, hygiene, principal coverage, progress, and termination
obligations. No smaller source language or production checker requirement is
introduced by this acceptance.

The reviewer wrote only this newly leased receipt. No proof source, import,
producer handoff, producer scratch/cache, shared status, Git state, or prior
review receipt was changed. No children or reviewer compiler checks were
started. **Review writes are stopped at this receipt.** Its exact SHA256 is
reported in the final handoff; that receipt hash is intentionally not inserted
into its own content.
