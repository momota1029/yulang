# Actual-inspection B4 boundary and fixed-hole phases

Date: 2026-11-14. Status: proved boundary transfers and conditional phase
termination; the general point-source readback construction remains open.
Integration baseline: `f77fa5109273d08b3bb0a54bd0dd65a4fc6ac85c`.

Authority: [spec §6](../../spec/06-roles.md), especially shared actual inputs,
actual-position K2 and unsettled-output deferral; the approved
[B4 draft](2026-11-08-b4-main-statement-draft.md), including addendum 7.
No language decision, existing definition or guard is changed.

## 1. Which Step does V5 currently use?

`B4TargetV5` and `B4SkeletonV5` are parameterized by a SourceBoundary. They do
not select a concrete Step. The original six-field concrete package is
`GeneralDictionaryReachableBoundary.boundary`, assembled by
`GeneralDictionaryReachableObligations.bridges_of_remaining`. Its state is
`GeneralNominalSaturationState.State`; its Step is the full feedback relation.
The six fields proved there are closure, stepModels, frontierLocal,
localIdentity, dictionaryRefl and initialReorders.

The later `GeneralNominalValueBoundary` uses `Tracked` states and Value Step.
`GeneralNominalSettledBoundary` replaces that Step with Settled Step and
adjusts inspection-pending. Neither is the actual-inspection relation used
by the new ground theorem.

`ActualInspectionSteps.step_shared` proves inclusion in Shared Step on the
same Tracked states. It does **not** prove accessibility of Shared Step from
actual-inspection accessibility. Nor is there a general exact-successor
inclusion from Shared Step into Settled/Value/the original feedback boundary:
shared installation retains different child-origin information. The existing
`GeneralDictionary169SharedStable.value_action_exists` transports the
existence of an action with the same focus; its successor can differ. It does
not transport exact traces or their reachable snapshots.

The new `GeneralNominalActualBoundary.boundary` is an **operational adapter**.
It retains the Settled local diagnostic fields and evidence field, changes
Step to the actual-inspection Step, defines Stable using actual At, and keeps
InitialSource as Initial. Reachable is proved equivalent to actual SourceFormed.
This adapter is not claimed to be a completed semantic retarget of B4.

| V5 field | Actual-inspection status and transfer direction |
| --- | --- |
| progress | Closed for ground-root point sources via the new `groundBoundary.Initial`; arbitrary InitialSource is still open. Restricting a relation transfers old Acc to new Acc, not conversely. |
| execution | An old executor's trace need not be an actual trace. `terminal_of_accessible` constructs existence of a finite halted actual trace. A particular executor still needs to select it and prove its run equation. |
| halted | Shared haltedness implies actual haltedness by inclusion; the converse is unavailable. `ground_terminal` supplies actual haltedness at an actual reachable endpoint. |
| closure | Reproved with actual At and generated transitivity. Actual halt cannot establish the old broader Stable. |
| stepModels | Proved by `step_shared` followed by `SharedSteps.step_models`, with final models included in earlier models. |
| frontierLocal / localIdentity | Reconstructed for the retained fields using local totality/functionality and survivor functionality. They are local classification laws, not guard completeness. |
| dictionaryRefl | Reuses dictionary equivalence reflexivity. |
| initialReorders | Reuses source formation under declaration reorder; no Step inclusion is needed. |

All six unconditional structural fields are thus available additively.
`ground_terminal` gives an actual finite trace, actual haltedness, root and
all-generated stability, and model inclusion from every ground-boundary
reachable state. It does not invent a dictionary tree or fill execution /
halted for an existing Executor.run.

To finish a semantic retarget, the local candidate/pending/K2 predicates must
also agree with shared generation and actual-position Safe/AlternativesSafe.
Retaining the old predicates can leave Local selected while the newer guard
blocks installation. An actual inspected cycle must receive K2 rejection,
not merely pending. That existing boundary integration gap is not repaired
by renaming Stable. The remaining eight fields of the old composition
(progress, execution, halted, whereAccessible, treeExecution,
canonicalLocalOrder, evidenceNode, generatedChildren) cannot be imported as
a package. In particular, local evidence and generated-child completeness
must be checked against the repaired emitter and diagnostics. No new complete
B4 Statement is asserted here.

`GeneralNominalActualPhaseBoundary.boundary` additionally restricts Initial to
point sources. Its progress field is proved under the single phase hypothesis
in §4. Show `pair (list int) int` is checked both through the new ground V5
progress field and through the new phase accessibility theorem.

## 2. What can be constructed immediately for unknown roots?

Let H be the existing finite `SourceFrontier.frontier` list for the initial
source. Its previously proved exploration theorem bounds source projection
paths by the number of initial slots and stops before cyclic inspection.
Keep index set `range H.length`. H can contain duplicate origins; a literal
source identity always uses its **first** index in H. Thus repeated uses of
one source identity choose exactly the same leaf. Keeping duplicate unused
indices only weakens the finite count bound; it does not identify distinct
origins.

`IndexedHoleReadback.initial_root` proves an actual semantic readback for
every unnamed root input: the leaf at that canonical index denotes the
original source origin in every initial model. It needs InitialSource, not
a finite closed model or a chosen interval interior. In particular an
unresolved or recursive value can remain an opaque leaf.

The same module proves:

* Actual Step preserves an existing readback by model restriction. Refresh
  or reobservation need not consume a hole merely because its descriptor
  becomes more informative.
* A represented constructor can be projected to its already represented
  child. Equality of actual origins transports a readback to an alias.
* If an update supplies an actual readback of hole h as a finite expression
  over the remaining holes, replacing h by that expression in **every**
  represented term preserves the readbacks and removes h from their leaf
  sets. `actual_elimination` states this simultaneous substitution over an
  arbitrary family of represented origins. The same replacement is used for
  every occurrence, including repeated captures and aliases.

These statements do not extract the replacement from arbitrary source
updates. They also do not turn a recursive opaque leaf into a finite ground
value. Treating an opaque cyclic component as a closed finite term in an
actual source model would be unjustified. The open producer must expose only
positions justified by the actual guard and supply the corresponding global
replacement, or keep the inventory unchanged.

In particular, `actual_elimination` proves readback preservation, not that h
is present in the remaining list or that its replacement has the bounded
vocabulary/depth required by Trace.next. Those are additional extraction
facts. Canonical first indices apply to literal source identities; semantic
aliases require the supplied Same certificate and are not automatically
canonicalized by this construction.

## 3. A finite cover needs only the current journal's bound

The new `SnapshotCover.snapshot` strengthens the available enumeration
interface. It assumes that the parents of **recorded packets in this one
reachable state** lie in the allocator frontier at depth N. It does not assume
InstalledDepthBound over all futures or all traces.

Its actual-trace induction proves:

1. Every current source/endpoint/output ID lies in the initial source pool
   plus reserved IDs allocated by those bounded parents. Refresh, aliasing,
   equating and observation cannot add an unsupported identity. Installation
   uses the existing exact reservation lemmas.
2. Every literal site occurrence lies in the finite occurrence-template list
   obtained from the parent frontier and the actual report enumeration.
3. Every currently Installable packet has a signature in the corresponding
   finite list of packet codes. The snapshot already contains its parent;
   the prospective installation need not be included in the historical bound.

The proof retains literal IDs and report data. It does not merge intervals
by overlap or endpoint equality, erase output constraints or equate different
source origins.

`PhaseLabels.PacketLabels` is a normalized finite syntactic realization of
a historical packet. It gives one capture substitution, the whole-head mass
comparison, and the children's normalized instantiated labels. Checked
Paterson descent proves strict mass decrease along every birth edge.
`packets_lineage` reconstructs each recorded packet parent's original birth
lineage; aliasing never resets it. One simultaneous realization of the current
journal therefore bounds every recorded parent by the current root-label
mass. Combining these lemmas constructs the snapshot cover.

The already closed ground producer is used directly by
`closed_packet_descent`: for an actual packet with finite input readbacks in
one model it produces the strict child inequalities and actual child Inputs.
No source-wide GroundRoots premise occurs in this local theorem. Extending
this input/capture correspondence to symbolic terms with opaque shared leaves
is part of the open readback construction, not an automatic corollary of the
ground theorem.

## 4. Phase well-foundedness avoids a uniform reset-size bound

A `HolePhases.PhaseCover` has a finite initial inventory indexed by H, an
invariant relating actual states to inventories, a finite signature list for
each inventory, and two obligations:

* Every actual update has a successor inventory connected by the existing
  `HoleElimination.Trace`, preserving the invariant. Its growth function is
  allowed to depend on this update.
* Every prospective installation in a represented state has a signature in
  that inventory's finite list.

There is no global bound on the sizes of replacement terms, the finite lists
at later phases, allocator ancestry, or execution length. A zero-elimination
Trace leaves the entire inventory equal. A positive Trace strictly decreases
the number of remaining holes. Concatenating traces with possibly different
growth functions gives `History`; `replay` proves

    total eliminations + remaining holes = initial holes,
    total eliminations ≤ |H|,

and validity of the resulting inventory. No new allocated ID becomes a new
member of H.

The accessibility proof is nested well-founded induction:

1. Outer measure: remaining hole count. A genuine elimination restarts the
   proof with fewer holes and any finite signature cover.
2. Within an unchanged inventory: the number of signatures in its finite
   cover still missing from the journal. A novel installation strictly
   decreases this number; other actual steps cannot increase it.
3. If both quantities are unchanged, the existing accessibility of passive
   administrative steps applies.

Every actual step is covered. The source-formation invariant excludes the
spurious enqueue case. This proves `HolePhases.accessible` without constructing
one finite cover for the whole source or an InstalledDepthBound.

The single remaining premise of `HolePhases.class_p_accessible` is named
`ClassPHolePhases`. The implication from the old ClassPInvocationBound is
proved: use its global SignatureCover and a constant inventory. Thus this
criterion is provably no stronger than the old uniform-depth criterion under
the stated source premises. It permits arbitrary finite reset sizes. In a
general infinitely branching transition system one rank drop can choose any
finite countdown, separating phase accessibility from a uniform numeric bound.
**Strict non-equivalence on this fixed Yulang carrier has not been proved.**
Calling the residual strictly logically weaker on that carrier would exceed
the established result. It is not a construction of ClassPHolePhases from
Checked and PointSource.

## 5. The remaining local source producer, without a growth premise

`HolePhaseSimulation.Simulation` is a sufficient, more concrete interface for
constructing the phase cover. It supplies an initial symbolic inventory and
its actual-state invariant, plus a simultaneous normalized realization of
all recorded packets. The root label is decoded from a term in the inventory.
For every actual Step it supplies a fixed-hole Trace and a successor
realization. There is no historical alias-mass, settlement-tree height,
source-wide depth or output-size premise.

`phase_cover` constructs the finite signature lists from this data; callers
do not supply a cover. `class_p_accessible` is proved under the single named
source premise `ClassPHoleReadback`, and `phases_of_readback` connects it to
§4's weaker finite-phase interface.

This local simulation is **not yet constructed for arbitrary point sources**.
Realized itself is syntactic: PacketLabels and data.decode do not assert an
actual-origin interpretation. The invariant is a supplied predicate, not a
constructed semantic invariant. Connecting these fields to IndexedHoleReadback
is explicitly part of the missing source construction.
The source frontier and root leaves are available, but the invariant must
still connect head-relevant dynamic IDs, captures, materialized outputs and
output-only binders to a simultaneous finite expression over the current
holes, preserving source keys and normalized counted labels. Every actual
refinement must either globally delete existing holes or preserve that
representation. A semantic equation, a fresh allocation, or a new observation
alone is not such a certificate. This is the remaining source extraction
link; packaging it in Simulation is not evidence that it holds.

The phase proof removes the need to bound the finite replacement's size
uniformly **for Acc**. Its finiteness and correct simultaneous source readback
still require proof. If a uniform settled-output growth function G is later
extracted, `fixed_growth_budget` and `fixed_growth_parent_depth` already give

    D(0) = initial depth,
    D(k+1) = D(k) + G(D(k)),
    root mass ≤ max { mass(decode(t)) : t ∈ enumerate H tests D(|H|) },
    installing-parent depth ≤ that same maximum.

They consume the original fixed-G HoleElimination.Trace. Together with its
source extraction, the existing allocation/report enumeration would again
give SignatureCover and SourceBudget. The arbitrary-reset phase theorem
itself proves Acc conditionally and does not assert that global SourceBudget.

No new infinite execution or semantic gap was found. No additional guard,
declaration rejection or owner decision was introduced. Unconditional
unknown-hole Class P Acc remains open; the ground-root theorem remains closed.

## 6. Verification and proof ownership

The yulang-proofs skill was used. The prescribed prover configuration and
policy files remain absent and the host has no registered callable prover
role. The primary constructed these derivations; no prover agent ran. An
independent reviewer checked the theorem scopes and phase argument.

Seven new modules are imported by appended lines in `lean/Yulang.lean`.
Audit entries are in the new `lean/Audit/ActualBoundaryHolePhases.lean`.
No existing Lean line, frozen file, specification or planning note is changed.
Final command results and review are recorded below.

Commands run with working directory `lean/`:

| Command | Exit code | Result |
| --- | --- | --- |
| `lake build Yulang.GeneralNominalActualBoundary Yulang.GeneralNominalSnapshotCover Yulang.GeneralNominalPhaseLabels Yulang.GeneralNominalHolePhases Yulang.GeneralNominalHolePhaseSimulation Yulang.GeneralNominalIndexedHoleReadback Yulang.GeneralNominalActualPhaseBoundary` | 0 | All seven modules; 817 jobs. |
| `lake build Yulang.GeneralNominalActualPhaseBoundary` | 0 | The same seven new modules are in its transitive imports. |
| `lake build Yulang` | 0 | Full aggregate; 2297 jobs. |
| `lake env lean Audit/ActualBoundaryHolePhases.lean` | 0 | All 29 declarations use only propext, Classical.choice and Quot.sound. |

An early `lake build Yulang.GeneralNominalActualBoundary` invocation from the
repository root exited 1 because that directory has no lake configuration.
It was rerun from `lean/`. Intermediate elaboration errors in the new modules
were corrected before the final successful checks above.

The independent reviewer ran the standalone audit and a separate
`lake env lean /dev/stdin` theorem-printing check, both exit 0. The printed
PhaseCover, Simulation, Class P residuals and progress theorem confirmed the
documented quantifiers. The reviewer found no blocking issue, including in
the arbitrary finite phase resets and the actual model-inclusion direction.

A read-only Python scope check exited 0: HEAD equals the integration baseline;
the only tracked changes are seven appended aggregate imports and one appended
design-index entry; the seven new modules contain no prohibited proof tokens;
the only new files are those modules, this note and its standalone audit.
Frozen files are unchanged. No git refs were changed. No Rust or parser tests
were run because this change adds Lean results and their design record only.
