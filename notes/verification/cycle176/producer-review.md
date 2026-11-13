# Centered selected-plan producer review (cycle176)

Positive result: `selected_candidate` constructs a current-context plan from an
actual centered finite trace, generated focus, and centered selected Local.
`reachable_candidate` specializes this to exact G Reachable, allowing root or
Generated. Neither assumes Joint, stability, source soundness, nor installation.
Candidate has ledger registration, declaration identity, exact ordered children,
Prepared inspection and one packet branch-model witness. Lean trust-zero source
and two-declaration audit exit 0; only propext/Classical.choice/Quot.sound.

What is NOT obtained: the branch witness is NOT claimed to satisfy every prior
packet, every center site, or every recorded centered plan equation. Existence
of a current centered model and existence of a packet branch model cannot be
conjoined without an amalgamation proof.

The already existing `GeneralNominalCenteredInspection.selected_installable_iff`
reduces centered installation, GIVEN raw FeedbackSteps.Installable and registered
input, to (1) ValueSupport.PacketGuard for some support and (2) a single model
satisfying Centered.Models and plan.Holds. It already derives decision support,
Safe, AlternativesSafe and cycle exclusion from selected Local. These should
not be restated as new unsolved independent fields.

Raw installation additionally needs Joint and raw MergesClosed; the existing
`GeneralNominalCenteredSelection.selected_base_plan` consumes precisely those.
Local still uses the ordinary survivor relation, whose consistency witness is
per-branch. It does not contain Joint. Centered stability blocks centered At;
it does not immediately supply raw MergesClosed (raw recovered inputs and
centered inputs use distinct ledgers/model predicates), nor value-support
witnesses for every prospective install. Reachable invariants may imply these,
but no such theorem was found and none is claimed here.

Therefore ModeledSelectedInstallable remains a sufficient residual producer,
not a proved consequence of G. No reachable stable modeled counterexample to G
EvidenceNode has been established. Failure to derive this stronger producer is
not itself a refutation of EvidenceNode; historical current-instance proofs
could in principle close EvidenceNode without reinstallability.

Fresh integration19462 adds `GeneralNominalCenteredSelectionCounterexample`.
Its ground_reachable + child_selected + child_not_installable show that G
reachability and Local selection alone DO NOT suffice for plan availability.
Its required_merge_step explicitly supplies a step at child10, so the example
is not Stable at that focus. It does not refute ModeledSelectedInstallable,
which retains Stable, nor the requested EvidenceNode. This is a concrete reason
not to drop stability while connecting candidate production to guarded plans.
`GeneralNominalCenteredModelExtension` supplies fresh-name model extension, not
general joint/alias closure or ValueSupport guard construction.

## Targeted merge closure

New `GeneralDictionaryCenteredSharedMerge176` proves exact shared-name closure:
for arbitrary Stable centered state at root, registered first/last center sites,
a Generated first occurrence, same role and identical ordered observed input
names, the two occurrence IDs are Alias. No support or model-equality premise
is hidden: `named_merge_guard` constructs legacy MergeGuard using empty support,
and `recovered_observed` shows explicit center origins need no recovery.
The four public theorems have trust-zero source/audit exit0.

This does not prove raw MergesClosed from Stable for all raw semantic input
equalities. Raw FeedbackSites.SameInputs quantifies ordinary journal Models on
recovered sites; centered SameInputs quantifies Centered.Models on explicit
centers. Centered At.merge also retains SupportChoices.MergeGuard quantifying
legacy Slice models. These are distinct predicates/representations.

`CenteredTrace.point_at` preserves `ReobservationOrder.Point`: a descriptor
property indexed by a source ID, whose nominal parameters have point bounds.
It is NOT `CenteredPointSource.Point occurrence`, which says every demand
argument has equal endpoint IDs. `CenteredAncestry.sites_bounded` produces
per-model finite labels and `GroundAccessibility.Inputs`; Inputs asserts Fits
(interval containment) of closed terms plus observed-center value equality.
It does not assert equal endpoint IDs at every generated occurrence. Thus those
theorems alone do not identify all generated raw sites with centered pointSite.
No stable raw/centered mismatch counterexample is asserted.

## Model-inhabited actual fragment

`GeneralDictionaryCenteredInhabited176` defines proof-indexed MergeAligned over
actual centered At. Administrative, refresh, and install actions are accepted
without extra premises. A merge is accepted when matching output names have
the same target Nat. This syntactic rule implies all added output atoms in any
model, so aligned_merge_models is a per-model equivalence. Actual installation
already supplies a common model in PacketGuard. Consequently at_inhabited,
step_inhabited and trace_inhabited preserve existence of a centered model.
AlignedStep/trace_actual exhibit inclusion into the original actual relation;
G is not changed. Arbitrary G traces need not satisfy this fragment, and general
merge consistency is not claimed. Seven public theorems: trust-zero build/audit
exit0, only propext/Classical.choice/Quot.sound.
