import Yulang.GeneralNominalInstallationSound190
import Yulang.GeneralNominalCenteredHeadWFJoinCounterexample

/-! The new operational sufficient condition is not asserted globally.
The existing supervisor-owned multi-tag materialization counterexample already
refutes it at a checked, reachable, stable source. This adapts that known
obstruction to the exact residual used by InstallationSound190. -/
namespace Yulang.GeneralNominalInstallationBoundary190
open GeneralNominalInstallationSound190
open GeneralNominalCenteredHeadWFJoinSource
open GeneralNominalCenteredHeadWFJoinLocal
open GeneralNominalCenteredHeadWFJoinCounterexample

theorem known_source_not_available : ¬ Available registry start root := by
  intro available
  obtain ⟨plan,support,frame,_,enabled⟩ := available root .root 37 children selected
  exact no_install plan frame.occurrence_eq support enabled

/-- Even checked reachable stable states do not suffice for universal actual
installation availability at the current WF boundary. This is a known source,
not a newly discovered language-design inconsistency. -/
theorem not_universal_available : ¬ (∀ (r : GeneralDeclarations.Registry),
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Checked r →
    ∀ state root,
    B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) r root state →
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Stable r state root →
    Available r state root) := by
  intro all
  exact known_source_not_available (all registry ⟨rfl,checked⟩ start root reachable stable)

end Yulang.GeneralNominalInstallationBoundary190
