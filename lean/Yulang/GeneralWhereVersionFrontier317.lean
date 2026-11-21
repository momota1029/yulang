import Yulang.GeneralWhereVersionReobserved317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 33000000
namespace Yulang.GeneralWhereVersionFrontier317
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralLiveCompoundChildSite316 (child signature)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralWhereVersionCase317 (occ site)
open GeneralWhereVersionCommit317 (core produced)
open GeneralWhereVersionRootReport317 (plan)
open GeneralWhereVersionCompiler317 (children)
open GeneralNominalSaturationState (Generated)

/-- The legacy child edge was neither erased nor rewritten. -/
theorem prior_generated : Generated core.erased.current root child := by
  apply Generated.child .root
  change (root,child) ∈ after.core.erased.current.edges ++ _
  apply List.mem_append_left
  change (root,child) ∈ GeneralLiveCompoundUpperRefresh316.upperState.core.erased.current.edges ++ _
  apply List.mem_append_left
  exact GeneralNominalVersionedInstall232.installed_child
    (GeneralLiveCompoundChildSite316.children ▸ List.mem_singleton_self _)

theorem same_identity : occ.identity = child.identity := by
  have h := GeneralWhereVersionCompiler317.child_owner rootPlan otherChild signature
  change occ.identity = (GeneralNominalVersionedFrame231.childSite
    (GeneralNominalVersionedTransport231.extendedPlan _ _ _ GeneralLiveCompoundCurrentRoot316.plan)
    otherChild signature).occurrence.identity at h
  rw [GeneralNominalVersionedTransport231.childSite_eq,
    GeneralLiveCompoundPostRootHead316.child_site signature] at h
  exact h

theorem current_not_historical : child ∉ children plan := by
  rw [GeneralWhereVersionReobserved317.rows_and_occurrence.2]
  intro member
  exact GeneralWhereVersionLeafRegistry317.corrected_not_old (List.mem_singleton.mp member).symm

/-- The cumulative generated graph is deliberately not the current ordered
compiler frontier. Preserving both history and current addresses requires
using the full occurrence, not identifying children by their owner alone. -/
theorem historical_and_current :
    Generated core.erased.current root child ∧ Generated core.erased.current root occ ∧
    occ.identity = child.identity ∧ occ ≠ child ∧
    children plan = [occ] ∧ child ∉ children plan :=
  ⟨prior_generated,produced,same_identity,GeneralWhereVersionLeafRegistry317.corrected_not_old,
    GeneralWhereVersionReobserved317.rows_and_occurrence.2,current_not_historical⟩

end Yulang.GeneralWhereVersionFrontier317
