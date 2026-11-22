import Yulang.GeneralDeclarativeCurrentSnapshot345
import Yulang.GeneralLiveCompoundFullResult316
import Yulang.GeneralDeclarativeRootReplay344

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDeclarativeCurrentBarrier345
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry boundary_checked)
open GeneralLiveCompoundLeafInstall316 (after reachable after_model)
open GeneralLiveCompoundPostFrames316 (rootPlan no_root_packet)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalCenteredHeadDefaultSchemas (RequestsDeclared)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralDeclarativeCurrentOrder345 (Row rows exact_row)
open GeneralWhereVersionInstall317 (Journal)
open GeneralDeclarativeRootReplay344 (batch actualDemand requests_exact)
open GeneralDeclarativeRawCapture344 (rawCap)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (Holds)

noncomputable abbrev view : Journal roles := ⟨after,[]⟩
abbrev rootRow : Row := ⟨0,0,⟨0,4⟩⟩

theorem root_row : rootRow ∈ rows after.core root := by
  apply exact_row.mpr
  refine ⟨GeneralNominalDemandMerging.pointSite root,?_,rfl,.refl _⟩
  change after.core.erased.current.sites[0]? = _
  rw [GeneralLiveCompoundPost316.raw_sites_after]
  rfl

theorem ready : RequestsDeclared after.core root rootPlan ∧ Ready after.core root rootPlan := by
  obtain ⟨declared,ready,_⟩ := GeneralDeclarativeCurrentSnapshot345.from_reached_frame boundary_checked
    reachable GeneralLiveCompoundPostRootHead316.frame
  exact ⟨declared,ready⟩

theorem known_without_packet :
    (∀ next, ¬ Step registry root after next) ∧
    RequestsDeclared after.core root rootPlan ∧ Ready after.core root rootPlan ∧
    rootRow ∈ rows after.core root ∧
    (∀ m, Models after m → ¬ GeneralNominalVersionedPlans231.Holds rootPlan m) := by
  exact ⟨GeneralLiveCompoundStable316.halted,ready.1,ready.2,root_row,fun _ => no_root_packet⟩

theorem literal_targets : (actualDemand rootPlan view).outputs.map GeneralSourceState.Output.target = [4] := by
  rw [requests_exact,GeneralLiveCompoundPostRootHead316.frame.occurrence_eq]
  classical
  unfold GeneralNominalCenteredHeadOutputs.requests
  change ((after.core.erased.current.sites.filter _).flatMap _).map _ = _
  rw [GeneralLiveCompoundPost316.raw_sites_after]
  have yes : GeneralNominalSaturationState.Alias after.core.erased.current root.identity
      (GeneralNominalDemandMerging.pointSite root).occurrence.identity := .refl _
  simp [List.filter_cons,yes]
  split <;> rfl

/-- Even the completed associated-output equations can be replayed in the
actual terminal model; this does not recover the missing where packet. -/
theorem held_outputs_without_packet :
    ∃ rs, collect (one rootPlan.packet.registry rootPlan.packet.context.interpretation
           rootPlan.packet.declaration (actualDemand rootPlan view) (rawCap rootPlan))
         (actualDemand rootPlan view).outputs = some rs ∧
      rs.map Equation.left = [4] ∧ (∀ equation ∈ rs,Holds w equation) ∧
      ¬ GeneralNominalVersionedPlans231.Holds rootPlan w := by
  obtain ⟨rs,ran,targets,valid⟩ := batch rootPlan view w rfl ready.2 GeneralLiveCompoundPostRootSelect316.classes
  exact ⟨rs,ran,targets.trans literal_targets,valid,no_root_packet after_model⟩

end Yulang.GeneralDeclarativeCurrentBarrier345
