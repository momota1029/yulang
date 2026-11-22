import Yulang.GeneralDeclarativeCurrentBodies345
import Yulang.GeneralDeclarativeStoppedFixture339

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDeclarativeNonPointBodies345
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (sourceRegistry checked)
open GeneralDictionaryCompoundFrame238 (installed effect)
open GeneralDictionaryCompoundStep238 (reachable)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeCurrentJoint345 (Block Attributed)
open GeneralDeclarativeCurrentOrder345 (rows exact_row Row)
open GeneralDeclarativeStoppedFixture339 (row fixed compiled_exact)
open CommonRoleOutermostResolver (All₂)

abbrev physicalOutput : Row := ⟨0,0,fixed⟩

theorem physical_row : physicalOutput ∈ rows installed.core root := by
  apply exact_row.mpr
  exact ⟨GeneralNominalDemandMerging.pointSite root,rfl,rfl,.refl _⟩

private theorem pair_found (good : All₂ P xs ys) (member : x ∈ xs) :
    ∃ y ∈ ys,P x y := by
  induction good with
  | nil => cases member
  | cons pair remains ih =>
    rcases List.mem_cons.mp member with rfl|later
    · exact ⟨_,List.mem_cons_self,pair⟩
    · obtain ⟨_,there,witness⟩ := ih later
      exact ⟨_,List.mem_cons_of_mem _ there,witness⟩

/-- Actual reachable compound installation with a nonpoint descriptor:
the old whole-state lowerer fails, but the real associated output is
still attributable and true in every actual valid post-model. -/
theorem actual (m : Assignment) (fit : Models installed m) :
    GeneralStoppedProjectedTrace335.normalized installed = none ∧
    ∃ equations, Block sourceRegistry root installed effect equations ∧
      row ∈ equations ∧ Holds m row := by
  obtain ⟨equations,paired,valid⟩ := GeneralDeclarativeCurrentBodies345.witnessed
    ⟨rfl,checked⟩ reachable (effect := effect) List.mem_cons_self m fit
  obtain ⟨got,there,made⟩ := pair_found paired physical_row
  obtain ⟨body,found,printed⟩ := made.1.authored
  have asPrinted : GeneralDictionaryAssociatedProvenance.lookup roles effect.plan.packet.declaration fixed.name =
      some (.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩) := rfl
  have same := Option.some.inj (found.symm.trans asPrinted)
  subst body
  have sameRow := Option.some.inj (printed.symm.trans compiled_exact)
  subst got
  exact ⟨GeneralDeclarativeStoppedFixture339.recognized_boundary,equations,paired,there,valid row there⟩

end Yulang.GeneralDeclarativeNonPointBodies345
