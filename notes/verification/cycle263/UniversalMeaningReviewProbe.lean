import Yulang.GeneralRebaseUniversalTrace263
import Yulang.GeneralRebaseUniversalRegression263
open Yulang GeneralRebaseUniversalRegression263
open GeneralRebaseTwoOwnerRegression263 (owners representative first last firstPlan lastPlan)
open GeneralRebaseMergeRequests261 (outputs)

private theorem compatible_self (plan : GeneralNominalCenters.Plan roles)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralRebaseNormalizedBody263.Compatible plan plan assignment :=
 ⟨⟨rfl,rfl,rfl⟩,fun _ _ _ _ => GeneralDictionaryDefaultExpression209.equivalent_refl _,
 fun _ => GeneralDictionaryDefaultExpression209.equivalent_refl _⟩

-- Even with the retained unused reservation, final meaning is precisely both
-- actual written effect tables, not a demand to install or validate all pool keys.
example (base : GeneralNominalCommonBridge.Assignment → Prop) (assignment) :
 GeneralRebaseUniversalMeaning263.Models base owners representative finish assignment ↔
 base assignment ∧ GeneralRebaseClassTable261.Effects firstPlan outputs assignment ∧
 GeneralRebaseClassTable261.Effects lastPlan outputs assignment := by
 have one : ∀ assignment, base assignment → GeneralRebaseNormalizedBody263.Compatible
   (representative first.owner) firstPlan assignment := by
  intro assignment _
  rw [GeneralRebaseTwoOwnerRegression263.rep_first]
  exact compatible_self _ _
 have two : ∀ assignment, base assignment → GeneralRebaseNormalizedBody263.Compatible
   (representative last.owner) lastPlan assignment := by
  intro assignment _
  rw [GeneralRebaseTwoOwnerRegression263.rep_last]
  exact compatible_self _ _
 rw [GeneralRebaseUniversalMeaning263.write_exact base owners representative pool last.owner
   (List.mem_cons_of_mem _ (List.mem_singleton_self _)) lastPlan outputs
   (fun _ member => List.mem_append_left _ member) two middle assignment]
 rw [GeneralRebaseUniversalMeaning263.write_exact base owners representative pool first.owner
   List.mem_cons_self firstPlan outputs (fun _ member => List.mem_append_left _ member) one start assignment]
 rw [GeneralRebaseUniversalMeaning263.initial_exact]
 exact and_assoc

#print axioms GeneralRebaseUniversalMeaning263.actual_proposal
#print axioms GeneralRebaseUniversalMeaning263.write_exact
#print axioms GeneralRebaseUniversalMeaning263.actual_write
#print axioms GeneralRebaseUniversalMeaning263.initial_exact
#print axioms GeneralRebaseUniversalTrace263.models_exact
#print axioms GeneralRebaseUniversalTrace263.from_checked
#print axioms GeneralRebaseUniversalTrace263.certificate
