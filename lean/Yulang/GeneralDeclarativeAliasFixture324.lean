import Yulang.GeneralDeclarativeHiddenPath324
import Yulang.GeneralDeclarativeOutputIdentity324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAliasFixture324
open GeneralDeclarativeHiddenDecl324
open GeneralDeclarativeHiddenState324
open GeneralDeclarativeExampleSource320 (point)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds literal)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeReobserve324 (Reobserves ordinary_reobserved)
open GeneralDeclarativeOutputIdentity324 (keep_old_rules)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm)
open GeneralDeclarativeRepeat320 (top_not_int)

abbrev changed : Names := ⟨fun n => point (if n = 0 then 3 else 55),fun _ => 55⟩
abbrev newChild : GeneralDeclarativeDemand320.Demand := ⟨2,[point 3],[⟨1,55⟩]⟩
abbrev newReturn : Equation := ⟨6,.variable 55⟩
abbrev aliasRow : Equation := ⟨55,.variable 5⟩

theorem same_actual_head : fact catalogue interpretation names.input (point 0) raw =
    fact catalogue interpretation changed.input (point 0) raw := rfl

theorem redirected_child : children parent changed place = [newChild] := rfl

theorem current_source : SourceEquation registry interpretation root parent changed.input newReturn :=
  ⟨⟨0,6⟩,List.mem_cons_self,.explicit out,.explicit _ List.mem_cons_self rfl,.variable 1,rfl,rfl⟩

def mixed : Assignment := fun n => if n = 55 then (.top, Common.rowEmpty) else assignment true n

theorem mixed_model : Models final mixed := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ never => False.elim (List.not_mem_nil never)⟩,?_⟩
  intro row there
  change row ∈ finalRows at there
  simp only [finalRows,s0Rows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

/-- Matching the same input head is insufficient if a where-output
identity was changed and no ordinary equation links its old and new
values. This says nothing against approved stable source selection. -/
theorem changed_target_not_stable :
    ¬StableUnder final (SourceEquation registry interpretation root parent changed.input) := by
  intro assumed
  have h := stable_exact.mp assumed _ current_source mixed mixed_model
  exact top_not_int h.2

abbrev joined : State := appendFacts final [aliasRow]

theorem linked : Reobserves joined parent names.input changed.input := by
  intro m good
  constructor
  · intro v there
    change v ∈ [0] at there
    cases List.mem_singleton.mp there
    exact eqv_refl _
  · intro v there
    change v ∈ [1] at there
    cases List.mem_singleton.mp there
    exact eqv_symm (good.2 _ (List.mem_append_right _ List.mem_cons_self))

theorem same_rule_after_ordinary_alias :
    StableUnder joined (SourceEquation registry interpretation root parent changed.input) :=
  ordinary_reobserved checked List.mem_cons_self linked
    (keep_old_rules (fun m good => ((model_append m).mp good).1) stable_root)

theorem joined_inhabited :
    Models joined (assignment true) ∧
    StableUnder joined (SourceEquation registry interpretation root parent changed.input) :=
  ⟨(model_append _).mpr ⟨fits_final,by
      intro _ mem; cases List.mem_singleton.mp mem; exact eqv_refl _⟩,
   same_rule_after_ordinary_alias⟩

end Yulang.GeneralDeclarativeAliasFixture324
