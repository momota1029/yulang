import Yulang.GeneralDeclarativeProvisionalFailure323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProvisionalClosure323
open GeneralDeclarativeProvisionalFixture323
open GeneralDeclarativeProvisionalSelect323 (before_tree localRule)
open GeneralDeclarativeProvisionalFailure323 (real_fixed_row not_compiles)
open GeneralDeclarativeExistingFixture322 (state equations model valid)
open GeneralDeclarativeExampleSource320 (root child registry interp leaf point checked)
open GeneralDeclarativeExampleTree320 (dictionary)
open GeneralDeclarativeEmissionClassify322 (actual_source_tree actual_source_models)
open GeneralDeclarativeEmissionFixture322 (leafNames)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputExact323 (append_exact)
open GeneralDeclarativeOutputs320 (OutputMeaning)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)

abbrev closed : State := appendFacts before [row]

theorem split_row (e : Equation) (found : e ∈ state.equations) :
    e ∈ before.equations ∨ e = row := by
  change e ∈ equations at found
  by_cases same : e.left = 5
  · simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> first | exact .inr rfl | cases same
  · exact .inl (List.mem_filter.mpr ⟨found,by simpa using same⟩)

theorem row_in_state : row ∈ state.equations := by simp [state,equations]

/-- Reinstating the actual missing row restores exactly the original
ordinary model set, not just one specially chosen model. -/
theorem closed_model_iff (m : Assignment) : Models closed m ↔ Models state m := by
  rw [model_append]
  constructor
  · rintro ⟨old,added⟩
    refine ⟨old.1,?_⟩
    intro e there
    rcases split_row e there with stays|rfl
    · exact old.2 _ stays
    · exact added row List.mem_cons_self
  · intro all
    exact ⟨⟨all.1,fun e found => all.2 e (subsetOrdinary found)⟩,
      fun e found => (List.mem_singleton.mp found).symm ▸ all.2 row row_in_state⟩

theorem closure_exact (m : Assignment) :
    Models closed m ↔ Models before m ∧
      OutputMeaning registry.roles registry.constructors interp leaf child leafNames.input m ⟨1,5⟩ :=
  append_exact checked (List.mem_cons_of_mem _ List.mem_cons_self) real_fixed_row m

theorem contrast (m : Assignment) (settled : Models closed m) :
    Classify localRule root (.selected dictionary) ∧ Evidence registry interp m root dictionary :=
  ⟨before_tree,actual_source_models m ((closed_model_iff m).mp settled)⟩

theorem closure_inhabited :
    Models closed model ∧ Evidence registry interp model root dictionary := by
  have consistent := (closed_model_iff model).mpr valid
  exact ⟨consistent,(contrast model consistent).2⟩

end Yulang.GeneralDeclarativeProvisionalClosure323
