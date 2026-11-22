import Yulang.GeneralDeclarativeNestedModels332
import Yulang.GeneralDeclarativeNestedIndex332

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000

namespace C332FirstHitContrast
open Yulang
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeNestedExample332 (state rows interpretation pat uses)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeNestedDecode332 (normalized)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarationExamples (constructors)

abbrev aliasRow : Equation := ⟨0,.variable 0⟩
abbrev current := appendFacts state [aliasRow]

def supported : Supported current (fun _ => False) :=
  ⟨fun row origin => row ∈ current.equations ∧ origin = .source,fun h => h.1⟩

noncomputable def headFirst := ofRows (aliasRow::rows) (fun _ found => by
  apply from_source supported
  rcases List.mem_cons.mp found with rfl|other
  · exact ⟨List.mem_append_right _ List.mem_cons_self,rfl⟩
  · exact ⟨List.mem_append_left _ other,rfl⟩)

noncomputable def structuralFirst := ofRows rows
  (fun _ found => from_source supported ⟨List.mem_append_left _ found,rfl⟩)

theorem same_models m : Models current m ↔ Models state m := by
  have kept : ∀ e ∈ [aliasRow], GeneralDeclarativeEntailment320.Entails state e := by
    intro e h _ _
    cases List.mem_singleton.mp h
    exact eqv_refl _
  exact GeneralDeclarativeEntailment320.conservative_append kept m

theorem bad_first : normalized headFirst constructors interpretation .actual (.variable 0) pat = none := rfl
theorem good_first :
    normalized structuralFirst constructors interpretation .actual (.variable 0) pat =
      some (uses .actual) := rfl

theorem present_model : ∃ m, Models current m :=
  ⟨_,(same_models _).mpr GeneralDeclarativeNestedModels332.initial⟩

-- This is an index limitation on the same ordinary state, not an accepted
-- stable source counterexample, diagnostic rule, or selection priority.
#print axioms bad_first
#print axioms good_first
#print axioms present_model
end C332FirstHitContrast
