import Yulang.GeneralDeclarativeWitnessSpineDeepFixture355
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 75000000
namespace Yulang.GeneralDeclarativeWitnessSpineDeepModel355
open GeneralDeclarativeWitnessGrandchildModel355 (model covers atomOK atom_sound supportedEquations)
open GeneralDeclarativeWitnessSpineDeepFixture355 (test actual_five_nodes data plan receipt)
open GeneralDeclarativeWitnessSpineDeepSeed355 (root)
open GeneralDeclarativeWitnessNominalSpine355 (Code NodeMeaning)
open GeneralDeclarativeWitnessNominalSpineWhole355 (Found run sound)
open GeneralDeclarativeWitnessTypedReemit354 (Wire Linked decode)
open GeneralDeclarativeWitnessCovariantOrigin353 (Valuation)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

theorem fixture_supported : (data.map fun (s,_,_) => covers s).getD false = true := by decide +kernel

theorem fits {s : State} {top : Wire} {rest : Code} (found : data = some (s,top,rest)) : Models s model := by
  have verified := fixture_supported
  rw [found] at verified
  have ⟨facts,erows⟩ := GeneralDeclarativeWitnessProblem349.splitAnd (show covers s = true from verified)
  have ⟨atoms,intervals⟩ := GeneralDeclarativeWitnessProblem349.splitAnd facts
  have noIntervals := List.isEmpty_iff.mp intervals
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a used
    exact atom_sound a (List.all_eq_true.mp atoms _ used)
  · intro pair used
    rw [noIntervals] at used
    cases used
  · intro e used
    have literal := of_decide_eq_true (List.all_eq_true.mp erows _ used)
    simp only [supportedEquations,List.mem_cons,List.not_mem_nil,or_false] at literal
    rcases literal with rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem actual_finite_chain_single_model :
    ∃ (s : State) (w : Wire) (r : Code) (top : Linked root s w) (a : Found top plan receipt),
      data = some (s,w,r) ∧ Models s model ∧
      receipt.result = .selected (GeneralDeclarativeWitnessNominalSpineWhole355.selectedDictionary top a.node) ∧
      (∀ edge ∈ a.node.hops,edge.1 = (GeneralDeclarativeWitnessSpineNode355.Node.ofFirst top plan.startVersion).valueName ∧
        edge.2.1 = (GeneralDeclarativeWitnessSpineNode355.Node.ofFirst top plan.startVersion).valueName) ∧
      ∃ v : Valuation, ∀ n ∈ a.node.nodes,NodeMeaning model v n := by
  have passed := actual_five_nodes
  unfold test at passed
  cases got : data with
  | none => rw [got] at passed; cases passed
  | some row =>
    obtain ⟨s,w,r⟩ := row
    have tested : ((decode root s w).map (fun top => (run top plan r receipt).isSome)).getD false = true :=
      by simpa [got] using passed
    cases linked : decode root s w with
    | none => rw [linked] at tested; cases tested
    | some top =>
      cases proof : run top plan r receipt with
      | none => simp [linked,proof] at tested
      | some a =>
        have m := fits got
        have read := sound a model m
        exact ⟨s,w,r,top,a,rfl,m,read.2.1,
          GeneralDeclarativeWitnessRetainedCut355.no_distinct_physical_sites_along_spine a.node,read.2.2.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessSpineDeepModel355
