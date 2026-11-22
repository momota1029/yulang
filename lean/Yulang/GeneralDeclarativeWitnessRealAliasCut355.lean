import Yulang.GeneralDeclarativeWitnessSpineFrontModel355
import Yulang.GeneralDeclarativeWitnessGrandchildFixture355
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 60000
set_option maxHeartbeats 60000000
namespace Yulang.GeneralDeclarativeWitnessRealAliasCut355
open GeneralDeclarativeWitnessGrandchildFixture355 (data plan)
open GeneralDeclarativeWitnessGrandchildSeed355 (seed)
open GeneralDeclarativeWitnessTypedReemit354 (Wire Linked decode)
open GeneralDeclarativeWitnessRangeRelease355 (Released)
open GeneralDeclarativeWitnessTypedReemitModel354 (model covers atomOK atom_sound supportedEquations)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Equivalent)

theorem actual_alternative_state :
    ((data 9).map (fun (s,_,_) => covers s)).getD false = true := by decide +kernel

theorem fits {s : State} {w : Wire} {leaf : GeneralDeclarativeWitnessGrandchild355.Wire}
    (got : data 9 = some (s,w,leaf)) : Models s model := by
  have verified := actual_alternative_state
  rw [got] at verified
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

def retainedEquation : Equation := ⟨10,.variable 9⟩

theorem actual_ordinary_alias_row :
    ((data 9).map (fun (s,_,_) => decide (retainedEquation ∈ s.equations))).getD false = true := by
  decide +kernel

theorem all_actual_models_agree_on_values {s : State} {w : Wire} {leaf : GeneralDeclarativeWitnessGrandchild355.Wire}
    (got : data 9 = some (s,w,leaf)) (m : GeneralNominalCommonBridge.Assignment) (fit : Models s m) :
    Equivalent (m 9).1 (m 10).1 := by
  have retained := actual_ordinary_alias_row
  rw [got] at retained
  have indexed : retainedEquation ∈ s.equations := of_decide_eq_true retained
  have same := fit.2 retainedEquation indexed
  exact ⟨same.2,same.1⟩

def localExample : Bool :=
  ((data 9).map (fun (s,w,_) => ((decode (seed 9) s w).map (fun a =>
    ((GeneralDeclarativeWitnessRangeRelease355.read a plan.authority plan.producer plan.writeIndex).map (fun r =>
      decide (a.receiver.compiled.readFrom.center.anchor.current.valueName = 9 ∧
        r.body.indexed.demand.target = 10))).getD false)).getD false)).getD false

theorem actual_existing_authority_and_distinct_center :
    localExample = true := by decide +kernel

theorem no_grandchild_at_released_site {i s w} {a : Linked i s w}
    (r : Released a plan.authority plan.producer plan.writeIndex)
    (different : r.body.indexed.demand.target ≠ a.receiver.compiled.readFrom.center.anchor.current.valueName)
    (wire : GeneralDeclarativeWitnessGrandchild355.Wire) :
    ¬ Nonempty (GeneralDeclarativeWitnessGrandchild355.Accepted a plan wire) := by
  rintro ⟨found⟩
  have slots := Option.some.inj (r.body.indexed.indexed.symm.trans found.released.body.indexed.indexed)
  have child := List.mem_of_getElem? found.actuallyEmitted
  have picked : found.results.facts.arg ∈ found.demand.arguments := by
    have shape := found.results.facts.shape
    change found.demand.arguments = [_] at shape
    rw [shape]
    exact List.mem_cons_self
  have trueCenter := GeneralDeclarativeWitnessRetainedCut355.cannot_rename_to_fixed_target a.receiver.compiled child picked
  have authorized := GeneralDeclarativeWitnessGrandchild355.exact_target found
  exact different ((congrArg GeneralSourceState.Output.target slots).trans (authorized.symm.trans trueCenter))

theorem witnessed_alias_never_repairs_the_actual_site :
    ∃ (s : State) (w : Wire) (leaf : GeneralDeclarativeWitnessGrandchild355.Wire)
      (a : Linked (seed 9) s w) (r : Released a plan.authority plan.producer plan.writeIndex),
      data 9 = some (s,w,leaf) ∧ Models s model ∧
      Equivalent (model 9).1 (model 10).1 ∧
      r.body.indexed.demand.target = 10 ∧
      a.receiver.compiled.readFrom.center.anchor.current.valueName = 9 ∧
      ∀ code, ¬ Nonempty (GeneralDeclarativeWitnessGrandchild355.Accepted a plan code) := by
  have yes := actual_existing_authority_and_distinct_center
  unfold localExample at yes
  cases got : data 9 with
  | none => rw [got] at yes; cases yes
  | some tuple =>
    obtain ⟨s,w,leaf⟩ := tuple
    cases first : decode (seed 9) s w with
    | none => simp [got,first] at yes
    | some a =>
      cases release : GeneralDeclarativeWitnessRangeRelease355.read a plan.authority plan.producer plan.writeIndex with
      | none => simp [got,first,release] at yes
      | some claim =>
        have localSpec : decide (a.receiver.compiled.readFrom.center.anchor.current.valueName = 9 ∧
            claim.body.indexed.demand.target = 10) = true := by simpa [got,first,release] using yes
        obtain ⟨center,target⟩ := of_decide_eq_true localSpec
        have fit := fits got
        have sem := all_actual_models_agree_on_values got model fit
        exact ⟨s,w,leaf,a,claim,rfl,fit,sem,target,center,
          no_grandchild_at_released_site claim (by rw [target,center]; decide)⟩
end Yulang.GeneralDeclarativeWitnessRealAliasCut355
