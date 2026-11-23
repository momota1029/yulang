import Yulang.GeneralDeclarativeWitnessAssociatedDescriptor359

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessAssociatedBatch359
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Wire Described describe exact_authored_address)
open GeneralDeclarativeWitnessScopedBindings359 (Frame FrameKey)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeDemand320 (Demand)
open GeneralSourceState (Output)
open CommonDeclaredNominalInspection (Registry)

structure Ordered (e : Environment) (table : Registry) (frames : List Frame)
    (scope : FrameKey) (demand : Demand) (results : List Wire) where
  exactLength : results.length = demand.outputs.length
  positions : ∀ j wire,results[j]? = some wire →
    wire.ordinal = j ∧ Nonempty (Described e table frames scope demand wire)

def verify (e : Environment) (table : Registry) (frames : List Frame)
    (scope : FrameKey) (demand : Demand) (results : List Wire) : Bool :=
  decide (results.length = demand.outputs.length) &&
  (results.zipIdx).all fun entry => decide (entry.1.ordinal = entry.2) &&
    (describe e table frames scope demand entry.1).isSome

theorem accepted_exact_order {e table frames scope demand results}
    (checked : verify e table frames scope demand results = true) :
    Ordered e table frames scope demand results := by
  have both := Bool.and_eq_true_iff.mp checked
  refine ⟨of_decide_eq_true both.1,?_⟩
  intro j wire atEntry
  have located : (wire,j) ∈ results.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr atEntry
  have yes := Bool.and_eq_true_iff.mp (List.all_eq_true.mp both.2 _ located)
  constructor
  · exact of_decide_eq_true yes.1
  · cases produced : describe e table frames scope demand wire with
    | none => rw [produced] at yes; cases yes.2
    | some proof => exact ⟨proof⟩

theorem same_fixed_target_order {e table frames scope demand results}
    (proof : Ordered e table frames scope demand results) :
    results.map Wire.target = demand.outputs.map Output.target := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map]
  cases located : results[j]? with
  | none =>
    have a : results.length ≤ j := List.getElem?_eq_none_iff.mp located
    have b : demand.outputs[j]? = none := List.getElem?_eq_none_iff.mpr (proof.exactLength ▸ a)
    simp [b]
  | some row =>
    obtain ⟨ordinal,⟨built⟩⟩ := proof.positions j row located
    have trueOutput : demand.outputs[j]? = some built.requested := ordinal ▸ built.indexed
    simp [trueOutput,built.fixed]

end Yulang.GeneralDeclarativeWitnessAssociatedBatch359
