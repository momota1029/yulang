import Yulang.GeneralDeclarativeRecordIntervals330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordMask330
open CommonNominalFullCarrier (Ty Row observeTy)
open CommonNominalFullDemand (Environment Observation MaskedProbeStep ProbeAt ProbeStep)
open GeneralDeclarativeRecordChannel330 (channel)

theorem same_guard {query label : Nat} {a b : List Nat} (same : query ∈ a ↔ query ∈ b) :
    (query = label ∧ label ∉ a) ↔ (query = label ∧ label ∉ b) := by
  constructor
  · rintro ⟨rfl,no⟩
    exact ⟨rfl,fun seen => no (same.mpr seen)⟩
  · rintro ⟨rfl,no⟩
    exact ⟨rfl,fun seen => no (same.mp seen)⟩

/-- Another hidden name cannot affect the requested record channel,
even through nested masks, defaults, joins and intersections. -/
theorem probe (key : Nat) (env : Environment Row) (order)
    (v : CommonNominalFullDemand.Ty Row) (optional : Bool) (a b : List Nat) (obs : Observation Row)
    (same : key ∈ a ↔ key ∈ b) :
    MaskedProbeStep Common.rowLe env order a v (channel optional key obs) ↔
      MaskedProbeStep Common.rowLe env order b v (channel optional key obs) := by
  cases v with
  | union left right =>
    cases optional
    · exact and_congr (probe key env order left false a b obs same) (probe key env order right false a b obs same)
    · exact and_congr (probe key env order left true a b obs same) (probe key env order right true a b obs same)
  | inter left right =>
    cases optional
    · exact or_congr (probe key env order left false a b obs same) (probe key env order right false a b obs same)
    · exact or_congr (probe key env order left true a b obs same) (probe key env order right true a b obs same)
  | mask labels inner =>
    have combined : key ∈ a ++ labels ↔ key ∈ b ++ labels := by simp only [List.mem_append,same]
    cases optional
    · exact probe key env order inner false _ _ obs combined
    · exact probe key env order inner true _ _ obs combined
  | exactEmpty =>
    cases optional
    · rfl
    · exact or_congr (not_congr same) Iff.rfl
  | record label payload tail =>
    have iffGate := same_guard (label := label) same
    by_cases here : key = label ∧ label ∉ a
    · have there := iffGate.mp here
      cases optional <;> simp [channel,MaskedProbeStep,here,there]
    · have nowhere : ¬(key = label ∧ label ∉ b) := fun proof => here (iffGate.mpr proof)
      cases optional
      · simpa [channel,MaskedProbeStep,here,nowhere] using probe key env order tail false a b obs same
      · simpa [channel,MaskedProbeStep,here,nowhere] using
          (or_congr (probe key env order tail true a b obs same) (Iff.rfl : (obs = .trivial) ↔ obs = .trivial))
  | recordDefault label source fallback =>
    have iffGate := same_guard (label := label) same
    by_cases here : key = label ∧ label ∉ a
    · have there := iffGate.mp here
      have equal := and_congr (probe key env order source true a b obs same)
        (or_congr (probe key env order source false a b .trivial same)
          (Iff.rfl : MaskedProbeStep Common.rowLe env order [] fallback obs ↔ _))
      cases optional
      · simpa [channel,MaskedProbeStep,here,there] using equal
      · simpa [channel,MaskedProbeStep,here,there] using
          (or_congr equal (Iff.rfl : (obs = .trivial) ↔ obs = .trivial))
    · have nowhere : ¬(key = label ∧ label ∉ b) := fun proof => here (iffGate.mpr proof)
      cases optional
      · simpa [channel,MaskedProbeStep,here,nowhere] using probe key env order source false a b obs same
      · simpa [channel,MaskedProbeStep,here,nowhere] using
          (or_congr (probe key env order source true a b obs same) (Iff.rfl : (obs = .trivial) ↔ obs = .trivial))
  | bottom | top | base | float | pair | emptyRecord | variant | arrow | nominal =>
    cases optional <;> rfl
termination_by sizeOf v

/-- Residual projection masks exactly the requested field; every
other required/optional channel is preserved at all observation
depths, including the zero approximation. -/
theorem other {forbid key : Nat} (diff : key ≠ forbid) (depth rank : Nat) (env : Environment Row)
    (v : Ty) (optional : Bool) (obs : Observation Row) :
    ProbeAt Common.rowLe rank env (observeTy depth (.mask [forbid] v)) (channel optional key obs) ↔
      ProbeAt Common.rowLe rank env (observeTy depth v) (channel optional key obs) := by
  have same : key ∈ [forbid] ↔ key ∈ ([] : List Nat) := by simp [diff]
  cases optional <;> cases rank
  · exact probe key env (fun _ _ => True) (observeTy depth v) false [forbid] [] obs same
  · rename_i rank
    exact probe key env (fun expected input => ∀ next test, ProbeAt Common.rowLe rank next input test →
      ProbeAt Common.rowLe rank next expected test) (observeTy depth v) false [forbid] [] obs same
  · exact probe key env (fun _ _ => True) (observeTy depth v) true [forbid] [] obs same
  · rename_i rank
    exact probe key env (fun expected input => ∀ next test, ProbeAt Common.rowLe rank next input test →
      ProbeAt Common.rowLe rank next expected test) (observeTy depth v) true [forbid] [] obs same

end Yulang.GeneralDeclarativeRecordMask330
