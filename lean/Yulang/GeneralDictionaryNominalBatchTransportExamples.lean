import Yulang.GeneralDictionaryNominalBatchTransport
import Yulang.GeneralDictionaryNominalSlotTransportExamples

/-! Nonempty repeated dictionary obligations and separate arrow row identities
survive strict slot transport. The nominal fixture has an actual descriptor and
a joint model; the arrow-term check is an evaluation identity, not a claim that
this role demand has an arrow-valued survivor. -/
namespace Yulang.GeneralDictionaryNominalBatchTransportExamples
open GeneralDictionaryNominalBatchTransport
open GeneralDictionaryNominalSlotTransportExamples (mixedBefore mixedAfter mixedTransport mixedAssignment)
open GeneralDictionaryStateEquations (Located liftType)
open GeneralDictionaryBatchRecording (Item)
open GeneralDictionaryTypeCoverageExamples (roles)
open Core.PresenceGeneration (TyTerm)

abbrev demand : GeneralSourceState.Demand roles where
  role := 0
  arguments := fun _ => (77, 77)
  outputs := [⟨0, 10⟩, ⟨0, 10⟩]
  declared := by intro _ _; exact ⟨none, rfl⟩

def oldLocated : Located mixedBefore.base demand where
  lower := fun _ => 1
  upper := fun _ => 1
  head := fun _ => .var 1
  target := fun _ => 0
  output := fun _ => .var 0
  arguments := by intro _; rfl
  targets := by
    intro index
    obtain ⟨i, bound⟩ := index
    change i < 2 at bound
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;> rfl

abbrev oldItem : Item roles mixedBefore.base := ⟨demand, oldLocated⟩
abbrev batch : List (Item roles mixedBefore.base) := [oldItem, oldItem]

theorem lifted_arrow_separate :
    liftType mixedAfter.base
      ((TyTerm.arrow (.var 1) (.var 1) (.var 1) (.var 1)).rename mixedTransport.embed) =
      .arrow (.var 77) (.var 43) (.var 77) (.var 43) := rfl

/-- The same finite nominal assignment satisfies all repeated obligations. -/
theorem old_item_holds : GeneralDictionaryNominalEquations.Holds oldLocated.equations mixedAssignment := by
  constructor
  · intro index
    exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
  · intro index
    obtain ⟨i, bound⟩ := index
    change i < 2 at bound
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl <;>
      exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩

theorem repeated_batch_joint :
    GeneralNominalState.Models (GeneralDictionaryNominalRecording.record mixedBefore batch) mixedAssignment ∧
      GeneralNominalState.Models
        (GeneralDictionaryNominalRecording.record mixedAfter (items mixedTransport batch)) mixedAssignment := by
  have old : GeneralNominalState.Models (GeneralDictionaryNominalRecording.record mixedBefore batch) mixedAssignment := by
    apply (GeneralDictionaryNominalRecording.record_models mixedBefore batch mixedAssignment).mpr
    refine ⟨GeneralDictionaryNominalSlotTransportExamples.mixed_nominal_nonvacuous.1, ?_⟩
    intro item member
    have same : item = oldItem := by simpa only [batch, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
    subst item
    exact old_item_holds
  exact ⟨old, (record_models mixedTransport batch mixedAssignment).mpr old⟩

theorem repeated_batch_not_collapsed :
    (items mixedTransport batch).length = 2 ∧
      ((items mixedTransport batch).map fun item => item.demand.outputs.length) = [2, 2] := ⟨rfl, rfl⟩

theorem all_assignment_recording_exact (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models
      (GeneralDictionaryNominalRecording.record mixedAfter (items mixedTransport batch)) model ↔
        GeneralNominalState.Models (GeneralDictionaryNominalRecording.record mixedBefore batch) model :=
  record_models mixedTransport batch model

end Yulang.GeneralDictionaryNominalBatchTransportExamples
