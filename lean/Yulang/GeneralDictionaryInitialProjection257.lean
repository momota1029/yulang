import Yulang.GeneralDictionaryFiveSlot257
namespace Yulang.GeneralDictionaryInitialProjection257
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryLooseIterationBook240 (context)
open GeneralDictionaryUpperHistory257 (history)
open GeneralPresenceOrderedBlock247 (solve)
open CommonNominalFullCarrier

/-- Fixed, stage-independent public observations: initial complete components
and all row components. The private type tail may be reconstructed. -/
def Agree (internal boundary : Assignment) : Prop :=
 (∀ name, name ≤ 4 → internal name = boundary name) ∧
 (∀ name, (internal name).2 = (boundary name).2)

theorem solve_agrees (n : Nat) (internal boundary : Assignment) (same : Agree internal boundary) :
 Agree (solve model (history n) internal) boundary := by
 constructor
 · intro name small
   have fixed : solve model (history n) internal name = internal name := by
     apply GeneralPresenceOrderedBlock247.solve_outside
     intro e member
     have above := GeneralDictionaryUpperHistory257.targets_above n e member
     omega
   exact fixed.trans (same.1 name small)
 · intro name
   exact (GeneralPresenceOrderedBlock247.solve_rows model (history n) internal name).trans (same.2 name)

theorem public_models (n : Nat) (boundary : Assignment) :
 (∃ internal, Agree internal boundary ∧ GeneralNominalState.Models (context n).state internal) ↔
 (∃ internal, Agree internal boundary ∧ (GeneralDictionaryFiveSlot257.view n).Models internal) := by
 constructor
 · rintro ⟨internal,same,valid⟩
   have blockValid : PresenceNormalForm.All model internal (GeneralPresenceDefinitionRewrite244.block (history n)) :=
     fun atom member => valid.2.2 atom (GeneralDictionaryUpperHistory257.block_in_source n member)
   have compact := (GeneralDictionaryCompactView257.recovered n internal blockValid).mpr valid
   exact ⟨internal,same,(GeneralDictionaryFiveSlot257.models_exact n internal).mp compact⟩
 · rintro ⟨internal,same,valid⟩
   have compact := (GeneralDictionaryFiveSlot257.models_exact n internal).mpr valid
   exact ⟨solve model (history n) internal,solve_agrees n internal boundary same,
     (GeneralDictionaryCompactView257.compact_solved n internal).mp compact⟩

/-- Exact stabilization of the raw-state public model projection for this
source-reachable family, not stabilization of its source journal or Step. -/
theorem stable (n : Nat) (boundary : Assignment) :
 (∃ internal, Agree internal boundary ∧ GeneralNominalState.Models (context (n+1)).state internal) ↔
 (∃ internal, Agree internal boundary ∧ GeneralNominalState.Models (context 1).state internal) := by
 rw [public_models,public_models,GeneralDictionaryFiveSlot257.stable]
end Yulang.GeneralDictionaryInitialProjection257
