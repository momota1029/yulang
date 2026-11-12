import Yulang.GeneralDictionaryNominalSlotTransport
import Yulang.GeneralDictionaryNominalRecording

/-!
# Dictionary batch meaning across certified nominal slot transport

The source-indexed demands do not change. Every local head/output term is
renamed through the explicit slot embedding, keeping separate type and row
identities. Exact full-state model equivalence holds even for inconsistent
batches. This adapter does not choose a dictionary or construct the target state.
-/
namespace Yulang.GeneralDictionaryNominalBatchTransport
open GeneralDictionaryNominalSlotTransport (Transport)
open GeneralDictionaryStateEquations (Located Recorded liftType)
open GeneralDictionaryBatchRecording (Item)
open GeneralDictionaryNominalEquations (Holds)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom)
open Core.PresenceGeneration (TyTerm)
variable {before after : GeneralNominalState.State}

/-- Reindex slots and terms, retaining each demand and every repeated output. -/
def located (transport : Transport before after) (old : Located before.base demand) :
    Located after.base demand where
  lower := fun index => transport.embed (old.lower index)
  upper := fun index => transport.embed (old.upper index)
  head := fun index => (old.head index).rename transport.embed
  target := fun index => transport.embed (old.target index)
  output := fun index => (old.output index).rename transport.embed
  arguments := fun index => by simpa only [transport.source] using old.arguments index
  targets := fun index => by simpa only [transport.source] using old.targets index

theorem liftType_eval (transport : Transport before after)
    (term : TyTerm (Fin before.base.slots)) (model : Assignment) :
    (liftType after.base (term.rename transport.embed)).eval CommonNominalFullCarrier.model model =
      (liftType before.base term).eval CommonNominalFullCarrier.model model := by
  rw [GeneralDictionaryNominalEquations.liftType_eval, GeneralDictionaryNominalSlotTransport.term_eval,
    GeneralDictionaryNominalEquations.liftType_eval]

/-- No model premise is needed to preserve the equations of an individual item. -/
theorem located_holds (transport : Transport before after) (old : Located before.base demand)
    (model : Assignment) : Holds (located transport old).equations model ↔ Holds old.equations model := by
  simp only [Holds, Located.equations, located, liftType_eval]

private theorem atom_member (transport : Transport before after) (atom : Atom (Fin before.base.slots))
    (member : atom ∈ before.base.ordinary) : atom.rename transport.embed ∈ after.base.ordinary := by
  rw [transport.atoms]
  exact List.mem_map.mpr ⟨atom, member, rfl⟩

theorem located_recorded (transport : Transport before after) (old : Located before.base demand)
    (recorded : Recorded old) : Recorded (located transport old) where
  lower := fun index => atom_member transport _ (recorded.lower index)
  upper := fun index => atom_member transport _ (recorded.upper index)
  outputForward := fun index => atom_member transport _ (recorded.outputForward index)
  outputBackward := fun index => atom_member transport _ (recorded.outputBackward index)

def item (transport : Transport before after) (old : Item roles before.base) : Item roles after.base :=
  ⟨old.demand, located transport old.located⟩

/-- Whole finite batches retain ordering and multiplicity. -/
def items (transport : Transport before after) (old : List (Item roles before.base)) :
    List (Item roles after.base) := old.map (item transport)

/-- Recording and certified reindexing commute in full nominal model sets.
Both sides use the very same global assignment, not existential replacements. -/
theorem record_models (transport : Transport before after) (old : List (Item roles before.base))
    (model : Assignment) :
    GeneralNominalState.Models (GeneralDictionaryNominalRecording.record after (items transport old)) model ↔
      GeneralNominalState.Models (GeneralDictionaryNominalRecording.record before old) model := by
  rw [GeneralDictionaryNominalRecording.record_models, GeneralDictionaryNominalRecording.record_models,
    GeneralDictionaryNominalSlotTransport.models transport]
  apply and_congr Iff.rfl
  simp only [items, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, item, located_holds]

theorem record_satisfiable (transport : Transport before after) (old : List (Item roles before.base)) :
    (∃ model, GeneralNominalState.Models (GeneralDictionaryNominalRecording.record after (items transport old)) model) ↔
      ∃ model, GeneralNominalState.Models (GeneralDictionaryNominalRecording.record before old) model := by
  simp only [record_models]

/-- Demand identity and repeated target lists are never reconstructed from slot positions. -/
theorem demands_preserved (transport : Transport before after) (old : List (Item roles before.base)) :
    (items transport old).map Item.demand = old.map Item.demand := by
  simp only [items, List.map_map, item, Function.comp_def]

end Yulang.GeneralDictionaryNominalBatchTransport
