import Yulang.GeneralDictionaryNominalEquations
import Yulang.GeneralNominalState

/-!
# Dictionary batches in the full nominal source state

Only the finite dictionary's global ordinary equations are appended. Existing
base slots, normalized view, nominal descriptors and source ownership are
retained. This is a dictionary transaction, not a Step rule or a source allocator.
-/
namespace Yulang.GeneralDictionaryNominalRecording
open PresenceNormalForm (Atom All)
open GeneralDictionaryBatchRecording (Item batchAtoms)
open GeneralDictionaryStateEquations (liftType liftRow)
open GeneralNominalCommonBridge (Assignment)

/-- Local type and row slots use their separate actual source maps. -/
def liftAtom (state : GeneralSourceState.State) : Atom (Fin state.slots) → Atom Nat
  | .tyLe first last => .tyLe (liftType state first) (liftType state last)
  | .rowLe first last => .rowLe (liftRow state first) (liftRow state last)

theorem liftAtom_exact (state : GeneralSourceState.State) (atom : Atom (Fin state.slots))
    (model : Assignment) :
    (liftAtom state atom).Holds CommonNominalFullCarrier.model model ↔
      atom.Holds CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state model) := by
  cases atom <;> simp only [liftAtom, Atom.Holds, GeneralDictionaryNominalEquations.liftType_eval,
    GeneralDictionaryNominalEquations.liftRow_eval]

theorem liftAtoms_exact (state : GeneralSourceState.State) (atoms : List (Atom (Fin state.slots)))
    (model : Assignment) :
    All CommonNominalFullCarrier.model model (atoms.map (liftAtom state)) ↔
      All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state model) atoms := by
  simp only [All, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, liftAtom_exact]

/-- Record the already prepared finite tree without changing the nominal graph. -/
def record (state : GeneralNominalState.State) (items : List (Item roles state.base)) :
    GeneralNominalState.State :=
  GeneralNominalState.extend state [] ((batchAtoms items).map (liftAtom state.base))

/-- All old nominal descriptor/head/interval obligations and every new dictionary
package share the same assignment. No existence of such an assignment is claimed. -/
theorem record_models (state : GeneralNominalState.State) (items : List (Item roles state.base))
    (model : Assignment) :
    GeneralNominalState.Models (record state items) model ↔
      GeneralNominalState.Models state model ∧
        ∀ item ∈ items, GeneralDictionaryNominalEquations.Holds item.located.equations model := by
  rw [record, GeneralNominalState.extend_models, liftAtoms_exact]
  apply and_congr Iff.rfl
  induction items with
  | nil => simp [batchAtoms]
  | cons item rest ih =>
    simp only [batchAtoms, List.flatMap_cons, PresenceNormalForm.all_append,
      GeneralDictionaryNominalEquations.atoms_exact, List.mem_cons, forall_eq_or_imp]
    exact and_congr Iff.rfl ih

/-- The same assignment is a model of the base-slot dictionary batch used by
source-evidence soundness. Full-state constraints are not discarded in record. -/
theorem recorded_base_model (state : GeneralNominalState.State) (items : List (Item roles state.base))
    (model : Assignment) (valid : GeneralNominalState.Models (record state items) model) :
    GeneralNominalCommonBridge.Models (GeneralDictionaryBatchRecording.record items) model := by
  obtain ⟨old, packages⟩ := (record_models state items model).mp valid
  exact (GeneralDictionaryNominalEquations.batch_models items model).mpr ⟨old.1, packages⟩

/-- Full-state model retention is a consequence, not a caller-supplied premise. -/
theorem record_preserves (state : GeneralNominalState.State) (items : List (Item roles state.base))
    (model : Assignment) (valid : GeneralNominalState.Models (record state items) model) :
    GeneralNominalState.Models state model := ((record_models state items model).mp valid).1

/-- Dict recording alone cannot turn an unresolved lower head into a known one. -/
theorem record_pending (state : GeneralNominalState.State) (items : List (Item roles state.base))
    (demand : GeneralSourceState.Demand roles) :
    GeneralNominalState.RootPending (record state items) demand ↔
      GeneralNominalState.RootPending state demand := Iff.rfl

/-- Reordering listed packages preserves the full nominal model set, including
old descriptor constraints; repeated packages are not silently removed. -/
theorem record_order_models (state : GeneralNominalState.State)
    (first last : List (Item roles state.base)) (order : first.Perm last) (model : Assignment) :
    GeneralNominalState.Models (record state first) model ↔
      GeneralNominalState.Models (record state last) model := by
  rw [record_models, record_models]
  exact and_congr Iff.rfl (by simp only [order.mem_iff])

end Yulang.GeneralDictionaryNominalRecording
