import Yulang.GeneralNominalRebaseEscapedProjection242
import Yulang.GeneralDictionaryOptionalOutput229
set_option backward.isDefEq.respectTransparency false
/-! Local regression against unrestricted union-domain replacement. An old
consumer of an undefined cell is not erased. This does not refute design A. -/
namespace Yulang.GeneralDictionaryRebaseNewCellObstruction242
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open CommonNominalFullCarrier

def oldEntries : List Entry := []
def newEntries : List Entry := [(2,.var 1)]
def witnessEntries : List Entry := [(2,.var 0)]
def oldConsumer : List (PresenceNormalForm.Atom Nat) := GeneralNominalAllocation.equations 2 (.var 0)

def model : Assignment := fun name =>
 (if name = 0 then GeneralDictionaryOptionalOutput229.value else .emptyRecord,Common.rowEmpty)

theorem singleton_coherent (name source : Nat) : Coherent [(name,.var source)] := by
 intro first member last included _
 cases List.mem_singleton.mp member
 cases List.mem_singleton.mp included
 rfl

theorem new_external : External newEntries := by
 intro entry member name present target included
 cases List.mem_singleton.mp member
 cases List.mem_singleton.mp included
 have one : name = 1 := List.mem_singleton.mp present
 subst name
 decide

theorem witness_external : External witnessEntries := by
 intro entry member name present target included
 cases List.mem_singleton.mp member
 cases List.mem_singleton.mp included
 have zero : name = 0 := List.mem_singleton.mp present
 subst name
 decide

theorem source_distinct : ¬ Equivalent (model 0).1 (model 1).1 :=
 GeneralDictionaryOptionalOutput229.not_width

theorem old_exists : ∃ old, Preserves newEntries old model ∧ Definitions oldEntries old ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model old oldConsumer := by
 let old := patch witnessEntries model
 have kept := patch_preserves witnessEntries model
 have equal := patch_definitions witnessEntries (singleton_coherent 2 0) witness_external model
 refine ⟨old,?_,?_,equal (2,.var 0) (by simp [witnessEntries])⟩
 · refine ⟨?_,kept.2⟩
   intro name absent
   apply kept.1 name
   intro entry member
   cases List.mem_singleton.mp member
   exact absent (2,.var 1) (by simp [newEntries])
 · intro entry member
   cases member

theorem conflicting_preserved_sources (next source : Assignment)
 (kept : Preserves newEntries next source)
 (definitions : Definitions newEntries next)
 (consumer : PresenceNormalForm.All CommonNominalFullCarrier.model next oldConsumer) :
 Equivalent (source 0).1 (source 1).1 := by
 have oldValue := (GeneralNominalCaptureMerges.equations_exact next 2 (.var 0)).mp consumer
 have newValue := (GeneralNominalCaptureMerges.equations_exact next 2 (.var 1)).mp
   (definitions (2,.var 1) (by simp [newEntries]))
 have atZero := kept.1 0 (by intro entry member; cases List.mem_singleton.mp member; decide)
 have atOne := kept.1 1 (by intro entry member; cases List.mem_singleton.mp member; decide)
 change Equivalent (next 2).1 (next 0).1 at oldValue
 change Equivalent (next 2).1 (next 1).1 at newValue
 rw [atZero] at oldValue
 rw [atOne] at newValue
 exact ⟨subtype_trans oldValue.2 newValue.1,subtype_trans newValue.2 oldValue.1⟩

theorem no_new : ¬ ∃ next, Preserves newEntries next model ∧ Definitions newEntries next ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model next oldConsumer := by
 rintro ⟨next,kept,definitions,consumer⟩
 exact source_distinct (conflicting_preserved_sources next model kept definitions consumer)

theorem projections_differ : ¬
 ((∃ old, Preserves newEntries old model ∧ Definitions oldEntries old ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model old oldConsumer) ↔
  (∃ next, Preserves newEntries next model ∧ Definitions newEntries next ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model next oldConsumer)) :=
 fun claimed => no_new (claimed.mp old_exists)

theorem without_consumer_exists : ∃ next, Preserves newEntries next model ∧ Definitions newEntries next :=
 ⟨patch newEntries model,patch_preserves newEntries model,
   patch_definitions newEntries (singleton_coherent 2 1) new_external model⟩
end Yulang.GeneralDictionaryRebaseNewCellObstruction242
