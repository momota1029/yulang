import Yulang.GeneralMixedCompoundBatch307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
namespace Yulang.GeneralMixedCompoundEarlyBase308
open GeneralDictionaryJournalRefinement228Source (roles root snapshot constructors interpretation)
open GeneralDictionaryJournalRefinement228Reobserve (loose exactCopy)
open GeneralDictionaryCompoundFrame238 (installed)
open GeneralMixedCompoundUpperSnapshot307 (snap context desc)
open GeneralMixedCompoundUpperBase307 (base view)
open GeneralMixedCompoundBatchBase307 (embed source_eq atom_membership)
open GeneralNominalRefinements (Refines renameDescriptor)
open GeneralNominalState (Known)
open GeneralNominalRecursiveCandidates (Context)

abbrev wideLoose : GeneralNominalState.Descriptor 8 := renameDescriptor embed loose

noncomputable abbrev looseSnap : GeneralNominalState.State where
  base := base
  view := view
  constructors := snap.constructors
  nominals := fun slot => if slot = 0 then some wideLoose else if slot = 1 then some desc else none
  catalogue := by
    intro slot d found
    by_cases zero : slot = 0 <;> by_cases one : slot = 1
    all_goals simp only [zero,one,ite_true,ite_false] at found
    all_goals first | cases Option.some.inj found; rfl | cases found
  bodies_opaque := by
    intro slot d found
    by_cases zero : slot = 0
    · subst slot; rfl
    · by_cases one : slot = 1
      · subst slot; rfl
      · simp [zero,one] at found
  allocated := snap.allocated
  reserved := snap.reserved
  ordinary := snap.ordinary
  seed := snap.seed

noncomputable abbrev looseContext : Context := ⟨looseSnap,interpretation⟩

theorem same_domain (slot : Fin 8) :
    looseSnap.nominals slot = none ↔ snap.nominals slot = none := by
  by_cases z : slot = 0 <;> by_cases o : slot = 1 <;> simp [looseSnap,snap,z,o]

theorem known_iff (id : Nat) : Known looseSnap id ↔ Known snap id := by
  constructor
  · rintro ⟨slot,eq,h|⟨d,found⟩⟩
    · exact ⟨slot,eq,Or.inl h⟩
    · cases seen : snap.nominals slot with
      | none => rw [(same_domain slot).mpr seen] at found; cases found
      | some current => exact ⟨slot,eq,Or.inr ⟨current,seen⟩⟩
  · rintro ⟨slot,eq,h|⟨d,found⟩⟩
    · exact ⟨slot,eq,Or.inl h⟩
    · cases seen : looseSnap.nominals slot with
      | none => rw [(same_domain slot).mp seen] at found; cases found
      | some current => exact ⟨slot,eq,Or.inr ⟨current,seen⟩⟩

theorem old_known (id : Nat) (recorded : Known installed.core.erased.current.context.state id) :
    Known looseSnap id := by
  have p := (GeneralNominalReobservationSteps.revision_known GeneralDictionaryCompoundPoint238.revision id).mpr recorded
  exact (known_iff id).mpr (GeneralMixedCompoundBatchBase307.known_point p)

noncomputable def refines : Refines installed.core.erased.current.context.state looseSnap where
  base := GeneralMixedCompoundBatchBase307.refineBatch.base
  heads := GeneralMixedCompoundBatchBase307.refineBatch.heads
  nominals := by
    intro slot d found
    change Fin 5 at slot
    change (if slot = 0 then some loose else if slot = 1 then some exactCopy else none) = some d at found
    split at found
    · rename_i z
      subst slot; cases Option.some.inj found; rfl
    · split at found
      · rename_i _ o
        subst slot; cases Option.some.inj found; rfl
      · cases found
  ordinary := fun _ h => h
  known := old_known
  reserved := fun _ h => h
  allocated := fun _ h => h
  seed := rfl
  constructors := rfl

end Yulang.GeneralMixedCompoundEarlyBase308
