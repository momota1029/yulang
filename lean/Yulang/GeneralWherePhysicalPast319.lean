import Yulang.GeneralWherePhysicalDeferred319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 21000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralWherePhysicalPast319
open GeneralDictionaryJournalRefinement228Source (snapshot base interpretation context)
open GeneralDictionaryJournalRefinement228Reobserve (pointSnapshot point_models_iff)
open GeneralWhereOriginSingleCells318 (loOld hi)
open GeneralWhereOriginSingleModel318 (previousLo previousHi older_absent old_lo_ne_hi)
open GeneralWherePhysicalIndex319 (old new)
open GeneralWherePhysicalBase319 (Layout expand source_old source_new)
open GeneralWherePhysicalDeferred319 (laid deferred noAdded)
open GeneralWherePhysicalNominal319 (refinement)
open GeneralNominalState (Models sources)
open GeneralNominalCommonBridge (Assignment assignment)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralSourceState (equationAtoms)
open PresenceNormalForm (All all_append)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier

abbrev firstLo : Fin 7 := new 5 (0 : Fin 2)
abbrev savedHi : Fin 7 := new 5 (1 : Fin 2)
abbrev two : Fin 7 := old 2 (2 : Fin 5)
abbrev four : Fin 7 := old 2 (4 : Fin 5)

theorem apart (i : Fin 5) (j : Fin 2) :
    base.source i ≠ (if j = 0 then loOld else hi) := by
  have seen := GeneralNominalAllocationSupport.slot_source snapshot i
  by_cases first : j = 0
  · simp only [first,ite_true]
    exact fun eq => older_absent loOld (previousLo.high rfl) (eq ▸ seen)
  · simp only [first,ite_false]
    exact fun eq => older_absent hi (previousHi.high rfl) (eq ▸ seen)

def layout : Layout base 2 where
  ids := fun j => if j = 0 then loOld else hi
  distinct := by
    intro a b same
    have cases' (i : Fin 2) : i = 0 ∨ i = 1 := by omega
    rcases cases' a with rfl|rfl <;> rcases cases' b with rfl|rfl
    · rfl
    · exact False.elim (old_lo_ne_hi same)
    · exact False.elim (old_lo_ne_hi same.symm)
    · rfl
  no_overlap := apart
  shape_indices := fun _ _ _ => Subsingleton.elim _ _

abbrev extra :=
  equationAtoms firstLo (.variant 0 (.var four)) ++ equationAtoms savedHi (.variant 0 (.var two))

abbrev loose := laid snapshot layout extra
abbrev point := laid pointSnapshot layout extra
abbrev looseCtx : GeneralNominalCandidates.Context := ⟨loose,interpretation⟩
abbrev pointCtx : GeneralNominalCandidates.Context := ⟨point,interpretation⟩

theorem low_id : loose.base.source firstLo = loOld := by
  change GeneralWherePhysicalBase319.source layout firstLo = _
  rw [source_new]
  rfl

theorem high_id : loose.base.source savedHi = hi := by
  change GeneralWherePhysicalBase319.source layout savedHi = _
  rw [source_new]; rfl

theorem loose_slots :
    sourceSlot loose.base loOld = some firstLo ∧ sourceSlot loose.base hi = some savedHi :=
  ⟨(sourceSlot_exact ..).mpr low_id,(sourceSlot_exact ..).mpr high_id⟩

theorem same_base : point.base = loose.base := rfl

theorem point_slots :
    sourceSlot point.base loOld = some firstLo ∧ sourceSlot point.base hi = some savedHi := loose_slots

theorem equation_extra {s : GeneralSourceState.State} {m : Assignment} (i : Fin s.slots) (term) :
    All CommonNominalFullCarrier.model (assignment s m) (equationAtoms i term) ↔
      Equivalent (m (s.source i)).1 (term.eval CommonNominalFullCarrier.model (assignment s m)) := by
  constructor
  · intro h
    exact ⟨h _ List.mem_cons_self,h _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩
  · intro h a found
    simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl
    · exact h.1
    · exact h.2

theorem extra_exact (m : Assignment) :
    All CommonNominalFullCarrier.model (assignment loose.base m) extra ↔
      Equivalent (m loOld).1 (variant 0 (m 4).1) ∧ Equivalent (m hi).1 (variant 0 (m 2).1) := by
  rw [all_append,equation_extra,equation_extra,low_id,high_id]
  rfl

theorem loose_models (m : Assignment) : Models loose m ↔ Models snapshot m ∧
    Equivalent (m loOld).1 (variant 0 (m 4).1) ∧ Equivalent (m hi).1 (variant 0 (m 2).1) := by
  change Models (laid snapshot layout extra) m ↔ _
  rw [GeneralWherePhysicalNominal319.models_iff]
  exact and_congr_right fun _ => extra_exact m

theorem point_models (m : Assignment) : Models point m ↔ Models loose m := by
  change Models (laid pointSnapshot layout extra) m ↔ Models (laid snapshot layout extra) m
  rw [GeneralWherePhysicalNominal319.models_iff,GeneralWherePhysicalNominal319.models_iff]
  exact and_congr_left' (point_models_iff m)

/-- The endpoints are genuinely present but not yet observed. This
distinguishes allocation/reuse from readiness of a generated child. -/
theorem high_pending : ¬ GeneralNominalState.Known point hi := by
  rintro ⟨i,asHi,seen⟩
  have eq := point.base.source_injective (asHi.trans high_id.symm)
  subst i
  rcases seen with shape|⟨d,nom⟩
  · exact shape rfl
  · change (none : Option (GeneralNominalState.Descriptor 7)) = some d at nom
    cases nom

end Yulang.GeneralWherePhysicalPast319
