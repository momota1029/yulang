import Yulang.GeneralWherePhysicalPast319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 23000000
namespace Yulang.GeneralWherePhysicalFresh319
open GeneralWherePhysicalPast319 (point loose layout extra firstLo savedHi two four high_id low_id extra_exact)
open GeneralWhereOriginSingleCells318 (loOld loNow hi lower_moves)
open GeneralWhereOriginSingleModel318 (presentLo older_absent new_lo_ne_hi)
open GeneralDictionaryJournalRefinement228Source (snapshot interpretation)
open GeneralWherePhysicalIndex319 (old new)
open GeneralWherePhysicalBase319 (Layout expand source_old source_new)
open GeneralWherePhysicalDeferred319 (laid deferred noAdded)
open GeneralWherePhysicalNominal319 (refinement)
open GeneralNominalState (State Models sources)
open GeneralNominalCommonBridge (Assignment assignment)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralSourceState (equationAtoms)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier

abbrev oldLo : Fin 8 := old 1 firstLo
abbrev upperSlot : Fin 8 := old 1 savedHi
abbrev lowerSlot : Fin 8 := new 7 (0 : Fin 1)
abbrev oldTwo : Fin 8 := old 1 two
abbrev oldFour : Fin 8 := old 1 four

theorem fresh_sources : loNow ∉ sources point := by
  intro appears
  have sourceOld : loNow ∉ sources snapshot := older_absent _ (presentLo.high rfl)
  simp only [sources,List.mem_append] at appears
  rcases appears with ((someType|someRow)|reserve)|ordinary
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp someType
    refine Fin.addCases (m := 5) (n := 2) (fun j h => ?_) (fun j h => ?_) i eq
    · change GeneralWherePhysicalBase319.source layout (old 2 j) = loNow at h
      rw [source_old] at h
      exact sourceOld (h ▸ GeneralNominalAllocationSupport.slot_source snapshot j)
    · have twoCases : j = 0 ∨ j = 1 := by omega
      rcases twoCases with rfl|rfl
      · exact lower_moves (low_id.symm.trans h)
      · exact new_lo_ne_hi (h.symm.trans high_id)
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp someRow
    have same : point.base.rowSource i = point.base.source i := by
      refine Fin.addCases (m := 5) (n := 2) ?_ ?_ i <;> intro j
      · change GeneralWherePhysicalBase319.rowSource layout (old 2 j) =
          GeneralWherePhysicalBase319.source layout (old 2 j)
        rw [GeneralWherePhysicalBase319.row_old,source_old]
      · change Fin.addCases snapshot.base.rowSource layout.ids (new 5 j) =
          GeneralWherePhysicalBase319.source layout (new 5 j)
        rw [Fin.addCases_right,source_new]
    have fromType := same.symm.trans eq
    refine Fin.addCases (m := 5) (n := 2) (fun j h => ?_) (fun j h => ?_) i fromType
    · change GeneralWherePhysicalBase319.source layout (old 2 j) = loNow at h
      rw [source_old] at h
      exact sourceOld (h ▸ GeneralNominalAllocationSupport.slot_source snapshot j)
    · have twoCases : j = 0 ∨ j = 1 := by omega
      rcases twoCases with rfl|rfl
      · exact lower_moves (low_id.symm.trans h)
      · exact new_lo_ne_hi (h.symm.trans high_id)
  · exact sourceOld (List.mem_append_left _ (List.mem_append_right _ reserve))
  · exact sourceOld (List.mem_append_right _ ordinary)

theorem old_lookup_absent : sourceSlot point.base loNow = none := by
  cases hit : sourceSlot point.base loNow with
  | none => rfl
  | some i =>
    exact False.elim (fresh_sources ((sourceSlot_exact ..).mp hit ▸ GeneralNominalAllocationSupport.slot_source point i))

noncomputable def finalLayout : Layout point.base 1 where
  ids := fun _ => loNow
  distinct := fun _ _ _ => Subsingleton.elim _ _
  no_overlap := fun i _ eq => fresh_sources (eq ▸ GeneralNominalAllocationSupport.slot_source point i)
  shape_indices := by
    intro a b _
    change Fin 1 at a b
    exact Subsingleton.elim a b

abbrev newAtoms := equationAtoms lowerSlot (.variant 0 (.var oldTwo))
noncomputable abbrev raw := laid point finalLayout newAtoms

theorem upper_id : raw.base.source upperSlot = hi := by
  change GeneralWherePhysicalBase319.source finalLayout (old 1 savedHi) = _
  rw [source_old]
  exact high_id

theorem lower_id : raw.base.source lowerSlot = loNow := by
  change GeneralWherePhysicalBase319.source finalLayout (new point.base.slots (0 : Fin 1)) = _
  rw [source_new]
  rfl

theorem final_slots : sourceSlot raw.base hi = some upperSlot ∧ sourceSlot raw.base loNow = some lowerSlot :=
  ⟨(sourceSlot_exact ..).mpr upper_id,(sourceSlot_exact ..).mpr lower_id⟩

theorem archived_lower : raw.base.source oldLo = loOld := by
  change GeneralWherePhysicalBase319.source finalLayout (old 1 firstLo) = _
  rw [source_old]
  exact low_id

theorem oldTwo_id : raw.base.source oldTwo = 2 := by
  change GeneralWherePhysicalBase319.source finalLayout (old 1 two) = _
  rw [source_old]
  change GeneralWherePhysicalBase319.source layout (old 2 (2 : Fin 5)) = _
  rw [source_old]; rfl

theorem raw_models (m : Assignment) :
    Models raw m ↔ Models point m ∧ Equivalent (m loNow).1 (variant 0 (m 2).1) := by
  change Models (laid point finalLayout newAtoms) m ↔ _
  rw [GeneralWherePhysicalNominal319.models_iff]
  apply and_congr_right
  intro _
  rw [GeneralWherePhysicalPast319.equation_extra]
  change Equivalent (m (raw.base.source lowerSlot)).1 (variant 0 (m (raw.base.source oldTwo)).1) ↔ _
  rw [lower_id,oldTwo_id]

end Yulang.GeneralWherePhysicalFresh319
