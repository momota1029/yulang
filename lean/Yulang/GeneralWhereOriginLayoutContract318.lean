import Yulang.GeneralWhereOriginCurrent318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralWhereOriginLayoutContract318
open GeneralNominalCenters (Plan)
open GeneralWhereVersionInstall317 (Journal)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginLayout318 (matchSlots check_spec freshCells mem_fresh)
open GeneralWhereOriginPartition318 (fresh existing_iff fresh_iff classified_iff allClassified)
open GeneralNominalAllocationSupport (slot_source)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)

theorem writer_exact {j : Journal rs} {p : Plan rs} {guard : List Nat}
    (pass : allClassified j p guard = true) (c : Cell p) :
    c ∈ fresh j p guard ↔ c ∈ freshCells (rawOf j) p := by
  constructor
  · intro written
    exact (mem_fresh c).mpr ((fresh_iff j c guard).mp written).1
  · intro rawFresh
    have absent := (mem_fresh c).mp rawFresh
    rcases List.mem_append.mp ((classified_iff j p guard).mp pass c) with reuse|write
    · obtain ⟨i,slot⟩ := (existing_iff j c).mp reuse
      exact False.elim (absent ((sourceSlot_exact ..).mp slot ▸ slot_source (rawOf j) i))
    · exact write

/-- Every new physical raw slot accepted by the allocator comes from the
actual writer partition. Conversely every writer cell gets a new physical
slot, and a previously found slot is never selected as a writer cell.
This states address integrity, not the model truth of the new observations. -/
theorem exact_insertion {j : Journal rs} {p : Plan rs} {after : GeneralNominalState.State} {guard : List Nat}
    (pass : allClassified j p guard = true) (layout : matchSlots (rawOf j) after p = true) :
    (∀ i : Fin after.base.slots, sourceSlot (rawOf j).base (after.base.source i) = none →
      ∃ c ∈ fresh j p guard, after.base.source i = c.row.target) ∧
    (∀ c ∈ fresh j p guard, sourceSlot (rawOf j).base c.row.target = none ∧
      ∃ i, sourceSlot after.base c.row.target = some i) := by
  have checked := (check_spec p).mp layout
  constructor
  · intro i missing
    rcases checked.2 i with ⟨old,eq⟩|⟨cell,member,id⟩
    · have located := (sourceSlot_exact (rawOf j).base (after.base.source i) old).mpr eq.symm
      rw [missing] at located
      cases located
    · exact ⟨cell,(writer_exact pass cell).mpr member,id⟩
  · intro c member
    have absent := ((fresh_iff j c guard).mp member).1
    have missing : sourceSlot (rawOf j).base c.row.target = none := by
      cases found : sourceSlot (rawOf j).base c.row.target with
      | none => rfl
      | some i =>
        exact False.elim (absent ((sourceSlot_exact ..).mp found ▸ slot_source (rawOf j) i))
    obtain ⟨i,found⟩ := checked.1 c ((writer_exact pass c).mp member)
    exact ⟨missing,i,(sourceSlot_exact ..).mpr found⟩

end Yulang.GeneralWhereOriginLayoutContract318
