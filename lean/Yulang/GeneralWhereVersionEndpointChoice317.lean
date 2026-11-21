import Yulang.GeneralWhereVersionReuse317
import Yulang.GeneralWhereVersionCurrentCert317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralWhereVersionEndpointChoice317
open GeneralNominalState (State sources)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralWhereVersionCase317 (lower upper expr)
open GeneralWhereVersionRootReport317 (plan)
open GeneralWhereVersionSnapshot317 (snap)
open GeneralLiveCompoundPost316 (raw)
open GeneralWhereVersionBase317 (loSlot hiSlot lower_fresh upper_fresh)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralVersionedEndpointAddress315 (atCell)

/-- Distinguish a reusable raw slot from a truly absent source and from
a reserved or mentioned source without a usable slot. The existence of
an existing slot never, by itself, certifies its current equation. -/
inductive Place (s : State) where
  | slot : Fin s.base.slots → Place s
  | fresh : Place s
  | occupied : Place s

def lookup (s : State) (key : Nat) : Place s :=
  match sourceSlot s.base key with
  | some slot => .slot slot
  | none => if key ∈ sources s then .occupied else .fresh

theorem slot_iff {s : State} {key : Nat} {i : Fin s.base.slots} :
    lookup s key = .slot i ↔ s.base.source i = key := by
  rw [← sourceSlot_exact s.base key i]
  constructor
  · intro found
    unfold lookup at found
    split at found
    · cases found; assumption
    · split at found <;> cases found
  · intro found
    simp [lookup,found]

theorem fresh_iff {s : State} {key : Nat} : lookup s key = .fresh ↔ key ∉ sources s := by
  constructor
  · intro fresh
    unfold lookup at fresh
    split at fresh
    · cases fresh
    · split at fresh
      · cases fresh
      · assumption
  · intro absent
    have none : sourceSlot s.base key = none := by
      cases found : sourceSlot s.base key with
      | none => rfl
      | some i =>
        exact False.elim (absent ((sourceSlot_exact s.base key i).mp found ▸
          GeneralNominalAllocationSupport.slot_source s i))
    simp [lookup,none,absent]

theorem occupied_iff {s : State} {key : Nat} :
    lookup s key = .occupied ↔ sourceSlot s.base key = none ∧ key ∈ sources s := by
  constructor
  · intro used
    unfold lookup at used
    split at used
    · cases used
    · split at used
      · exact ⟨by assumption,by assumption⟩
      · cases used
  · rintro ⟨none,used⟩
    simp [lookup,none,used]

theorem first_install : lookup raw lower = .fresh ∧ lookup raw upper = .fresh :=
  ⟨fresh_iff.mpr lower_fresh,fresh_iff.mpr upper_fresh⟩

theorem reuses :
    lookup snap (atCell plan .lower otherChild.id 0 expr) = .slot loSlot ∧
    lookup snap (atCell plan .upper otherChild.id 0 expr) = .slot hiSlot := by
  exact ⟨slot_iff.mpr ((sourceSlot_exact ..).mp GeneralWhereVersionReuse317.exact_slots.1),
    slot_iff.mpr ((sourceSlot_exact ..).mp GeneralWhereVersionReuse317.exact_slots.2)⟩

end Yulang.GeneralWhereVersionEndpointChoice317
