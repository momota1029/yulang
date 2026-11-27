import Yulang.GeneralDeclarativeWitnessBound349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparationBoundReplay467
open GeneralDeclarativeWitnessBound349 (Path Checked replay check sound)
open GeneralDeclarativeBounds319 (Bound)
private abbrev Raw := GeneralDeclarativeHead320.State

private theorem check_at_read {s : Raw} {p : Path} {x : Checked s} (h : replay s p = some x) :
    check s x.lower x.upper p = true := by simp [check,h]

theorem every_actual_bound_has_finite_literal_source_wire {s : Raw} {a b : Nat}
    (raw : Bound s.normal a b) :
    ∃ w : Path, ∃ x : Checked s, replay s w = some x ∧ x.lower = a ∧ x.upper = b := by
  induction raw with
  | @interval a b member =>
    obtain ⟨i,h⟩ := List.mem_iff_getElem?.mp member
    refine ⟨.interval i,⟨a,b,.interval member⟩,?_,rfl,rfl⟩
    unfold replay
    split
    · rename_i not
      rw [h] at not
      cases not
    · rename_i p q here
      have same := Option.some.inj (h.symm.trans here)
      cases same
      rfl
  | @constraint a b member =>
    obtain ⟨i,h⟩ := List.mem_iff_getElem?.mp member
    refine ⟨.constraint i,⟨a,b,.constraint member⟩,?_,rfl,rfl⟩
    unfold replay
    split
    · rename_i p q here
      have same := Option.some.inj (h.symm.trans here)
      cases same
      rfl
    · rename_i no
      exact (no a b h).elim
  | refl a => exact ⟨.refl a,⟨a,a,.refl _⟩,rfl,rfl,rfl⟩
  | trans _ _ left right =>
    obtain ⟨lw,l,first,lo,mid⟩ := left
    obtain ⟨rw,r,second,meet,hi⟩ := right
    have connection := mid.trans meet.symm
    refine ⟨.compose lw rw,⟨l.lower,r.upper,.trans l.fact (connection.symm ▸ r.fact)⟩,?_,lo,hi⟩
    simp [replay,first,second,Option.bind,connection]

theorem finite_literal_bound_wire_is_equivalent_to_independent_bound (s : Raw) (a b : Nat) :
    (∃ w : Path, check s a b w = true) ↔ Bound s.normal a b := by
  constructor
  · rintro ⟨_,h⟩
    exact sound h
  · intro raw
    obtain ⟨w,x,passed,lo,hi⟩ := every_actual_bound_has_finite_literal_source_wire raw
    exact ⟨w,lo ▸ hi ▸ check_at_read passed⟩

end Yulang.GeneralDeclarativeI65.I72.PreparationBoundReplay467
