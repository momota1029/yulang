import Yulang.GeneralRebaseActualReplay281

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseOverlap281
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralRebasePortCopy280 (Write Apart Copy Isolated Unambiguous copy_agrees)
open GeneralRebasePortProjection280 (Supported Extension Project Respects copy_satisfies)

def kept (support : List Nat) (writes : List Write) : List Write :=
  writes.filter (fun w => decide (w.1 ∈ support))

def fresh (support : List Nat) (writes : List Write) : List Write :=
  writes.filter (fun w => decide (w.1 ∉ support))

theorem in_kept : row ∈ kept support writes ↔ row ∈ writes ∧ row.1 ∈ support := by
  simp only [kept,List.mem_filter,decide_eq_true_eq]

theorem in_fresh : row ∈ fresh support writes ↔ row ∈ writes ∧ row.1 ∉ support := by
  simp only [fresh,List.mem_filter,decide_eq_true_eq]

theorem kept_supported {writes : List Write} (reads : ∀ row ∈ writes, row.2 ∈ support) :
    Supported support (Respects (kept support writes)) := by
  intro a b agrees
  constructor <;> intro prior row listed
  · obtain ⟨member,within⟩ := in_kept.mp listed
    rw [← agrees row.1 within,← agrees row.2 (reads row member)]
    exact prior row listed
  · obtain ⟨member,within⟩ := in_kept.mp listed
    rw [agrees row.1 within,agrees row.2 (reads row member)]
    exact prior row listed

theorem fresh_apart (support : List Nat) (writes : List Write) :
    Apart (fresh support writes) support :=
  fun _ listed => (in_fresh.mp listed).2

theorem fresh_unique (original : Unambiguous writes) : Unambiguous (fresh support writes) :=
  fun a ha b hb h => original a (in_fresh.mp ha).1 b (in_fresh.mp hb).1 h

theorem fresh_isolated {writes : List Write} (reads : ∀ row ∈ writes, row.2 ∈ support) :
    Isolated (fresh support writes) := by
  intro row listed overlaps
  obtain ⟨other,member,same⟩ := List.mem_map.mp overlaps
  exact fresh_apart support writes row listed (same ▸ reads other (in_fresh.mp member).1)

theorem respects_partition (writes : List Write) (support : List Nat) (a : Assignment) :
    Respects writes a ↔ Respects (kept support writes) a ∧ Respects (fresh support writes) a := by
  constructor
  · intro law
    exact ⟨fun row listed => law row (in_kept.mp listed).1,
      fun row listed => law row (in_fresh.mp listed).1⟩
  · rintro ⟨hold,new⟩ row listed
    by_cases within : row.1 ∈ support
    · exact hold row (in_kept.mpr ⟨listed,within⟩)
    · exact new row (in_fresh.mpr ⟨listed,within⟩)

theorem project_overlap (supported : Supported support base) (unique : Unambiguous writes)
    (reads : ∀ row ∈ writes, row.2 ∈ support) (m : Assignment) :
    Project support (Extension base writes) m ↔ Project support (Extension base (kept support writes)) m := by
  constructor
  · rintro ⟨model,agrees,valid,written⟩
    exact ⟨model,agrees,valid,((respects_partition writes support model).mp written).1⟩
  · rintro ⟨model,agrees,valid,held⟩
    have agree := copy_agrees (fresh_apart support writes) model
    refine ⟨Copy (fresh support writes) model, fun id listed => (agree id listed).symm.trans (agrees id listed),
      (supported _ _ agree).mp valid, ?_⟩
    exact (respects_partition writes support _).mpr ⟨(kept_supported reads _ _ agree).mp held,
      copy_satisfies (fresh_unique unique) (fresh_isolated reads) _⟩

theorem project_supported (supported : Supported support base) (m : Assignment) :
    Project support base m ↔ base m := by
  constructor
  · rintro ⟨a,agrees,valid⟩
    exact (supported _ _ agrees).mp valid
  · intro valid
    exact ⟨m,fun _ _ => rfl,valid⟩

end Yulang.GeneralRebaseOverlap281
