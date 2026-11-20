import Yulang.GeneralGeneratedDictionaryRankExists299

namespace Yulang.GeneralGeneratedDictionaryFiniteCap299
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryAcc299
open GeneralGeneratedDictionaryRankCheck299
open GeneralGeneratedDictionaryRankExists299
open CommonRoleOutermostResolver (Dictionary)

theorem acc_no_loop {α : Type} {R : α → α → Prop} {a : α} (acc : Acc R a) : ¬ R a a := by
  induction acc with
  | intro x pred ih =>
    intro self
    exact ih x self self

theorem no_return (read : Read) (x a : Nat) (acc : Acc (Edge read) x)
    (edge : Edge read a x) (y : Nat)
    (descendant : y = a ∨ Relation.TransGen (Edge read) y a) : y ≠ x := by
  intro equal
  subst y
  apply acc_no_loop acc.transGen
  rcases descendant with same | path
  · subst a
    exact .single edge
  · exact .tail path edge

theorem descends_known (read : Read) (closed : Closed read) (x c : Nat)
    (path : Relation.TransGen (Edge read) c x) :
    (∃ row, read x = some row) → (∃ row, read c = some row) := by
  induction path with
  | single step =>
    intro _
    obtain ⟨row,hit,member⟩ := step
    exact closed _ row hit _ member
  | tail _ last ih =>
    intro _
    obtain ⟨row,hit,member⟩ := last
    exact ih (closed _ row hit _ member)

theorem bounded_from (read : Read) (closed : Closed read) (x : Nat)
    (acc : Acc (Edge read) x) (remaining : List Nat)
    (within : ∀ y, y = x ∨ Relation.TransGen (Edge read) y x → y ∈ remaining)
    (row : Entry) (hit : read x = some row) :
    ∃ d, run read remaining.length x = some d := by
  have present := within x (.inl rfl)
  have positive := List.length_pos_of_mem present
  cases eq : remaining.length with
  | zero => omega
  | succ n =>
    obtain ⟨ds,filled⟩ := collect_exists (run read n) row.children (by
      intro child member
      have edge : Edge read child x := ⟨row,hit,member⟩
      obtain ⟨childRow,childHit⟩ := closed x row hit child member
      have childWithin : ∀ y, y = child ∨ Relation.TransGen (Edge read) y child →
          y ∈ remaining.erase x := by
        intro y reached
        apply (List.mem_erase_of_ne (no_return read x child acc edge y reached)).mpr
        apply within y
        right
        rcases reached with rfl | path
        · exact .single edge
        · exact .tail path edge
      obtain ⟨d,ok⟩ := bounded_from read closed child (acc.inv edge)
        (remaining.erase x) childWithin childRow childHit
      rw [List.length_erase_of_mem present,eq,Nat.succ_sub_one] at ok
      exact ⟨d,ok⟩)
    exact ⟨.node row.key ds,by simp [run,hit,filled]⟩
termination_by remaining.length
decreasing_by
  rw [List.length_erase_of_mem present]
  omega

theorem finite_cap (read : Read) (domain : List Nat) (closed : Closed read)
    (known : Known read domain) (x : Nat) (acc : Acc (Edge read) x)
    (row : Entry) (hit : read x = some row) :
    ∃ d, run read domain.length x = some d := by
  apply bounded_from read closed x acc domain ?_ row hit
  intro y seen
  rcases seen with rfl | path
  · exact known _ row hit
  · obtain ⟨here,found⟩ := descends_known read closed x y path ⟨row,hit⟩
    exact known y here found

theorem check_length (read : Read) (domain : List Nat) (closed : Closed read)
    (known : Known read domain) :
    check read domain domain.length = true ↔
      ∀ x ∈ domain, (∃ row, read x = some row) ∧ Acc (Edge read) x := by
  constructor
  · intro h
    exact (finite_exact read domain closed).mp ⟨_,h⟩
  · intro h
    apply List.all_eq_true.mpr
    intro x member
    obtain ⟨⟨row,hit⟩,acc⟩ := h x member
    obtain ⟨k,when⟩ := found_at_cap read x domain.length (finite_cap read domain closed known x acc row hit)
    simp [hit,when]

end Yulang.GeneralGeneratedDictionaryFiniteCap299
