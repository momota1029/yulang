import Yulang.GeneralObservedLadderReadback301

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderJournalRows301
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralObservedLadderOnlyInstall301 (generated)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (State)

theorem site_count (n k : Nat) : (sites n k).length = k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sites,ih]

theorem indexed_site (n i k : Nat) : (sites n k)[i]? = if i ≤ k then some (site n i) else none := by
  induction k with
  | zero =>
    cases i with
    | zero => rfl
    | succ i => simp [sites]
  | succ k ih =>
    rw [sites]
    by_cases before : i ≤ k
    · rw [List.getElem?_append_left (by rw [site_count]; omega),ih,
        ite_eq_left before,ite_eq_left (by omega)]
    · rw [List.getElem?_append_right (by rw [site_count]; omega),site_count]
      by_cases exactly : i = k+1
      · subst i
        rw [Nat.sub_self,ite_eq_left (Nat.le_refl _)]
        rfl
      · have tooFar : 0 < i-(k+1) := by omega
        rw [ite_eq_right (by omega)]
        exact List.getElem?_eq_none (by simp only [List.length_singleton]; omega)

abbrev Rows := List (GeneralNominalDemandMerging.Site roles)

def rawRow (s : State roles) (i : Nat) := s.core.erased.current.sites[i]?

theorem raw_hit (p : Phase n k) (i : Nat) :
    rawRow p.state i = if i ≤ k then some (site n i).observed else none := by
  unfold rawRow
  rw [p.raw_eq,List.getElem?_map,indexed_site]
  by_cases hi : i ≤ k <;> simp [hi]

def attached (s : State roles) (i j : Nat) : Bool :=
  match rawRow s i, rawRow s j with
  | some first,some last =>
    s.core.erased.current.edges.any
      (fun e => (e.1.identity == first.occurrence.identity) &&
        (e.2.identity == last.occurrence.identity))
  | _,_ => false

theorem attached_exact (p : Phase n k) (i j : Nat) :
    attached p.state i j = true ↔ i < k ∧ j = i+1 := by
  unfold attached
  rw [raw_hit p i,raw_hit p j]
  by_cases hi : i ≤ k
  · rw [ite_eq_left hi]
    by_cases hj : j ≤ k
    · rw [ite_eq_left hj]
      change p.state.core.erased.current.edges.any (fun e =>
        (e.1.identity == invocation n i) && (e.2.identity == invocation n j)) = true ↔ _
      rw [List.any_eq_true]
      constructor
      · rintro ⟨edge,listed,tests⟩
        rw [p.edges_eq] at listed
        obtain ⟨u,early,rfl⟩ := (edge_exact ..).mp listed
        have pairs := (Bool.and_eq_true _ _).mp tests
        have left : u = i := injective n (beq_iff_eq.mp pairs.1)
        have right : u+1 = j := injective n (beq_iff_eq.mp pairs.2)
        omega
      · rintro ⟨early,rfl⟩
        refine ⟨(focus n i,focus n (i+1)),?_,by simp⟩
        rw [p.edges_eq]
        exact (edge_exact ..).mpr ⟨i,early,rfl⟩
    · rw [ite_eq_right hj]
      constructor
      · intro no; cases no
      · omega
  · rw [ite_eq_right hi]
    cases j <;> simp_all <;> omega

theorem all_generated (p : Phase n k) (i : Nat) (bound : i ≤ k) :
    GeneralNominalSaturationState.Generated p.state.core.erased.current GeneralNominalExamples.displayRoot (focus n i) := by
  induction i with
  | zero => exact .root
  | succ i ih =>
    apply GeneralNominalSaturationState.Generated.child (ih (by omega))
    rw [p.edges_eq]
    exact (edge_exact ..).mpr ⟨i,by omega,rfl⟩

end Yulang.GeneralObservedLadderJournalRows301
