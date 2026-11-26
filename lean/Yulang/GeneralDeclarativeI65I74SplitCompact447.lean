import Yulang.GeneralDeclarativeI65I74SplitEscapeFinite446
namespace Yulang.GeneralDeclarativeI65.I72.SplitEscape446.SplitCompact447
open GeneralDeclarativeWitnessRank350 (rank)
open List410

def below (xs : List Nat) (r : Nat) : Nat := xs.countP (· < r)

theorem below_mono (xs : List Nat) {a b : Nat} (h : a ≤ b) :
    below xs a ≤ below xs b := by
  induction xs with
  | nil => simp [below]
  | cons x xs ih =>
    simp only [below, List.countP_cons] at *
    by_cases xa : x < a
    · have xb := Nat.lt_of_lt_of_le xa h
      simp [xa,xb,ih]
    · by_cases xb : x < b <;> simp [xa,xb] <;> omega

theorem below_strict (xs : List Nat) {a b : Nat} (mem : a ∈ xs) (h : a < b) :
    below xs a < below xs b := by
  induction xs with
  | nil => cases mem
  | cons x xs ih =>
    have le := below_mono xs (Nat.le_of_lt h)
    rcases List.mem_cons.mp mem with atHead|atTail
    · subst x
      simp [below,h] at le ⊢
      omega
    · have strict := ih atTail
      simp only [below,List.countP_cons] at strict ⊢
      by_cases xa : x < a
      · have xb := Nat.lt_trans xa h
        simp [xa,xb,strict]
      · by_cases xb : x < b <;> simp [xa,xb] <;> omega

theorem below_inside (xs : List Nat) {a : Nat} (mem : a ∈ xs) :
    below xs a < xs.length := by
  induction xs with
  | nil => cases mem
  | cons x xs ih =>
    rcases List.mem_cons.mp mem with atHead|atTail
    · subst x
      have len := List.countP_le_length (l := xs) (p := fun x => decide (x < a))
      simp [below]
      omega
    · have strict := ih atTail
      simp only [below,List.countP_cons,List.length_cons] at strict ⊢
      split <;> omega

def observations (w : ExactEscapeWire) (n : Nat) : List Nat :=
  List.ofFn fun i : Fin n => rank w.ranks i.val

theorem seen_rank (w : ExactEscapeWire) {n a} (inside : a < n) :
    rank w.ranks a ∈ observations w n :=
  List.mem_ofFn.mpr ⟨⟨a,inside⟩,rfl⟩

def newGrade (w : ExactEscapeWire) (n a : Nat) :=
  1 + below (observations w n) (rank w.ranks a)

def newRanks (w : ExactEscapeWire) (n : Nat) : List Nat :=
  List.ofFn fun i : Fin n => newGrade w n i.val

theorem new_rank_inside (w : ExactEscapeWire) {n a} (inside : a < n) :
    rank (newRanks w n) a = newGrade w n a := by simp [rank,newRanks,inside]

theorem grade_in_range (w : ExactEscapeWire) {n a} (inside : a < n) :
    newGrade w n a < n+1 := by
  have h := below_inside _ (seen_rank w inside)
  have len : (observations w n).length = n := List.length_ofFn
  rw [len] at h
  unfold newGrade
  omega

theorem equal_compact_rank (w : ExactEscapeWire) {n a b}
    (ha : a < n) (hb : b < n) (eq : newGrade w n a = newGrade w n b) :
    rank w.ranks a = rank w.ranks b := by
  by_cases same : rank w.ranks a = rank w.ranks b
  · exact same
  rcases Nat.lt_or_gt_of_ne same with lt|gt
  · have strict := below_strict _ (seen_rank w ha) lt
    unfold newGrade at eq
    omega
  · have strict := below_strict _ (seen_rank w hb) gt
    unfold newGrade at eq
    omega

noncomputable def newSide (w : ExactEscapeWire) (n g : Nat) : Nat := by
  classical
  exact if read : ∃ i : Fin n, newGrade w n i.val = g
    then w.side (Classical.choose read).val else 2

noncomputable def compact (w : ExactEscapeWire) (n : Nat) : ExactEscapeWire :=
  ⟨newRanks w n,List.ofFn fun g : Fin (n+1) => newSide w n g.val⟩

theorem compact_side_exact447 (w : ExactEscapeWire) {n a} (inside : a < n) :
    (compact w n).side a = w.side a := by
  classical
  have small := grade_in_range w inside
  have seen : ∃ i : Fin n, newGrade w n i.val = newGrade w n a :=
    ⟨⟨a,inside⟩,rfl⟩
  change colour (List.ofFn fun i : Fin (n+1) => newSide w n i.val)
    (rank (newRanks w n) a) = _
  rw [new_rank_inside w inside]
  unfold colour
  simp only [List.getElem?_ofFn,dite_eq_left small,Option.getD_some,newSide,dite_eq_left seen]
  exact congrArg (colour w.palette)
    (equal_compact_rank w (Classical.choose seen).isLt inside (Classical.choose_spec seen))

open GeneralDeclarativeGraphRows321 (shapeOf observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)

theorem compact_ready447 {s : GeneralDeclarativeHead320.State} {site w} (yes : SplitReady s site w) :
    SplitReady s site (compact w (rawLimit s site)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a b bound
    rcases nontrivial_bound_inside_support446 (bound_support_from_actual_rows446 s site) bound
      with eq|⟨ha,hb⟩
    · subst b
      exact Nat.le_refl _
    · rw [show (compact w (rawLimit s site)).ranks = newRanks w (rawLimit s site) from rfl,
        new_rank_inside w ha,new_rank_inside w hb]
      exact Nat.add_le_add_left (below_mono _ (yes.boundShape _ _ bound)) _
  · intro e present n eq
    have l : e.left < rawLimit s site := write_name_inside446 present List.mem_cons_self
    have r : n < rawLimit s site := write_name_inside446 present
      (List.mem_cons_of_mem _ (List.mem_append_left _ (by simp [flatEnd,eq])))
    rw [compact_side_exact447 w l,compact_side_exact447 w r]
    exact yes.flatSide _ present _ eq
  · rw [compact_side_exact447 w (root_inside446 s site)]
    exact yes.rootZero
  · intro e inRows head decoded entered n found
    have owner : e.left < rawLimit s site := write_name_inside446 inRows List.mem_cons_self
    have child : n < rawLimit s site := write_name_inside446 inRows
      (List.mem_cons_of_mem _ (List.mem_append_right _ (by simpa [shapeChildren,decoded] using found)))
    rw [compact_side_exact447 w child]
    rw [compact_side_exact447 w owner] at entered
    exact yes.edges _ inRows _ decoded entered _ found

theorem compact_exact_raw_witness447 {s : GeneralDeclarativeHead320.State} {site w}
    (yes : splitCheck446 s site w = true) :
    splitCheck446 s site (compact w (rawLimit s site)) = true ∧
    (compact w (rawLimit s site)).ranks.length = rawLimit s site ∧
    (compact w (rawLimit s site)).palette.length = rawLimit s site+1 ∧
    ∀ n < rawLimit s site, (compact w (rawLimit s site)).side n = w.side n := by
  exact ⟨split_check_reflects_actual_rows446.mpr (compact_ready447
    (split_check_reflects_actual_rows446.mp yes)),List.length_ofFn,List.length_ofFn,
       fun _ inside => compact_side_exact447 w inside⟩

theorem raw_safe_iff_small_witness447 (s : GeneralDeclarativeHead320.State) (site : Nat) :
    (¬AliasCycle s (observed s) site) ↔ ∃ w : ExactEscapeWire,
    splitCheck446 s site w = true ∧ w.ranks.length = rawLimit s site ∧
    w.palette.length = rawLimit s site+1 := by
  constructor
  · intro safe
    obtain ⟨w,yes⟩ := (raw_safe_iff_finite_split_witness446 s site).mp safe
    have both := compact_exact_raw_witness447 yes
    exact ⟨compact w (rawLimit s site),both.1,both.2.1,both.2.2.1⟩
  · rintro ⟨w,yes,_⟩
    exact checked_split_escape_excludes_exact_raw_K2446 yes


end Yulang.GeneralDeclarativeI65.I72.SplitEscape446.SplitCompact447
