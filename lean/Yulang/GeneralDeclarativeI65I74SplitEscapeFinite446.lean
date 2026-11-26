import Yulang.GeneralDeclarativeI65I74SplitBoundRank446

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SplitEscape446
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeK2Graph321 (Shape Descends Path path_cat edge_transport)
open GeneralDeclarativeLowerKnown321 (alias_refl alias_symm)
open GeneralDeclarativeGraphRows321 (shapeOf observed structural literal_head)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeWitnessRank350 (rank)
open PresenceNormalForm (Atom)
open List410

private abbrev Raw := GeneralDeclarativeHead320.State
private abbrev Al := GeneralDeclarativeLowerKnown321.Alias

def boundAtomNames : Atom Nat → List Nat
  | .tyLe (.var a) (.var b) => [a,b]
  | _ => []

def flatEnd (e : Equation) : List Nat :=
  match e.right with
  | .variable n => [n]
  | _ => []

def shapeChildren (e : Equation) : List Nat := (shapeOf e.right).map Shape.children |>.getD []

def writeNames (e : Equation) : List Nat := e.left :: (flatEnd e ++ shapeChildren e)

def rawNames (s : Raw) (site : Nat) : List Nat :=
  site :: (s.normal.ordinary.flatMap boundAtomNames ++
    (s.normal.intervals.flatMap (fun z => [z.1,z.2]) ++ s.equations.flatMap writeNames))

def cap : List Nat → Nat
  | [] => 0
  | x::xs => max (x + 1) (cap xs)

theorem mem_below_cap446 {xs : List Nat} {x : Nat} (seen : x ∈ xs) : x < cap xs := by
  induction xs with
  | nil => cases seen
  | cons h rest ih =>
    rcases List.mem_cons.mp seen with same|tail
    · subst x
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih tail) (Nat.le_max_right _ _)

def rawLimit (s : Raw) (site : Nat) : Nat := cap (rawNames s site)

theorem root_inside446 (s : Raw) (site : Nat) : site < rawLimit s site :=
  mem_below_cap446 List.mem_cons_self

theorem bound_support_from_actual_rows446 (s : Raw) (site : Nat) :
    BoundSupport s.normal (rawLimit s site) := by
  have intake (z : Nat) (h : z ∈ s.normal.ordinary.flatMap boundAtomNames ∨
      z ∈ s.normal.intervals.flatMap (fun pair => [pair.1,pair.2])) :
      z < rawLimit s site := by
    apply mem_below_cap446
    apply List.mem_cons_of_mem
    rcases h with a|b
    · exact List.mem_append_left _ a
    · exact List.mem_append_right _ (List.mem_append_left _ b)
  refine ⟨?_,?_⟩
  · intro a b row
    exact ⟨intake a (.inr (List.mem_flatMap.mpr ⟨(a,b),row,List.mem_cons_self⟩)),
      intake b (.inr (List.mem_flatMap.mpr
        ⟨(a,b),row,List.mem_cons_of_mem _ List.mem_cons_self⟩))⟩
  · intro a b row
    exact ⟨intake a (.inl (List.mem_flatMap.mpr ⟨_,row,List.mem_cons_self⟩)),
      intake b (.inl (List.mem_flatMap.mpr ⟨_,row,List.mem_cons_of_mem _ List.mem_cons_self⟩))⟩

theorem write_name_inside446 {s : Raw} {site : Nat} {e : Equation} {n : Nat}
    (row : e ∈ s.equations) (name : n ∈ writeNames e) : n < rawLimit s site := by
  apply mem_below_cap446
  exact List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e,row,name⟩)))

/-- A nonempty structural path, with ordinary Alias only as the final
location correspondence. No repeated payload or solver step is used. -/
def nonemptyReaches (s : Raw) (site n : Nat) : Prop :=
  ∃ first last, Descends (structural s) site first ∧
    Path (structural s) first last ∧ Al s last n

theorem reach_respects_alias446 {s : Raw} {site a b} (same : Al s a b) :
    nonemptyReaches s site a ↔ nonemptyReaches s site b := by
  constructor
  · rintro ⟨first,last,head,tail,atA⟩
    exact ⟨first,last,head,tail,.trans atA same⟩
  · rintro ⟨first,last,head,tail,atB⟩
    exact ⟨first,last,head,tail,.trans atB (alias_symm same)⟩

theorem reachable_not_root_alias446 {s : Raw} {site n}
    (safe : ¬AliasCycle s (observed s) site) (reached : nonemptyReaches s site n) :
    ¬Al s site n := by
  rintro atRoot
  obtain ⟨first,last,head,tail,same⟩ := reached
  exact safe ⟨first,last,head,tail,.trans same (alias_symm atRoot)⟩

noncomputable def desiredSide (s : Raw) (site n : Nat) : Nat := by
  classical
  exact if Al s site n then 0 else if nonemptyReaches s site n then 1 else 2

theorem desired_side_respects_alias446 {s : Raw} {site a b} (same : Al s a b) :
    desiredSide s site a = desiredSide s site b := by
  classical
  have root : Al s site a ↔ Al s site b :=
    ⟨fun h => .trans h same,fun h => .trans h (alias_symm same)⟩
  simp [desiredSide,root,reach_respects_alias446 same]

theorem desired_side_moves_forward446 {s : Raw} {site a b}
    (safe : ¬AliasCycle s (observed s) site) (here : desiredSide s site a ≤ 1)
    (edge : Descends (structural s) a b) : desiredSide s site b = 1 := by
  classical
  have hit : nonemptyReaches s site b := by
    by_cases isRoot : Al s site a
    · exact ⟨b,b,edge_transport isRoot edge,.refl _,alias_refl _⟩
    · by_cases atA : nonemptyReaches s site a
      · obtain ⟨first,last,head,tail,toA⟩ := atA
        exact ⟨first,b,head,path_cat tail (.next (edge_transport toA edge) (.refl _)),alias_refl _⟩
      · simp [desiredSide,isRoot,atA] at here
  simp [desiredSide,reachable_not_root_alias446 safe hit,hit]

noncomputable def gradeSide (s : Raw) (site limit grade : Nat) : Nat := by
  classical
  exact if seen : ∃ i : Fin limit, rank (boundGrades s.normal limit) i.val = grade
    then desiredSide s site (Classical.choose seen).val else 2

noncomputable def finiteWire (s : Raw) (site : Nat) : ExactEscapeWire :=
  let limit := rawLimit s site
  ⟨boundGrades s.normal limit,List.ofFn (fun i : Fin (2 ^ limit + 1) =>
    gradeSide s site limit i.val)⟩

theorem finite_wire_exact_side_on_support446 {s : Raw} {site n}
    (inside : n < rawLimit s site) :
    (finiteWire s site).side n = desiredSide s site n := by
  classical
  let limit := rawLimit s site
  let grade := rank (boundGrades s.normal limit) n
  have small : grade < 2 ^ limit + 1 := active_grade_bounded446 inside
  have seen : ∃ i : Fin limit, rank (boundGrades s.normal limit) i.val = grade :=
    ⟨⟨n,inside⟩,rfl⟩
  change colour (List.ofFn fun i : Fin (2 ^ limit + 1) =>
    gradeSide s site limit i.val) grade = _
  unfold colour
  simp only [List.getElem?_ofFn,dite_eq_left small,Option.getD_some]
  change gradeSide s site limit grade = _
  unfold gradeSide
  rw [dite_eq_left seen]
  have congr := equal_active_grades_are_exact_SCC446 (Classical.choose seen).isLt inside
    (Classical.choose_spec seen)
  exact desired_side_respects_alias446 (.bounds congr.1 congr.2)

theorem finite_wire_ready446 (s : Raw) (site : Nat) (safe : ¬AliasCycle s (observed s) site) :
    SplitReady s site (finiteWire s site) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro a b bound
    exact bound_grade_monotone446 (bound_support_from_actual_rows446 s site) bound
  · intro e has n eq
    have l : e.left < rawLimit s site := write_name_inside446 has List.mem_cons_self
    have r : n < rawLimit s site := write_name_inside446 has
      (List.mem_cons_of_mem _ (List.mem_append_left _ (by simp [flatEnd,eq])))
    rw [finite_wire_exact_side_on_support446 l,finite_wire_exact_side_on_support446 r]
    have row : (⟨e.left,.variable n⟩ : Equation) ∈ s.equations := by
      cases e
      dsimp at eq ⊢
      subst_vars
      exact has
    exact desired_side_respects_alias446 (.forward row)
  · rw [finite_wire_exact_side_on_support446 (root_inside446 s site)]
    simp [desiredSide,alias_refl]
  · intro e inRows head decoded entered n found
    have owner : e.left < rawLimit s site := write_name_inside446 inRows List.mem_cons_self
    have child : n < rawLimit s site := write_name_inside446 inRows
      (List.mem_cons_of_mem _ (List.mem_append_right _ (by simpa [shapeChildren,decoded] using found)))
    rw [finite_wire_exact_side_on_support446 child]
    rw [finite_wire_exact_side_on_support446 owner] at entered
    exact desired_side_moves_forward446 safe entered ⟨head,literal_head inRows decoded,found⟩

/-- Exact finite witness EXISTENCE for the original raw AliasCycle.
The witness can be very large; the proof does not implement a solver
or claim its termination. Stored grades separate directed Bound
from the later flat-Alias side comparison. -/
theorem raw_safe_iff_finite_split_witness446 (s : Raw) (site : Nat) :
    (¬AliasCycle s (observed s) site) ↔ ∃ w : ExactEscapeWire, splitCheck446 s site w = true := by
  constructor
  · intro safe
    exact ⟨finiteWire s site,split_check_reflects_actual_rows446.mpr (finite_wire_ready446 s site safe)⟩
  · rintro ⟨w,yes⟩
    exact checked_split_escape_excludes_exact_raw_K2446 yes

end Yulang.GeneralDeclarativeI65.I72.SplitEscape446
