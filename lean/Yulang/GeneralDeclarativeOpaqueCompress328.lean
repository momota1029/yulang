import Yulang.GeneralDeclarativeOpaqueDiagnostic328
import Yulang.GeneralDeclarativeCopyCollapse326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueCompress328
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOpaqueIntervals328 (Ends protect left right ready)
open GeneralDeclarativeOpaqueNames328 (kept first second row expose)
open GeneralDeclarativeOpaqueAuthority328 (FreshName before_fresh unchanged_alias)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeCopyCollapse326 (ordinary_eq_names)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeCaptureClosure320 (withOrdinary atoms preserve_bound)

def jump (a b : Nat) : PresenceNormalForm.Atom Nat := .tyLe (.var a) (.var b)

def small (s : State) (e : Ends) : State :=
  withOrdinary s [jump e.firstLo e.firstHi,jump e.secondLo e.secondHi]

def squash (s : State) (root : Nat) (keep : List Nat) (e : Ends) (n : Nat) : Nat :=
  if n = (first s root (protect keep e)) then e.firstLo
  else if n = (second s root (protect keep e)) then e.secondLo else n

section
variable (s : State) (root : Nat) (keep : List Nat) (e : Ends)
local notation "q" => squash s root keep e
local notation "tailA" => (first s root (protect keep e))
local notation "tailB" => (second s root (protect keep e))
local notation "extended" => ready s root keep e
local notation "compressed" => small s e

theorem keeps {n : Nat} (old : n ∈ kept s root (protect keep e)) : q n = n := by
  have a : n < tailA := before_fresh (show FreshName s root (protect keep e) tailA from .inl rfl) old
  have b : n < tailB := before_fresh (show FreshName s root (protect keep e) tailB from .inr rfl) old
  simp [squash,Nat.ne_of_lt a,Nat.ne_of_lt b]

theorem old_name {n : Nat} (present : n ∈ stateNames s) : q n = n :=
  keeps s root keep e (List.mem_append_left _ present)

theorem left_center : q tailA = e.firstLo := by simp [squash]

theorem right_center : q tailB = e.secondLo := by
  have diff : tailB ≠ tailA := Nat.succ_ne_self _
  simp [squash,diff]

theorem oneLo : q e.firstLo = e.firstLo :=
  keeps s root keep e (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem oneHi : q e.firstHi = e.firstHi :=
  keeps s root keep e (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem twoLo : q e.secondLo = e.secondLo :=
  keeps s root keep e (List.mem_append_right _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem twoHi : q e.secondHi = e.secondHi :=
  keeps s root keep e (List.mem_append_right _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))

theorem project_bound {a b : Nat} (h : Bound (extended).normal a b) :
    Bound (compressed).normal (q a) (q b) := by
  induction h with
  | refl => exact .refl _
  | trans _ _ l r => exact .trans l r
  | @interval a b presentOld =>
    change (a,b) ∈ s.normal.intervals at presentOld
    have listed : ∀ n ∈ [a,b], n ∈ stateNames s := fun n h =>
      List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(a,b),presentOld,h⟩))
    rw [old_name s root keep e (listed a List.mem_cons_self),
      old_name s root keep e (listed b (List.mem_cons_of_mem _ List.mem_cons_self))]
    exact .interval presentOld
  | @constraint a b which =>
    change jump a b ∈ s.normal.ordinary ++
      (atoms (left s root keep e) ++ atoms (right s root keep e)) at which
    rcases List.mem_append.mp which with source|added
    · have listed : ∀ n ∈ [a,b], n ∈ stateNames s := fun n h =>
        List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨jump a b,source,h⟩))
      rw [old_name s root keep e (listed a List.mem_cons_self),
        old_name s root keep e (listed b (List.mem_cons_of_mem _ List.mem_cons_self))]
      exact .constraint (List.mem_append_left _ source)
    · change jump a b ∈ [jump e.firstLo tailA,jump tailA e.firstHi,
        jump e.secondLo tailB,jump tailB e.secondHi] at added
      simp only [List.mem_cons,List.not_mem_nil,or_false] at added
      rcases added with add|add|add|add <;> injection add with l r <;> injection l with la <;> injection r with rb <;> subst a <;> subst b
      · rw [oneLo,left_center]
        exact .refl _
      · rw [left_center,oneHi]
        exact .constraint (List.mem_append_right _ List.mem_cons_self)
      · rw [twoLo,right_center]
        exact .refl _
      · rw [right_center,twoHi]
        exact .constraint (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem lift_bound {a b : Nat} (h : Bound (compressed).normal a b) :
    Bound (extended).normal a b := by
  induction h with
  | refl => exact .refl _
  | trans _ _ l r => exact .trans l r
  | interval line => exact .interval line
  | @constraint a b which =>
    change jump a b ∈ s.normal.ordinary ++ [jump e.firstLo e.firstHi,jump e.secondLo e.secondHi] at which
    rcases List.mem_append.mp which with source|added
    · exact .constraint (List.mem_append_left _ source)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at added
      rcases added with add|add <;> injection add with l r <;> injection l with la <;> injection r with rb <;> subst a <;> subst b
      · exact .trans (.constraint (List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self)))
          (.constraint (List.mem_append_right _ (List.mem_append_left _
            (List.mem_cons_of_mem _ List.mem_cons_self))))
      · exact .trans (.constraint (List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)))
          (.constraint (List.mem_append_right _ (List.mem_append_right _
            (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem variable_old {a b : Nat} (got : (⟨a,.variable b⟩ : Equation) ∈ (extended).equations) :
    (⟨a,.variable b⟩ : Equation) ∈ s.equations := by
  rcases List.mem_append.mp got with source|added
  · exact source
  · have impossible := congrArg Equation.right (List.mem_singleton.mp added)
    cases impossible

theorem project_alias {a b : Nat} (same : Alias extended a b) :
    Alias compressed (q a) (q b) := by
  have variable_same {a b : Nat} (got : (⟨a,.variable b⟩ : Equation) ∈ (extended).equations) :
      (⟨q a,.variable (q b)⟩ : Equation) ∈ (compressed).equations := by
    have inOld := variable_old s root keep e got
    have listed := ordinary_eq_names (⟨a,.variable b⟩ : Equation) inOld
    rw [old_name s root keep e (listed List.mem_cons_self),
      old_name s root keep e (listed (List.mem_cons_of_mem _ List.mem_cons_self))]
    exact inOld
  induction same with
  | bounds lo hi => exact .bounds (project_bound s root keep e lo) (project_bound s root keep e hi)
  | forward present => exact .forward (variable_same present)
  | backward present => exact .backward (variable_same present)
  | trans _ _ l r => exact .trans l r

theorem lift_alias {a b : Nat} (same : Alias compressed a b) : Alias extended a b := by
  induction same with
  | bounds lo hi => exact .bounds (lift_bound s root keep e lo) (lift_bound s root keep e hi)
  | forward present => exact .forward (List.mem_append_left _ present)
  | backward present => exact .backward (List.mem_append_left _ present)
  | trans _ _ l r => exact .trans l r

/-- On old names the *entire* change of ordinary aliasing from fresh
pair naming with bounds is exactly the two literal endpoint bridges.
This does not identify fresh nodes with their endpoints. -/
theorem alias_exact {a b : Nat}
    (oldA : a ∈ kept s root (protect keep e)) (oldB : b ∈ kept s root (protect keep e)) :
    Alias extended a b ↔ Alias compressed a b := by
  constructor
  · intro same
    simpa only [keeps s root keep e oldA,keeps s root keep e oldB] using project_alias s root keep e same
  · exact lift_alias s root keep e

theorem bound_exact {a b : Nat}
    (oldA : a ∈ kept s root (protect keep e)) (oldB : b ∈ kept s root (protect keep e)) :
    Bound (extended).normal a b ↔ Bound (compressed).normal a b := by
  constructor
  · intro same
    simpa only [keeps s root keep e oldA,keeps s root keep e oldB] using project_bound s root keep e same
  · exact lift_bound s root keep e

theorem collapse_old {a b : Nat}
    (l : Bound s.normal e.firstLo e.firstHi) (r : Bound s.normal e.secondLo e.secondHi)
    (p : Bound (compressed).normal a b) : Bound s.normal a b := by
  induction p with
  | refl => exact .refl _
  | trans _ _ x y => exact .trans x y
  | interval h => exact .interval h
  | @constraint a b which =>
    change jump a b ∈ s.normal.ordinary ++ [jump e.firstLo e.firstHi,jump e.secondLo e.secondHi] at which
    rcases List.mem_append.mp which with old|added
    · exact .constraint old
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at added
      rcases added with add|add <;> injection add with al bl <;> injection al <;> injection bl <;> subst a <;> subst b
      · exact l
      · exact r

theorem alias_from_small {a b : Nat}
    (l : Bound s.normal e.firstLo e.firstHi) (r : Bound s.normal e.secondLo e.secondHi)
    (h : Alias (compressed) a b) : Alias s a b := by
  induction h with
  | bounds lower upper => exact .bounds (collapse_old s e l r lower) (collapse_old s e l r upper)
  | forward present => exact .forward present
  | backward present => exact .backward present
  | trans _ _ lower upper => exact .trans lower upper

theorem alias_to_small {a b : Nat} (h : Alias s a b) : Alias (compressed) a b := by
  induction h with
  | bounds lower upper => exact .bounds (preserve_bound lower _) (preserve_bound upper _)
  | forward present => exact .forward present
  | backward present => exact .backward present
  | trans _ _ lower upper => exact .trans lower upper

/-- Existing ordinary syntactic component bridges suffice to preserve
all protected-name aliases; semantic model entailment alone does not. -/
theorem old_alias_if {a b : Nat}
    (l : Bound s.normal e.firstLo e.firstHi) (r : Bound s.normal e.secondLo e.secondHi)
    (oldA : a ∈ kept s root (protect keep e)) (oldB : b ∈ kept s root (protect keep e)) :
    Alias extended a b ↔ Alias s a b := by
  rw [alias_exact s root keep e oldA oldB]
  exact ⟨alias_from_small s e l r,alias_to_small s e⟩

end
end Yulang.GeneralDeclarativeOpaqueCompress328
