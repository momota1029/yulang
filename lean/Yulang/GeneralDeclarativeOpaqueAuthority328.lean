import Yulang.GeneralDeclarativeOpaqueNames328
import Yulang.GeneralDeclarativeGraphFootprint326
import Yulang.GeneralDeclarativeCopyCollapse326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueAuthority328
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOpaqueNames328 (kept first second row expose)
open GeneralDeclarativeFootprint321 (stateNames equationNames atomSources typeSources)
open GeneralDeclarativeOrigins321 (Supported Backed restriction backed_iff)
open GeneralDeclarativeCopyCollapse326 (ordinary_eq_names)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl alias_mono)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeNewNames321 (before_after)

def FreshName (s : State) (root : Nat) (extra : List Nat) (n : Nat) : Prop :=
  n = first s root extra ∨ n = second s root extra

theorem before_fresh {s : State} {root extra n old}
    (a : FreshName s root extra n) (b : old ∈ kept s root extra) : old < n := by
  rcases a with rfl|rfl
  · exact before_after b
  · exact Nat.lt_succ_of_lt (before_after b)

theorem outside {s : State} {root extra n} (a : FreshName s root extra n) :
    n ∉ stateNames s := by
  intro old
  exact (Nat.lt_irrefl _) (before_fresh a (List.mem_append_left _ old))

theorem not_root {s : State} {root extra n} (a : FreshName s root extra n) :
    n ≠ root := by
  intro same
  subst root
  exact (Nat.lt_irrefl _) (before_fresh a (List.mem_append_right _ List.mem_cons_self))

theorem new_row_not_old (s : State) (root : Nat) (extra : List Nat) : row s root extra ∉ s.equations := by
  intro old
  exact outside (s := s) (root := root) (extra := extra) (.inl rfl)
    (ordinary_eq_names _ old (List.mem_cons_of_mem _ List.mem_cons_self))

/-- Ordinary pair readback is deliberately not a new source origin.
All pre-existing backed rows are retained, and the copied witness
view is exactly the original support restriction before adding any
additional projected interval bounds. -/
def retain {s : State} (p : Supported s completed) (root : Nat) (extra : List Nat) :
    Supported (expose s root extra) completed :=
  ⟨p.derivesFrom,fun h => List.mem_append_left _ (p.ordinary h)⟩

theorem exactly_old_support {s : State} (p : Supported s completed) (root : Nat) (extra : List Nat) :
    restriction (retain p root extra) = restriction p := by
  classical
  have noNew : ¬Backed (retain p root extra) (row s root extra) := by
    intro added
    obtain ⟨_,already,_⟩ := added
    exact new_row_not_old s root extra (p.ordinary already)
  unfold restriction expose GeneralDeclarativeEntailment320.appendFacts
  simp only [List.filter_append]
  congr 1
  have noAlso : List.filter (fun e => decide (Backed (retain p root extra) e)) [row s root extra] = [] := by
    simp [noNew]
  rw [noAlso,List.append_nil]
  rfl

theorem unchanged_alias {s : State} (root : Nat) (extra : List Nat) :
    Alias (expose s root extra) a b ↔ Alias s a b := by
  constructor
  · have old {x y : Nat} (eq : (⟨x,.variable y⟩ : Equation) ∈ (expose s root extra).equations) :
        (⟨x,.variable y⟩ : Equation) ∈ s.equations := by
      rcases List.mem_append.mp eq with old|later
      · exact old
      · have bad := congrArg Equation.right (List.mem_singleton.mp later)
        cases bad
    intro route
    induction route with
    | bounds lo hi => exact .bounds lo hi
    | forward eq => exact .forward (old eq)
    | backward eq => exact .backward (old eq)
    | trans _ _ a b => exact .trans a b
  · exact alias_mono (s := s) (t := expose s root extra) rfl (fun _ h => List.mem_append_left _ h)

theorem bound_places {s : State} (fact : Bound s.normal a b) :
    a = b ∨ a ∈ stateNames s ∧ b ∈ stateNames s := by
  induction fact with
  | refl => exact .inl rfl
  | @interval a b listed =>
    have inFootprint (n) (found : n ∈ [a,b]) : n ∈ stateNames s :=
      List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨(a,b),listed,found⟩))
    exact .inr ⟨inFootprint a List.mem_cons_self,inFootprint b (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  | @constraint a b listed =>
    have inFootprint (n) (found : n ∈ [a,b]) : n ∈ stateNames s :=
      List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨_,listed,found⟩))
    exact .inr ⟨inFootprint a List.mem_cons_self,inFootprint b (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  | trans _ _ i j =>
    rcases i with same|⟨start,mid⟩
    · simpa only [same] using j
    · rcases j with same|⟨_,done⟩
      · exact .inr ⟨start,same ▸ mid⟩
      · exact .inr ⟨start,done⟩

theorem alias_places {s : State} (fact : Alias s a b) :
    a = b ∨ a ∈ stateNames s ∧ b ∈ stateNames s := by
  induction fact with
  | bounds lo _ => exact bound_places lo
  | forward visible =>
    have all := ordinary_eq_names _ visible
    exact .inr ⟨all List.mem_cons_self,all (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  | backward visible =>
    have all := ordinary_eq_names _ visible
    exact .inr ⟨all (List.mem_cons_of_mem _ List.mem_cons_self),all List.mem_cons_self⟩
  | trans _ _ i j =>
    rcases i with same|⟨start,mid⟩
    · simpa only [same] using j
    · rcases j with same|⟨_,endHere⟩
      · exact .inr ⟨start,same ▸ mid⟩
      · exact .inr ⟨start,endHere⟩

theorem fresh_alias {s : State} (name : FreshName s root extra a)
    (connected : Alias (expose s root extra) a b) : a = b := by
  rcases alias_places ((unchanged_alias root extra).mp connected) with equal|⟨before,_⟩
  · exact equal
  · exact False.elim (outside name before)

end Yulang.GeneralDeclarativeOpaqueAuthority328
