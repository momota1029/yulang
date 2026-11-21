import Yulang.GeneralDeclarativeWhereIntervals325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereLayouts325
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSparseWhere325 (job plan atPosition direct_omitted)

def links (a : Capture) : List (Nat × Nat) := [(a.lower,a.center),(a.center,a.upper)]

def spans (start : Nat) : List (Option Expr) → List (Nat × Nat)
  | [] => []
  | none::rest => spans start rest
  | some _::rest => links ⟨start,start+1,start+2⟩ ++ spans (start+3) rest

theorem accounted {jobs : List (Option Expr)} {n : Nat} (chosen : jobs[n]? = some (some code)) :
    links (atPosition start jobs n) ⊆ spans start jobs := by
  induction n generalizing jobs start with
  | zero =>
    cases jobs with
    | nil => cases chosen
    | cons first rest =>
      cases Option.some.inj chosen
      exact fun _ h => List.mem_append_left _ h
  | succ n ih =>
    cases jobs with
    | nil => cases chosen
    | cons first rest =>
      cases first with
      | none => exact ih chosen
      | some exp => exact fun _ h => List.mem_append_right _ (ih chosen h)

theorem of_compound {jobs : List (Option Expr)} (introduced : link ∈ spans start jobs) :
    ∃ n : Nat, ∃ code, jobs[n]? = some (some code) ∧ link ∈ links (atPosition start jobs n) := by
  induction jobs generalizing start with
  | nil => cases introduced
  | cons first rest ih =>
    cases first with
    | none =>
      obtain ⟨n,e,found,wrote⟩ := ih introduced
      exact ⟨n+1,e,found,wrote⟩
    | some exp =>
      rcases List.mem_append.mp introduced with used|later
      · exact ⟨0,exp,rfl,used⟩
      · obtain ⟨n,e,found,wrote⟩ := ih later
        exact ⟨n+1,e,found,wrote⟩

theorem find_position {ps : List Pattern} {es : List Expr} {n : Nat}
    (accounted : (plan ps es)[n]? = some (some code)) :
    ∃ p, ps[n]? = some p ∧ es[n]? = some code ∧ GeneralDeclarativeEmissionOperands322.Compound p := by
  induction n generalizing ps es with
  | zero =>
    cases ps with
    | nil => cases accounted
    | cons p rest =>
      cases es with
      | nil => cases accounted
      | cons e more =>
        have existsCode : job p e = some code := Option.some.inj accounted
        cases shape : normalize p with
        | var name => simp [direct_omitted shape] at existsCode
        | app | variant | join | record =>
          have matched : e = code := by simpa [job,shape] using existsCode
          subst e
          refine ⟨p,rfl,rfl,?_⟩
          intro name wrong
          rw [shape] at wrong
          cases wrong
  | succ n ih =>
    cases ps with
    | nil => cases accounted
    | cons p rest =>
      cases es with
      | nil => cases accounted
      | cons e more => exact ih accounted

end Yulang.GeneralDeclarativeWhereLayouts325
