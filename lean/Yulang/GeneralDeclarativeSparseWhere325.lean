import Yulang.GeneralDeclarativeClauseOrigins325
import Yulang.GeneralDeclarativeFreshCalls321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSparseWhere325
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeNewNames321 (numbered)
open GeneralDeclarativeFreshCalls321 (argCode)
open GeneralDeclarativeClauseOrigins325 (Origin origin_here)

def job (p : Pattern) (e : Expr) : Option Expr :=
  match normalize p with
  | .var _ => none
  | _ => some e

theorem direct_omitted (bare : normalize p = .var n) : job p e = none := by simp [job,bare]

theorem compound_job (nonvar : Compound p) : job p e = some e := by
  cases h : normalize p with
  | var n => exact False.elim (nonvar n h)
  | app | record | variant | join => simp [job,h]

def plan : List Pattern → List Expr → List (Option Expr)
  | p::ps,e::es => job p e :: plan ps es
  | _,_ => []

theorem planned {p : Pattern} {e : Expr} {n : Nat}
    (pos : ps[n]? = some p) (code : es[n]? = some e) : (plan ps es)[n]? = some (job p e) := by
  induction n generalizing ps es with
  | zero =>
    cases ps with
    | nil => cases pos
    | cons a rem =>
      cases es with
      | nil => cases code
      | cons b tail =>
        cases Option.some.inj pos
        cases Option.some.inj code
        rfl
  | succ n ih =>
    cases ps with
    | nil => cases pos
    | cons a rem =>
      cases es with
      | nil => cases code
      | cons b tail => exact ih pos code

def bodies (capture : Nat → Capture) : List (Option Expr) → List Expr
  | [] => []
  | none::rest => bodies capture rest
  | some e::rest => argCode capture e ++ bodies capture rest

def atPosition (start : Nat) : List (Option Expr) → Nat → Capture
  | [],_ => ⟨start,start,start⟩
  | none::_rest,0 => ⟨start,start,start⟩
  | some _::_rest,0 => ⟨start,start+1,start+2⟩
  | none::rest,n+1 => atPosition start rest n
  | some _::rest,n+1 => atPosition (start+3) rest n

theorem allocated {s : State} {jobs : List (Option Expr)} {capture : Nat → Capture}
    (recorded : numbered start (bodies capture jobs) ⊆ s.equations)
    (wasJob : jobs[n]? = some (some e)) :
    Origin s (atPosition start jobs n).lower (logical capture .lower e) ∧
    Origin s (atPosition start jobs n).center (logical capture .actual e) ∧
    Origin s (atPosition start jobs n).upper (logical capture .upper e) := by
  induction n generalizing jobs start with
  | zero =>
    cases jobs with
    | nil => cases wasJob
    | cons current rest =>
      have someCurrent : current = some e := Option.some.inj wasJob
      subst current
      have first : (⟨start,logical capture .lower e⟩ : Equation) ∈ s.equations := recorded List.mem_cons_self
      have center : (⟨start+1,logical capture .actual e⟩ : Equation) ∈ s.equations :=
        recorded (List.mem_cons_of_mem _ List.mem_cons_self)
      have upper : (⟨start+2,logical capture .upper e⟩ : Equation) ∈ s.equations :=
        recorded (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      exact ⟨origin_here first,origin_here center,origin_here upper⟩
  | succ n ih =>
    cases jobs with
    | nil => cases wasJob
    | cons current rest =>
      cases current with
      | none => exact ih recorded wasJob
      | some code =>
        have next : numbered (start+3) (bodies capture rest) ⊆ s.equations := by
          intro eq listed
          exact recorded (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ listed)))
        exact ih next wasJob

theorem direct_reuses_source (bare : normalize p = .var n) :
    GeneralDeclarativeSourceEmission322.useArg names (atPosition start jobs pos) p = names.input n :=
  GeneralDeclarativeSourceEmission322.source_var names _ p bare

end Yulang.GeneralDeclarativeSparseWhere325
