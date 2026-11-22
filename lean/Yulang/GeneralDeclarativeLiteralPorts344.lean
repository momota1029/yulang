import Yulang.GeneralDeclarativeReplayOrdering344

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeLiteralPorts344
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr translateMany)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarations (Clause)
open GeneralDeclarativeClauseBatch327 (Port prepare make make_grows reflexive)
open GeneralDeclarativeFreshInputs325 (prepared)
open GeneralDeclarativeFreshWhere325 (seed newState)
open GeneralDeclarativeNewNames321 (numbered supply)
open GeneralDeclarativeSparseWhere325 (bodies plan atPosition planned compound_job)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeGrowth327 (Extends trans)
open CommonRoleOutermostResolver (All₂)

def Rows (s : State) (cap : Nat → Capture) (a : Capture) (e : Expr) : Prop :=
  (⟨a.lower,logical cap .lower e⟩ : Equation) ∈ s.equations ∧
  (⟨a.center,logical cap .actual e⟩ : Equation) ∈ s.equations ∧
  (⟨a.upper,logical cap .upper e⟩ : Equation) ∈ s.equations

theorem numbered_at {s : State} {js : List (Option Expr)} {cap : Nat → Capture}
    (recorded : numbered start (bodies cap js) ⊆ s.equations)
    (job : js[n]? = some (some e)) : Rows s cap (atPosition start js n) e := by
  induction n generalizing js start with
  | zero =>
    cases js with
    | nil => cases job
    | cons x rest =>
      have equal : x = some e := Option.some.inj job
      subst x
      exact ⟨recorded List.mem_cons_self,
        recorded (List.mem_cons_of_mem _ List.mem_cons_self),
        recorded (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  | succ n ih =>
    cases js with
    | nil => cases job
    | cons x rest =>
      cases x with
      | none => exact ih recorded job
      | some first =>
        have later : numbered (start+3) (bodies cap rest) ⊆ s.equations :=
          fun _ present => recorded (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present)))
        exact ih later job

def Literal (s : State) (cap : Nat → Capture) (cl : Clause) (port : Port) : Prop :=
  ∀ j pat e, cl.arguments[j]? = some pat → port.code[j]? = some e → Compound pat →
    Rows s cap (port.input j) e

theorem produced_at {s t : State} {cl : Clause} {codes : List Expr} {protect : List Nat} {cap : Nat → Capture}
    (grown : Extends (prepared s protect cap (plan cl.arguments codes)) t) :
    Literal t cap cl (make s protect cap cl codes) := by
  intro j p e source code complex
  have atJob := planned source code
  rw [compound_job complex] at atJob
  apply numbered_at (start := seed s protect cap (plan cl.arguments codes)) ?_ atJob
  intro row listed
  apply grown.equations
  change row ∈ s.equations ++ supply s protect (bodies cap (plan cl.arguments codes))
  exact List.mem_append_right _ listed

/-- Follow the actual normalized compiler fold, including each
allocation offset. Every compound triple is literally present in
the final prepared frame, rather than known only up to alias. -/
theorem read {s t : State} {cs : List Clause} {ports : List Port}
    (actual : prepare c i protect cap s cs = some (t,ports)) :
    Extends s t ∧ All₂ (Literal t cap) cs ports := by
  induction cs generalizing s ports with
  | nil =>
    have eq : (s,[]) = (t,ports) := Option.some.inj actual
    cases eq
    exact ⟨reflexive _,.nil⟩
  | cons cl rest ih =>
    cases viewed : translateMany c i (cl.arguments.map normalize) with
    | none => simp [prepare,viewed] at actual
    | some codes =>
      let next := prepared s protect cap (plan cl.arguments codes)
      cases more : prepare c i protect cap next rest with
      | none => simp [prepare,viewed,next,more] at actual
      | some pair =>
        obtain ⟨final,remaining⟩ := pair
        have eq : (final,make s protect cap cl codes :: remaining) = (t,ports) := by
          simpa [prepare,viewed,next,more] using actual
        cases eq
        obtain ⟨advance,ordered⟩ := ih more
        exact ⟨trans (make_grows s protect cap _) advance,.cons (produced_at advance) ordered⟩

end Yulang.GeneralDeclarativeLiteralPorts344
