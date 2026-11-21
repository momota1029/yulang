import Yulang.GeneralDeclarativeSparseWhere325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFreshWhere325
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSparseWhere325 (job plan bodies atPosition planned allocated compound_job)
open GeneralDeclarativeNewNames321 (after supply old_plus_extra)
open GeneralDeclarativeClauseOrigins325 (Origin)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)

def seed (s : State) (protect : List Nat) (cap : Nat → Capture) (jobs : List (Option Expr)) : Nat :=
  after ((stateNames s ++ protect) ++ (bodies cap jobs).flatMap names)

def newState (s : State) (protect : List Nat) (cap : Nat → Capture) (jobs : List (Option Expr)) : State :=
  appendFacts s (supply s protect (bodies cap jobs))

/-- Only a genuinely compound position receives three new ordinary
defined names. This does not force any old result target equation or
infer whether the new child is ready for candidate inspection. -/
theorem compound_reads (s : State) (protect : List Nat) (cap : Nat → Capture)
    (pos : ps[j]? = some p) (decoded : es[j]? = some e) (needed : Compound p) :
    let jobs := plan ps es
    let a := atPosition (seed s protect cap jobs) jobs j
    let t := newState s protect cap jobs
    Origin t a.lower (logical cap .lower e) ∧
    Origin t a.center (logical cap .actual e) ∧ Origin t a.upper (logical cap .upper e) := by
  dsimp
  have built := planned pos decoded
  rw [compound_job needed] at built
  apply allocated ?_ built
  intro row listed
  exact List.mem_append_right _ listed

theorem projection (s : State) (protect : List Nat) (cap : Nat → Capture)
    (jobs : List (Option Expr)) (m : Assignment) :
    Models s m ↔ ∃ next, Models (newState s protect cap jobs) next ∧
      ∀ n ∈ stateNames s ++ protect, next n = m n := by
  constructor
  · intro valid
    obtain ⟨new,kept⟩ := old_plus_extra s protect (bodies cap jobs) m valid
    exact ⟨_,new,kept⟩
  · rintro ⟨next,new,kept⟩
    have prior := ((model_append next).mp new).1
    exact (preserves_models s (fun n used => kept n (List.mem_append_left _ used))).mp prior

theorem count (cap : Nat → Capture) (jobs : List (Option Expr)) :
    (bodies cap jobs).length = 3 * (jobs.filterMap id).length := by
  induction jobs with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | none => simpa [bodies] using ih
    | some e =>
      simp only [bodies,List.length_append]
      change 3 + (bodies cap rest).length = 3 * ((rest.filterMap id).length + 1)
      omega

end Yulang.GeneralDeclarativeFreshWhere325
