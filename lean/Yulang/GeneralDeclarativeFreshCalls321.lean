import Yulang.GeneralDeclarativeNewNames321
import Yulang.GeneralDeclarativeWhereProducer321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace Yulang.GeneralDeclarativeFreshCalls321
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeNewNames321 (numbered after supply fresh_supply old_plus_extra)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeFresh321 (extend)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarations (Registry Clause)
open GeneralSourceState (Output)
open CommonRoleOutermostResolver (All₂)

def argCode (capture : Nat → Capture) (code : Expr) : List Expr :=
  [logical capture .lower code,logical capture .actual code,logical capture .upper code]

def codes (capture : Nat → Capture) (args : List Expr) (outputs : List (Nat × Expr)) : List Expr :=
  args.flatMap (argCode capture) ++ outputs.map (fun pr => logical capture .actual pr.2)

def arguments (first : Nat) : List Expr → List Capture
  | [] => []
  | _ :: more => ⟨first,first+1,first+2⟩ :: arguments (first+3) more

def results (first : Nat) : List (Nat × Expr) → List Output
  | [] => []
  | (key,_) :: more => ⟨key,first⟩ :: results (first+1) more

def demand (role first : Nat) (args : List Expr) (outputs : List (Nat × Expr)) : Demand :=
  ⟨role,arguments first args,results (first + 3 * args.length) outputs⟩

def seed (s : State) (extra : List Nat) (exps : List Expr) : Nat :=
  after ((stateNames s ++ extra) ++ exps.flatMap names)

/-- Compilation from declaration syntax preserves the order of actual
where operands and the order and names of its associated requests. -/
structure SourceCodes (r : Registry) (interp : Interpretation) (clause : Clause)
    (args : List Expr) (out : List (Nat × Expr)) : Prop where
  arguments : All₂ (fun pattern code => translate r.constructors interp (normalize pattern) = some code)
    clause.arguments args
  outputs : All₂ (fun eqn pr => pr.1 = eqn.name ∧ translate r.constructors interp eqn.rhs = some pr.2)
    clause.outputs out

theorem length_argCode (capture : Nat → Capture) (args : List Expr) :
    (args.flatMap (argCode capture)).length = 3 * args.length := by
  induction args with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.flatMap_cons,List.length_append,argCode,List.length_cons,List.length_nil,ih]
    omega

theorem from_append (first : Nat) (a b : List Expr) :
    numbered first (a ++ b) = numbered first a ++ numbered (first+a.length) b := by
  induction a generalizing first with
  | nil => simp [numbered]
  | cons one rest ih =>
    simp only [List.cons_append,numbered,ih,List.length_cons]
    have ix : first + 1 + rest.length = first + (rest.length + 1) := by omega
    rw [ix]

end Yulang.GeneralDeclarativeFreshCalls321
