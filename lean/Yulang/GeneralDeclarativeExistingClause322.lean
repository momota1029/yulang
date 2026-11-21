import Yulang.GeneralDeclarativeEqualities322
import Yulang.GeneralDeclarativeFreshExact321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExistingClause322
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeCompileLists321 (Result zip_result)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeFreshCalls321 (SourceCodes)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeArgumentFacts320 (whereFacts)
open GeneralDeclarativeOutputFacts320 (childFact)
open GeneralDeclarativeNodeFacts320 (clauseFacts)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralDeclarations (Clause Registry)
open GeneralSourceState (Output)
open CommonRoleOutermostResolver (All₂)

def Refers (s : State) (capture : Nat → Capture) (code : Expr) (argument : Capture) : Prop :=
  Derives s (.variable argument.lower) (logical capture .lower code) ∧
  Derives s (.variable argument.center) (logical capture .actual code) ∧
  Derives s (.variable argument.upper) (logical capture .upper code)

def NamedRefers (s : State) (capture : Nat → Capture) (code : Nat × Expr) (out : Output) : Prop :=
  code.1 = out.name ∧ Derives s (.variable out.target) (logical capture .actual code.2)

/-- The logical names used by the where call already exist in the normal
state. No address is allocated and no effect is appended to that state. -/
structure Existing (s : State) (r : Registry) (interp : Interpretation) (capture : Nat → Capture)
    (clause : Clause) (request : Demand) : Prop where
  sameRole : request.role = clause.role
  positions : ∃ args out, SourceCodes r interp clause args out ∧
    All₂ (Refers s capture) args request.arguments ∧ All₂ (NamedRefers s capture) out request.outputs

theorem arg_result {s : State}
    (compiled : translate c interp (normalize pat) = some e) (known : Refers s capture e arg) :
    Result s (whereFacts c interp capture arg pat) := by
  simp only [Result,whereFacts,compiled,Option.map_some]
  refine ⟨_,rfl,?_⟩
  intro row h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> subst row
  · exact entails known.1
  · exact entails known.2.1
  · exact entails known.2.2

theorem out_result {s : State}
    (name : code.1 = src.name) (compiled : translate c interp src.rhs = some code.2)
    (known : NamedRefers s capture code out) :
    Result s (childFact c interp capture src out) := by
  have e := known.1.symm.trans name
  refine ⟨[⟨out.target,logical capture .actual code.2⟩],by simp [childFact,e,compiled],?_⟩
  intro row h
  cases List.mem_singleton.mp h
  exact entails known.2

theorem input_results {s : State} {capture : Nat → Capture}
    (compiled : All₂ (fun pat code => translate c interp (normalize pat) = some code) ps es)
    (read : All₂ (Refers s capture) es args) :
    All₂ (fun arg pat => Result s (whereFacts c interp capture arg pat)) args ps := by
  induction compiled generalizing args with
  | nil => cases read; exact .nil
  | cons hd tl ih =>
    cases read with
    | cons first last =>
      exact .cons (arg_result hd first) (ih last)

theorem output_results {s : State} {capture : Nat → Capture}
    (compiled : All₂ (fun e p => p.1 = e.name ∧ translate c interp e.rhs = some p.2) eqs outs)
    (read : All₂ (NamedRefers s capture) outs names) :
    All₂ (fun eqn req => Result s (childFact c interp capture eqn req)) eqs names := by
  induction compiled generalizing names with
  | nil => cases read; exact .nil
  | cons hd tl ih =>
    cases read with
    | cons first last =>
      exact .cons (out_result hd.1 hd.2 first) (ih last)

theorem existing_result {s : State} (read : Existing s r interp capture clause child) :
    Result s (clauseFacts r interp capture clause child) := by
  obtain ⟨args,out,source,readArgs,readOut⟩ := read.positions
  obtain ⟨a,ha,ea⟩ := zip_result (f := whereFacts r.constructors interp capture)
    (input_results source.arguments readArgs)
  obtain ⟨b,hb,eb⟩ := zip_result (f := childFact r.constructors interp capture)
    (output_results source.outputs readOut)
  refine ⟨a ++ b,by simp [clauseFacts,read.sameRole,ha,hb],?_⟩
  intro row atBoth
  exact (List.mem_append.mp atBoth).elim (ea row) (eb row)

end Yulang.GeneralDeclarativeExistingClause322
