import Yulang.GeneralDeclarativeEmissionOperands322
import Yulang.GeneralDeclarativeEmissionOutputs322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEmissionClause322
open GeneralDeclarativeSourceEmission322 (Names useArg inputs useOutput demand)
open GeneralDeclarativeEmissionOperands322 (Compound ordered_inputs)
open GeneralDeclarativeEmissionOutputs322 (Direct Agree ordered_outputs)
open GeneralDeclarativeExistingClause322 (Refers input_results)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeCompileLists321 (Result zip_result)
open GeneralDeclarativeArgumentFacts320 (whereFacts)
open GeneralDeclarativeOutputFacts320 (childFact)
open GeneralDeclarativeNodeFacts320 (clauseFacts)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarations (Declaration Clause Registry)
open CommonRoleOutermostResolver (All₂)

/-- Source table for named compound operands only. Direct uses of input and
output binders do not need ordinary lookup certificates. -/
structure Ready (s : State) (r : Registry) (interp : Interpretation) (decl : Declaration)
    (clause : Clause) (names : Names) (compound : Nat → Capture) (targets : Nat → Nat) : Prop where
  args : ∃ codes : List Expr,
    All₂ (fun p e => translate r.constructors interp (normalize p) = some e) clause.arguments codes ∧
    (∀ (i : Nat) p e, clause.arguments[i]? = some p → codes[i]? = some e →
      Compound p → Refers s names.input e (compound i))
  outputs : ∀ eqn ∈ clause.outputs, ∃ raw norm,
    translate r.constructors interp eqn.rhs = some raw ∧
    translate r.constructors interp (normalize eqn.rhs) = some norm ∧
    (¬Direct decl eqn → Derives s (.variable (useOutput decl names targets eqn).target)
      (logical names.input .actual norm))

theorem clause_ordinary {s : State}
    (agrees : Agree decl names) (coverage : Ready s r interp decl clause names compound targets) :
    Result s (clauseFacts r interp names.input clause (demand decl clause names compound targets)) := by
  obtain ⟨codes,order,comp⟩ := coverage.args
  have asks := ordered_inputs (s := s) order 0 compound
    (by intro i pat code pos shape nonVar; simpa only [Nat.zero_add] using comp i pat code pos shape nonVar)
  obtain ⟨a,ha,ea⟩ := zip_result (f := whereFacts r.constructors interp names.input)
    (input_results order asks)
  obtain ⟨b,hb,eb⟩ := zip_result (f := childFact r.constructors interp names.input)
    (ordered_outputs agrees coverage.outputs)
  refine ⟨a ++ b,by simp [clauseFacts,demand,ha,hb],?_⟩
  intro row used
  exact (List.mem_append.mp used).elim (ea row) (eb row)

end Yulang.GeneralDeclarativeEmissionClause322
