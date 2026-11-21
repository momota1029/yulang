import Yulang.GeneralDeclarativeExistingClause322
import Yulang.GeneralDeclarativeHeadCases321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExistingReturn322
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeOutputs320 (bodyCapture bodyPattern compile_exact)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDictionaryAssociatedProvenance (Supplies lookup_exact)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized translate_value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (normalize)
open GeneralSourceState (Output)
open GeneralDeclarations (Declaration Registry Checked)

/-- The body can be explicit or a role default. Checking its existing
ordinary equation does not assert either dictionary success or that the
output was a lawful source of input-head readiness. -/
def Settled (s : State) (r : Registry) (interp : Interpretation) (impl : Declaration)
    (d : Demand) (capture : Nat → Capture) (out : Output) : Prop :=
  ∃ body raw norm, Supplies r.roles impl out.name body ∧
    translate r.constructors interp (bodyPattern body) = some raw ∧
    translate r.constructors interp (normalize (bodyPattern body)) = some norm ∧
    Derives s (.variable out.target) (logical (bodyCapture d capture body) .actual norm)

theorem settled_result {s : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (settled : Settled s r interp impl d capture out) :
    Result s (rootFact r interp impl d capture out) := by
  obtain ⟨body,raw,norm,source,rawCode,normCode,holds⟩ := settled
  have unique := (checked.2 impl visible).identified.2.2.1
  have found := (lookup_exact r.roles impl unique _ body).mpr source
  have code := (compile_exact r.constructors interp body).symm.trans rawCode
  refine ⟨[⟨out.target,logical (bodyCapture d capture body) .actual raw⟩],
    by simp [rootFact,found,code],?_⟩
  intro row member m valid
  cases List.mem_singleton.mp member
  simp only [Holds,logical_value]
  have derived := entails holds m valid
  simp only [Holds,logical_value] at derived
  rw [translate_value (normalize (bodyPattern body)) normCode] at derived
  exact eqv_trans derived (eqv_symm (compiled_normalized
    (variables := variables (bodyCapture d capture body) m) rawCode))

end Yulang.GeneralDeclarativeExistingReturn322
