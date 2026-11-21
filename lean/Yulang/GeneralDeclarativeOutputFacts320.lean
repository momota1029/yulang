import Yulang.GeneralDeclarativeArgumentFacts320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13500
set_option maxHeartbeats 3600000
namespace Yulang.GeneralDeclarativeOutputFacts320
open GeneralDeclarations (Declaration Registry)
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand sourceValue)
open GeneralDeclarativeAssembly320 (Named)
open GeneralDeclarativeSubstitution320 (logical EquationRead equation_read)
open GeneralDeclarativeOutputs320 (ChildOutputMeaning bodyCapture compile)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDictionaryAssociatedProvenance (lookup)
open GeneralSourceState (Output)
open GeneralDeclarativeBatch320 (zipFacts zip_sound collect collect_sound)
open GeneralDeclarativeNormalized320 (ordered_map)
open CommonRoleOutermostResolver (All₂)

def childFact (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (equation : GeneralDeclarations.Equation) (request : Output) :
    Option (List GeneralDeclarativeHead320.Equation) :=
  if request.name = equation.name then
    (translate c interp equation.rhs).map fun e => [⟨request.target,logical capture .actual e⟩]
  else none

def rootFact (r : Registry) (interp : Interpretation) (decl : Declaration) (d : Demand)
    (capture : Nat → Capture) (request : Output) : Option (List GeneralDeclarativeHead320.Equation) := do
  let body ← lookup r.roles decl request.name
  let e ← compile r.constructors interp body
  pure [⟨request.target,logical (bodyCapture d capture body) .actual e⟩]

theorem child_fact {s c interp capture eq out facts}
    (generated : childFact c interp capture eq out = some facts)
    (settled : facts ⊆ s.equations) (m : Assignment) (valid : Models s m) :
    ChildOutputMeaning c interp capture m eq out := by
  by_cases same : out.name = eq.name
  · cases translated : translate c interp eq.rhs with
    | none => simp [childFact,same,translated] at generated
    | some e =>
      have batch : [⟨out.target,logical capture .actual e⟩] = facts := by
        simpa [childFact,same,translated] using generated
      subst facts
      have read : EquationRead s capture .actual out.target e := .whole (settled List.mem_cons_self)
      exact ⟨same,eqv_trans (equation_read read m valid) (compiled_normalized translated)⟩
  · simp [childFact,same] at generated

theorem root_fact {s r interp decl d capture out facts}
    (generated : rootFact r interp decl d capture out = some facts)
    (settled : facts ⊆ s.equations) : Named s r interp d decl capture out := by
  cases chosen : lookup r.roles decl out.name with
  | none => simp [rootFact,chosen] at generated
  | some body =>
    cases translated : compile r.constructors interp body with
    | none => simp [rootFact,chosen,translated] at generated
    | some e =>
      have batch : [⟨out.target,logical (bodyCapture d capture body) .actual e⟩] = facts := by
        simpa [rootFact,chosen,translated] using generated
      subst facts
      exact ⟨body,e,chosen,translated,.whole (settled List.mem_cons_self)⟩

theorem compiled_child_outputs {s c interp capture eqs outs facts}
    (generated : zipFacts (childFact c interp capture) eqs outs = some facts)
    (settled : facts ⊆ s.equations) (m : Assignment) (valid : Models s m) :
    All₂ (ChildOutputMeaning c interp capture m) eqs outs := by
  apply ordered_map (zip_sound generated)
  rintro _ _ _ _ ⟨batch,comp,sub⟩
  exact child_fact comp (fun _ used => settled (sub used)) m valid

theorem compiled_root_outputs {s r interp decl d capture facts}
    (generated : collect (rootFact r interp decl d capture) d.outputs = some facts)
    (settled : facts ⊆ s.equations) :
    ∀ out ∈ d.outputs, Named s r interp d decl capture out := by
  intro out member
  obtain ⟨batch,comp,sub⟩ := collect_sound generated out member
  exact root_fact comp (fun _ used => settled (sub used))

end Yulang.GeneralDeclarativeOutputFacts320
