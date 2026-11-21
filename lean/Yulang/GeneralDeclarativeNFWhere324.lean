import Yulang.GeneralDeclarativeNFNode324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNFWhere324
open GeneralDeclarations (Clause Declaration Registry)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (Holds Entails literal)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeDemand320 (Demand sourceValue Bounds)
open GeneralDeclarativeOutputs320 (ChildOutputMeaning)
open GeneralDeclarativeArgumentFacts320 (whereFacts compiled_where)
open GeneralDeclarativeAssembly320 (ChildDenotes)
open GeneralDeclarativeNormalized320 (normalized_where_clause ordered_map)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeBatch320 (zipFacts zip_sound)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (translate_value)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationPatterns (Constructors normalize)
open GeneralSourceState (Output)
open CommonRoleOutermostResolver (All₂)

/-- A named where operand keeps its fixed target and source association
name, but reads only the normalized RHS, not erased source constructors. -/
def namedFact (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (eqn : GeneralDeclarations.Equation) (request : Output) : Option (List Equation) :=
  if request.name = eqn.name then
    (translate c interp (normalize eqn.rhs)).map fun nf =>
      [⟨request.target,logical capture .actual nf⟩]
  else none

theorem named_sound {s : State} (recipe : Result s (namedFact c interp capture eqn out))
    (m : Assignment) (valid : Models s m) :
    ChildOutputMeaning c interp capture m eqn out := by
  obtain ⟨rows,built,truth⟩ := recipe
  by_cases same : out.name = eqn.name
  · cases printed : translate c interp (normalize eqn.rhs) with
    | none => simp [namedFact,same,printed] at built
    | some nf =>
      have sameRows : [⟨out.target,logical capture .actual nf⟩] = rows := by
        simpa [namedFact,same,printed] using built
      subst rows
      have value := truth _ List.mem_cons_self m valid
      simp only [Holds,logical_value,translate_value (normalize eqn.rhs) printed] at value
      exact ⟨same,value⟩
  · simp [namedFact,same] at built

def clauseFacts (r : Registry) (interp : Interpretation) (capture : Nat → Capture)
    (clause : Clause) (d : Demand) : Option (List Equation) :=
  if d.role = clause.role then do
    let as ← zipFacts (whereFacts r.constructors interp capture) d.arguments clause.arguments
    let ns ← zipFacts (namedFact r.constructors interp capture) clause.outputs d.outputs
    pure (as ++ ns)
  else none

theorem clause_sound {s : State}
    (checked : GeneralDeclarations.DeclarationChecked r.constructors r.roles impl)
    (listed : clause ∈ impl.requirements) (span : ∀ n ∈ impl.inputNames, Bounds s (capture n))
    (printed : clauseFacts r interp capture clause child = some rows)
    (literalRows : rows ⊆ s.equations) (m : Assignment) (valid : Models s m) :
    ChildDenotes r.constructors interp capture m clause child := by
  by_cases role : child.role = clause.role
  · cases args : zipFacts (whereFacts r.constructors interp capture) child.arguments clause.arguments with
    | none => simp [clauseFacts,role,args] at printed
    | some aa =>
      cases outs : zipFacts (namedFact r.constructors interp capture) clause.outputs child.outputs with
      | none => simp [clauseFacts,role,args,outs] at printed
      | some oo =>
        have exactRows : aa ++ oo = rows := by simpa [clauseFacts,role,args,outs] using printed
        subst rows
        refine ⟨role, normalized_where_clause checked listed span
          (compiled_where args (fun _ used => literalRows (List.mem_append_left _ used))) m valid,?_⟩
        apply ordered_map (zip_sound outs)
        rintro _ _ _ _ ⟨block,emitted,contained⟩
        exact named_sound ⟨block,emitted,fun row used => literal
          (literalRows (List.mem_append_right _ (contained used)))⟩ m valid
  · simp [clauseFacts,role] at printed

theorem clauses_sound {s : State}
    (checked : GeneralDeclarations.DeclarationChecked r.constructors r.roles impl)
    (span : ∀ n ∈ impl.inputNames, Bounds s (capture n))
    (printed : zipFacts (clauseFacts r interp capture) impl.requirements children = some rows)
    (literalRows : rows ⊆ s.equations) (m : Assignment) (valid : Models s m) :
    All₂ (ChildDenotes r.constructors interp capture m) impl.requirements children := by
  apply ordered_map (zip_sound printed)
  rintro clause listed child _ ⟨block,emitted,contains⟩
  exact clause_sound checked listed span emitted (fun _ used => literalRows (contains used)) m valid

end Yulang.GeneralDeclarativeNFWhere324
