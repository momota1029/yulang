import Yulang.GeneralDeclarativeOrdinaryReads321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereProducer321
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrdinaryReads321 (Reads entails_read)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeCompileLists321 (Result zip_result)
open GeneralDeclarativeArgumentFacts320 (whereFacts)
open GeneralDeclarativeOutputFacts320 (childFact)
open GeneralDeclarativeNodeFacts320 (clauseFacts)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralDeclarations (Clause Registry)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralSourceState (Output)
open CommonRoleOutermostResolver (All₂)

def Operand (s : State) (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (arg : Capture) (p : Pattern) : Prop :=
  ∃ code, translate c interp (normalize p) = some code ∧
    Reads s capture .lower arg.lower code ∧ Reads s capture .actual arg.center code ∧
    Reads s capture .upper arg.upper code

theorem operand_result {s : State} (read : Operand s c interp capture arg p) :
    Result s (whereFacts c interp capture arg p) := by
  obtain ⟨code,translated,lo,center,hi⟩ := read
  simp only [Result,whereFacts,translated,Option.map_some]
  refine ⟨_,rfl,?_⟩
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h <;> subst row
  · exact entails_read lo
  · exact entails_read center
  · exact entails_read hi

def ChildName (s : State) (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (eqn : GeneralDeclarations.Equation) (out : Output) : Prop :=
  out.name = eqn.name ∧ ∃ code, translate c interp eqn.rhs = some code ∧
    Reads s capture .actual out.target code

theorem child_name_result (read : ChildName s c interp capture eqn out) :
    Result s (childFact c interp capture eqn out) := by
  obtain ⟨named,code,translated,found⟩ := read
  refine ⟨[⟨out.target,logical capture .actual code⟩],by simp [childFact,named,translated],?_⟩
  intro row member
  cases List.mem_singleton.mp member
  exact entails_read found

/-- The actual declaration child determines the position and named target;
an ordinary read may use a projected equality or a syntactic constructor. -/
structure Child (s : State) (r : Registry) (interp : Interpretation) (capture : Nat → Capture)
    (clause : Clause) (child : Demand) : Prop where
  role : child.role = clause.role
  arguments : All₂ (Operand s r.constructors interp capture) child.arguments clause.arguments
  outputs : All₂ (ChildName s r.constructors interp capture) clause.outputs child.outputs

theorem child_result (read : Child s r interp capture clause child) :
    Result s (clauseFacts r interp capture clause child) := by
  obtain ⟨a,ca,ea⟩ := zip_result (f := whereFacts r.constructors interp capture)
    (GeneralDeclarativeNormalized320.ordered_map read.arguments (fun _ _ _ _ h => operand_result h))
  obtain ⟨o,co,eo⟩ := zip_result (f := childFact r.constructors interp capture)
    (GeneralDeclarativeNormalized320.ordered_map read.outputs (fun _ _ _ _ h => child_name_result h))
  refine ⟨a ++ o,by simp [clauseFacts,read.role,ca,co],?_⟩
  intro row used
  exact (List.mem_append.mp used).elim (ea row) (eo row)

end Yulang.GeneralDeclarativeWhereProducer321
