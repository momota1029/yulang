import Yulang.GeneralDeclarativeStableRigid323
import Yulang.GeneralDeclarativeRigidProbe323
import Yulang.GeneralDeclarativeTraceCapture323
import Yulang.GeneralDeclarativeProducerFixture322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRepeatedSource323
open GeneralDeclarationExamples (constructors roles bareRole binaryRole outputRole)
open GeneralDeclarations (Clause Declaration DeclarationChecked Registry Checked)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs substArgs counted encodeArgs)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Ready knows_row alias_refl Alias)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeExampleSource320 (interp point int)
open GeneralDeclarativeProducerFixture322 (nominal_use)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (nominal subtype_refl)

abbrev pat : Pattern := .app 0 [.var 0]
abbrev whereClause : Clause := ⟨90,0,[.var 0],[]⟩
abbrev parent : Declaration := ⟨91,4,[pat,pat],[whereClause],[],[]⟩
abbrev child : Declaration := ⟨92,0,[.var 0],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[parent,child]⟩

theorem parent_checked : DeclarationChecked constructors roles parent := by
  constructor
  · refine ⟨rfl,by simp,?_,?_⟩
    · intro name body unknown; cases unknown
    · intro clause inWhere
      cases List.mem_singleton.mp inWhere
      exact ⟨rfl,by simp⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,GeneralDeclarationPatterns.ArgsWellScoped,GeneralDeclarationPatterns.WellScoped]
  · intro clause there
    cases List.mem_singleton.mp there
    exact ⟨rfl,rfl⟩
  · intro clause there
    cases List.mem_singleton.mp there
    exact (GeneralDeclarationPatterns.checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause there
    cases List.mem_singleton.mp there
    unfold GeneralDeclarationPatterns.ConservativeSmaller
    decide +kernel
  · intro clause there
    cases List.mem_singleton.mp there
    intro assign
    constructor
    · simp [substArgs,Pattern.subst,normalizeArgs,normalize,counted,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
      omega
    · intro name
      simp [substArgs,Pattern.subst,normalizeArgs,normalize,counted,encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences]

theorem child_checked : DeclarationChecked constructors roles child := by
  constructor
  · refine ⟨rfl,by simp,?_,by simp⟩
    intro name body nowhere; cases nowhere
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,GeneralDeclarationPatterns.ArgsWellScoped,GeneralDeclarationPatterns.WellScoped]
  all_goals intro clause present; cases present

theorem checked : Checked registry := by
  constructor
  · decide +kernel
  · intro chosen present
    rcases List.mem_cons.mp present with rfl|later
    · exact parent_checked
    · cases List.mem_singleton.mp later
      exact child_checked

theorem well_covered : Coverage registry interp := by
  refine ⟨?_,GeneralDeclarativeProducerFixture322.metadata.2⟩
  intro d found
  rcases List.mem_cons.mp found with rfl|later
  · refine ⟨⟨⟨nominal_use,⟨trivial,trivial⟩⟩,⟨⟨nominal_use,⟨trivial,trivial⟩⟩,trivial⟩⟩,?_,by simp⟩
    intro clause occurs
    cases List.mem_singleton.mp occurs
    exact ⟨⟨trivial,trivial⟩,by simp⟩
  · cases List.mem_singleton.mp later
    exact ⟨⟨trivial,trivial⟩,by simp,by simp⟩

abbrev a : Capture := ⟨0,1,2⟩
abbrev b : Capture := ⟨10,11,12⟩
abbrev goal : Demand := ⟨4,[a,b],[]⟩
abbrev emitted : Demand := ⟨0,[point 3],[]⟩
abbrev nominalCode (n : Nat) : Expr := .nominal 0 [.variable n]
abbrev scalar : Expr := .primitive (.scalar .int) []
abbrev eqs : List Equation :=
  [⟨0,nominalCode 3⟩,⟨2,nominalCode 4⟩,⟨10,nominalCode 7⟩,⟨12,nominalCode 8⟩,
   ⟨3,scalar⟩,⟨4,.variable 3⟩,⟨7,.variable 3⟩,⟨8,.variable 3⟩]
def state : State := ⟨⟨[],[(0,1),(1,2),(10,11),(11,12)]⟩,eqs⟩

def support : Supported state (fun _ => False) :=
  ⟨fun eq origin => eq ∈ eqs ∧ origin = .source,fun h => h.1⟩

theorem row {e : Equation} (source : e ∈ eqs) : e ∈ (restriction support).equations :=
  from_source support ⟨source,rfl⟩

abbrev model : Assignment := fun n =>
  (if n ≤ 2 ∨ (10 ≤ n ∧ n ≤ 12) then nominal 0 [.inl int] else int,Common.rowEmpty)

theorem fits : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro span used
    change span ∈ [(0,1),(1,2),(10,11),(11,12)] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl|rfl <;> exact subtype_refl _
  · intro item used
    change item ∈ eqs at used
    simp only [eqs,List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

end Yulang.GeneralDeclarativeRepeatedSource323
