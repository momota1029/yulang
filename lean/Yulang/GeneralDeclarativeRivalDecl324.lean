import Yulang.GeneralDeclarativeNominalClash324
import Yulang.GeneralDeclarativeAggregateResolve324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRivalDecl324
open GeneralDeclarations (Declaration Registry Checked DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeRepeatedSource323 (registry parent child pat goal parent_checked child_checked)
open GeneralDeclarativeAggregateFixture324 (newState inhabited support old_rows supported_row)
open GeneralDeclarativeExampleSource320 (interp)
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeOrigins321 (restriction restrict_models)
open GeneralDeclarativeNominalClash324 (Clash AtHead eliminates)
open GeneralNominalInspection (Interpretation)

def richer : Interpretation :=
  ⟨fun _ => none,fun k => k == 0 || k == 1,fun _ _ => rfl⟩

abbrev other : Pattern := .app 1 [.var 0]
abbrev rival : Declaration := ⟨93,4,[other,pat],[],[],[]⟩
abbrev wider : Registry := ⟨registry.constructors,registry.roles,[parent,rival,child]⟩

theorem rival_checked : DeclarationChecked wider.constructors wider.roles rival := by
  constructor
  · refine ⟨rfl,by simp,?_,by simp⟩
    intro name body never; cases never
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  all_goals intro clause present; cases present

theorem wider_checked : Checked wider := by
  refine ⟨by decide +kernel,?_⟩
  intro impl found
  rcases List.mem_cons.mp found with rfl|more
  · exact parent_checked
  · rcases List.mem_cons.mp more with rfl|tail
    · exact rival_checked
    · cases List.mem_singleton.mp tail
      exact child_checked

theorem real_conflict (done : Nat → Prop) :
    AtHead (restriction (support done)) wider.constructors richer goal rival := by
  refine ⟨0,_,other,rfl,rfl,0,1,[.variable 3],[.variable 0],?_,rfl,by decide +kernel⟩
  exact .row (supported_row done (old_rows (by simp [GeneralDeclarativeRepeatedSource323.eqs])))

theorem not_viable (done : Nat → Prop) :
    ¬GeneralDeclarativeEndpointProbe321.HeadMatches (restriction (support done))
      wider.constructors richer goal rival := by
  obtain ⟨m,valid⟩ := inhabited
  exact eliminates (restrict_models (support done) m valid) (real_conflict done)

end Yulang.GeneralDeclarativeRivalDecl324
