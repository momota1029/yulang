import Yulang.GeneralNominalTraceDictionary197
import Yulang.GeneralNominalExecutableView196
import Yulang.GeneralNominalSpineFacts

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalTraceRefreshExample197
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalInspectionTrace197 GeneralNominalTraceDictionary197
open GeneralNominalViewTransport196
open GeneralNominalRefreshFork (state context descriptor)
open GeneralNominalExecutableView196 (next start finish certificate)
open GeneralDeclarationExamples (roles constructors)

abbrev declaration : Declaration := ⟨970,0,[.app 0 [.app 0 [.var 0]]],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev focus : Occurrence roles := ⟨197,⟨0,fun _ => (1,1),[],by intro _ h; cases h⟩⟩
abbrev tree : Dictionary roles := .node focus 970 []
abbrev payload : GeneralDictionaryReadback.Payload := .node 970 []
abbrev query : GeneralNominalInspection.Query := .nominal 0 [.nominal 0 [.variables [0]]]

theorem computed_query : GeneralNominalInspection.queries (state none)
    (context none).interpretation declaration = [query] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate]

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped]
  · simp [Declaration.ConstructorScoped,GeneralDeclarationPatterns.ArgsWellScoped,
      GeneralDeclarationPatterns.WellScoped,constructors]
  all_goals intro clause member; cases member

theorem nominal_trace (wide : Bool) : Trace (state none) (next wide) query (1,1) := by
  change Trace (state none) (next wide) (.nominal 0 [.nominal 0 [.variables [0]]]) ((1 : Fin 5),1)
  apply Trace.nominalPoint (state := state none) (next := next wide) (slot := (1 : Fin 5)) (descriptor := descriptor (2,2)) (actuals := [(2,2)]) rfl
    (by cases wide <;> rfl) rfl rfl
  apply Traces.cons
  · apply Trace.nominalPoint (state := state none) (next := next wide) (slot := (2 : Fin 5)) (descriptor := descriptor (3,3)) (actuals := [(3,3)]) rfl
      (by cases wide <;> rfl) rfl rfl
    exact .cons .variables .nil
  · exact .nil

theorem lookup : GeneralNominalRecursiveCandidates.arguments (context none) focus = some [(1,1)] := by
  decide +kernel

theorem traced (wide : Bool) : TreeTrace registry (context none) (next wide) tree := by
  apply TreeTrace.node
  · intro decl member _ bounds located
    have same := List.mem_singleton.mp member
    subst decl
    have same := Option.some.inj (lookup.symm.trans located)
    subst bounds
    rw [computed_query]
    exact .cons (nominal_trace wide) .nil
  · intro child member; cases member

theorem actual_step (wide : Bool) :
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Step registry
      GeneralNominalRefreshFork.root start (finish wide) :=
  GeneralNominalExecutableView196.actual_step registry wide

theorem changed_outside_trace (wide : Bool) :
    (state none).nominals 0 ≠ (replace (state none) (next wide)).nominals ⟨0,by change 0 < 5; decide⟩ := by
  cases wide <;> intro h <;> cases h

theorem preserved_report (wide : Bool) :
    Rechecked (context none) (next wide) declaration [(1,1)] := by
  apply rechecked_of_trace
  rw [computed_query]
  exact .cons (nominal_trace wide) .nil

/-- Two real nominal constructors, not a variable-only query. -/
theorem not_variable_only : ¬ ∃ names : List (List Nat),
    GeneralNominalInspection.queries (state none) (context none).interpretation declaration =
      names.map GeneralNominalInspection.Query.variables := by
  rw [computed_query]
  rintro ⟨names,equal⟩
  cases names with
  | nil => cases equal
  | cons first rest => cases equal
end Yulang.GeneralNominalTraceRefreshExample197
