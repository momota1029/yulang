import Yulang.GeneralDeclarativeI65I74StructuralWhereMixedPosition428

set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereMixedSibling428
open GeneralDeclarativeI65 StructuralWhere427 StructuralWhere428
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarations (Declaration Clause DeclarationChecked)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeHead320 (Equation)
open CommonRoleOutermostResolver (Dictionary Tree Summarizes)
open CommonNominalFullCarrier (Ty record nominal subtype_refl)
open Checker408 (Problem)

def sourceBodies : Source 3 0 0 :=
  ⟨[⟨90,[]⟩],
    fun i => if i.val = 0 then .union (.variant 3 (.inl 1)) (.variant 4 (.inl 2))
      else if i.val = 1 then .nominal 90 [] else .base .unit,
    fun i => i.elim0⟩

def first : Clause := ⟨50,20,[writtenRecord427 30 8 9],[]⟩
def second : Clause := ⟨6,21,[.var 8],[]⟩
def parentDecl : Declaration :=
  ⟨218,19,[RecordK2412.closedHead412 30 31 9 8],[first,second],[],[]⟩
def structuralDecl : Declaration := ⟨219,20,[writtenRecord427 30 14 9],[],[],[]⟩
def legacyDecl : Declaration := ⟨88,21,[.app 90 []],[],[],[]⟩
def rowsSource : InputBundle :=
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
    ⟨90,some ⟨[],90⟩,.unclassified⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩,⟨20,1,[]⟩,⟨21,1,[]⟩]⟩,
    [parentDecl,structuralDecl,legacyDecl]⟩

def rootReadRow : Equation := ⟨0,.record 30 (.variable 1) (.variable 2)⟩
def innerReadRow : Equation := ⟨1,.record 31 (.variable 3) (.variable 2)⟩
def emptyRow : Equation := ⟨2,.primitive .emptyRecord []⟩
def authoredNominalRow : Equation := ⟨3,.nominal 90 []⟩
def structuralRetained : Equation := RecordK2412.recordRow412 4 30 3
def graphRoot : Equation := RecordK2412.recordRow412 0 30 1
def graphInner : Equation := RecordK2412.recordRow412 1 31 3
def rows : List Equation := [rootReadRow,innerReadRow,emptyRow,authoredNominalRow,
  structuralRetained,graphRoot,graphInner]
def rootAuth : Origin := ⟨0,[32],RecordK2412.recordInput412 30 1⟩
def namedAuth : Origin := ⟨3,[42],.nominal 90 []⟩
def make : Option Problem := do
  let graph ← compile sourceBodies
  let src ← GeneralSourceMetadataBareBundle291.compile rowsSource
  let env : Environment := ⟨3,0,0,sourceBodies,graph,src⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨env,⟨⟨[],[]⟩,rows⟩,[]⟩,List.replicate 91 [],[rootAuth,namedAuth],[]⟩
  let a : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,a⟩,⟨[71],⟨19,[point 0],[]⟩⟩⟩
def mixedProblem : Problem := make.get (by decide +kernel)

def rootEsc : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[0,1,2,1,2]⟩
def insideEsc : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,0,2,1,2]⟩
def noFieldEsc : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,2,0,2,2]⟩
def capturedEsc : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,2,2,0,2]⟩
def placedEsc : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,2,2,1,0]⟩
def rootInput : PositiveHeadWire427 :=
  ⟨0,0,2,rootEsc,insideEsc,noFieldEsc,.nested 1 2 capturedEsc noFieldEsc⟩
def rootPick : ReadPositiveHead427 mixedProblem.state.core mixedProblem.root :=
  (readPositiveHead427 mixedProblem.state.core mixedProblem.root rootInput).get (by decide +kernel)
def originalPlace : Placement :=
  ⟨fun c _ => if c.id = first.id then point 4 else point 0,fun _ _ => 0⟩
def frame : AuthoredBodyFrame393 mixedProblem.state.core mixedProblem.root :=
  ⟨rootPick.ordinal,rootPick.decl,rootPick.fromRegistry,rootPick.visibleDecl,originalPlace,rootPick.capture⟩
def actualRecord : OriginalRecordArgument427 frame 0 0 :=
  (readOriginalRecordArgument427 frame ⟨0,0,4⟩).get (by decide +kernel)
def actualVariable : LiteralVariableArgumentAt428 frame 1 :=
  ⟨second,by decide +kernel,8,rfl,rfl⟩
def selectedStruct : ReadClosedChild427 actualRecord mixedProblem.state.b6 :=
  (readModeClosedChild428 actualRecord mixedProblem.state.b6 ⟨1,placedEsc⟩).get (by decide +kernel)

def actualLegacy : Problem := ⟨mixedProblem.state,actualVariable.child⟩
def oldWire : Named409.NamedWire := ⟨1,[2,1,0,0,1]⟩
theorem singleton_legacy : visible actualLegacy.state.core actualLegacy.root = [legacyDecl] := by decide +kernel
def oldRead : Named409.VerifiedName actualLegacy legacyDecl :=
  (Named409.replayNamedHead actualLegacy legacyDecl singleton_legacy oldWire).get (by decide +kernel)

def showType (n : Nat) : Ty :=
  if n = 0 then record 30 (record 31 (nominal 90 []) .emptyRecord) .emptyRecord
  else if n = 1 then record 31 (nominal 90 []) .emptyRecord
  else if n = 2 then .emptyRecord
  else if n = 4 then record 30 (nominal 90 []) .emptyRecord else nominal 90 []
def fitModel : I72.Model :=
  ⟨fun n => (showType n,Common.rowEmpty),fun _ => none,
    fun n => if n = 0 then some (RecordK2412.recordInput412 30 1)
      else if n = 3 then some (.nominal 90 []) else none⟩

theorem genuine_mixed_problem_has_one_model428 : I72.Fits mixedProblem.state fitModel := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ e; cases e
  · intro _ e; cases e
  · intro item atRow
    change item ∈ rows at atRow
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at atRow
    rcases atRow with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ e; cases e
  · intro item stated
    change item ∈ [rootAuth,namedAuth] at stated
    simp only [List.mem_cons,List.not_mem_nil,or_false] at stated
    rcases stated with rfl|rfl <;> rfl

theorem original_structural_and_variable_children_are_not_the_same428 :
    actualRecord.child.occurrence = [71,0] ∧ actualVariable.child.occurrence = [71,1] ∧
      actualRecord.name = 4 ∧ (frame.names.input actualVariable.binder).center = 3 ∧
      oldRead.known.origin.slot = 3 ∧ oldRead.known.origin.endpoint = .nominal 90 [] := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals try (decide +kernel)
  have key : oldRead.known.key = 90 := by decide +kernel
  exact oldRead.known.endpoint.trans
    (congrArg (fun k => CommonRecursiveNominalIntervals.Endpoint.nominal k []) key)

theorem existing_actual_named_leaf_checker_runs_on_the_literal_sibling428 :
    Named409.check actualLegacy (Check408.nullaryReport legacyDecl) (.bareName oldWire) = true := by
  decide +kernel

def throughCurrentPreR14 : RepeatedCenters421.Witness :=
  .previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.bareName oldWire))))))))))))

theorem existing_current_dispatch_uses_the_actual_legacy_named_sibling428 :
    RepeatedCenters421.check actualLegacy (Check408.nullaryReport legacyDecl) throughCurrentPreR14 = true :=
  by decide +kernel

theorem named_leaf_checker_does_not_relabel_actual_structural_child428 :
    Named409.check ⟨mixedProblem.state,actualRecord.child⟩
      (Check408.nullaryReport structuralDecl) (.bareName oldWire) = false ∧
    (readModeClosedChild428 actualRecord mixedProblem.state.b6 ⟨2,placedEsc⟩).isNone = true := by
  decide +kernel

open GeneralDeclarationPatterns (CountsCovered Smaller ConservativeSmaller StableSmaller
  counted substArgs normalizeArgs normalize encodeArgs Pattern checkSmaller_exact)

private theorem nested_var_stable428 (box tick empty binder : Nat) :
    StableSmaller [RecordK2412.closedHead412 box tick empty binder] [.var binder] := by
  intro capture
  constructor
  · simp [RecordK2412.closedHead412,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
      encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size] <;> omega
  · intro q
    simp [RecordK2412.closedHead412,counted,substArgs,Pattern.subst,normalizeArgs,normalize,
      encodeArgs,Pattern.encode,Roles.argsOccurrences,Roles.Term.occurrences] <;> omega

private theorem checked_ordinary_descent428 {a b : List Pattern}
    (read : RecordK2412.recordDescent412 a b = true) (stable : StableSmaller a b) :
    CountsCovered a b ∧ Smaller a b ∧ ConservativeSmaller a b ∧ StableSmaller a b := by
  open GeneralDeclarativeWitnessProblem349 in
  exact ⟨splitAnd (splitAnd (splitAnd read).1).1,
    (checkSmaller_exact ..).mp (splitAnd (splitAnd read).1).2,(splitAnd read).2,stable⟩

theorem checked_parent_syntax428 : DeclarationChecked
    (authoredRegistry mixedProblem.state.core.current).constructors
    (authoredRegistry mixedProblem.state.core.current).roles frame.decl := by
  let current := mixedProblem.state.core.current
  let env := current.environment
  have roles : GeneralSourceMetadataRoles291.Valid env.source.roles :=
    (GeneralSourceMetadataRoles291.check_exact _).mp (by decide +kernel)
  have cover := (GeneralDeclarativeWitnessModeCoverage357.check_exact roles).mp (by decide +kernel)
  have included : parentDecl ∈ env.source.declarations := by decide +kernel
  have header : RecordK2412.header412 current parentDecl = true := by decide +kernel
  have actual : frame.decl = parentDecl := by decide +kernel
  rw [actual]
  unfold RecordK2412.header412 at header
  open GeneralDeclarativeWitnessProblem349 in
  open GeneralDeclarativeWitnessChecks349 in
  obtain ⟨top,tail⟩ := splitAnd header
  open GeneralDeclarativeWitnessProblem349 in
  obtain ⟨sig,ids⟩ := splitAnd top
  open GeneralDeclarativeWitnessProblem349 in
  obtain ⟨bind,scope⟩ := splitAnd tail
  open GeneralDeclarativeWitnessProblem349 in
  obtain ⟨made,lexical⟩ := splitAnd bind
  have mixed : ∀ c ∈ parentDecl.requirements,
      CountsCovered parentDecl.head c.arguments ∧ Smaller parentDecl.head c.arguments ∧
      ConservativeSmaller parentDecl.head c.arguments ∧ StableSmaller parentDecl.head c.arguments := by
    intro c belongs
    change c ∈ [first,second] at belongs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at belongs
    rcases belongs with rfl|rfl
    · exact RecordK2412.checked_closed_record_descent412 (by decide +kernel)
    · exact checked_ordinary_descent428 (by decide +kernel) (nested_var_stable428 30 31 9 8)
  refine ⟨GeneralDeclarativeWitnessSignature349.checked_signature sig,
    GeneralDeclarativeWitnessChecks349.identified ids,GeneralDeclarativeWitnessChecks349.produced made,
    GeneralDeclarativeWitnessChecks349.output_only lexical,GeneralDeclarativeWitnessChecks349.scope_sound scope,
    GeneralDeclarativeWitnessModeDeclaration357.scoped_decl (cover.1 _ included),?_,?_,?_,?_⟩
  · exact fun c h => (mixed c h).1
  · exact fun c h => (mixed c h).2.1
  · exact fun c h => (mixed c h).2.2.1
  · exact fun c h => (mixed c h).2.2.2

def parentNode : Event mixedProblem.state mixedProblem.root :=
  originalNoOutputEvent427 mixedProblem.state.b6 frame rootPick.head rfl
def structNode : Event mixedProblem.state actualRecord.child :=
  selectedStruct.source.event (atlas:=mixedProblem.state.b6)

private inductive Fresh (s : I72.State) : (q : Request) → Event s q → Type where
  | outer {q} (read : ReadPositiveHead427 s.core q)
      (f : AuthoredBodyFrame393 s.core q) (actualDecl : f.decl = read.decl)
      (capture : f.input = read.capture)
      (single : visible s.core q = [read.decl])
      (declared : DeclarationChecked (authoredRegistry s.core.current).constructors
        (authoredRegistry s.core.current).roles f.decl)
      (record : OriginalRecordArgument427 f 0 0)
      (direct : LiteralVariableArgumentAt428 f 1)
      (noOutputs : q.demand.outputs = [])
      (raw : ∀ d ∈ visible s.core q, ∃ p code,
        d.head = [p] ∧ translateWhere427 s.core p = some code ∧
        ∀ a ∈ q.demand.arguments,
          ¬ GeneralDeclarativeInspect321.PatternK2 s.core.current.ordinary a.lower code) :
    Fresh s q (originalNoOutputEvent427 s.b6 f (actualDecl.symm ▸ read.head) noOutputs)
  | structural {q} {f : AuthoredBodyFrame393 s.core q} {k}
      {original : OriginalRecordArgument427 f k 0} (data : ReadClosedChild427 original s.b6) :
    Fresh s original.child (data.source.event (atlas:=s.b6))

private def structuralTestRules : SourcePrimitives where
  elected s q e needs := needs = [] ∧ Nonempty (Fresh s q e)
  other _ _ _ _ := False

private theorem structural_local_same_model428 : SelectedLaw428 structuralTestRules := by
  intro s q e needs picked m fit
  obtain ⟨source⟩ := picked.2
  cases source with
  | outer read f same _ _ _ _ _ empty _ =>
    exact no_output_ordinary_event_same_model_semantics428 f (same.symm ▸ read.head) empty m fit
  | structural data =>
    refine ⟨⟨source_head_sound data.source.sourceHead m fit,?_⟩,?_⟩ <;>
      (intro i; exact Fin.elim0 (Fin.cast (congrArg List.length data.source.noOutputs) i))

private theorem parent_raw_exact428 :
    ∀ d ∈ visible mixedProblem.state.core mixedProblem.root,
      ∃ p code, d.head = [p] ∧ translateWhere427 mixedProblem.state.core p = some code ∧
        ∀ a ∈ mixedProblem.root.demand.arguments,
          ¬ GeneralDeclarativeInspect321.PatternK2 mixedProblem.state.core.current.ordinary a.lower code := by
  intro d visibleAt
  have only : visible mixedProblem.state.core mixedProblem.root = [parentDecl] := by decide +kernel
  rw [only] at visibleAt
  cases List.mem_singleton.mp visibleAt
  have checked : checkedCandidateVisitBySource427 mixedProblem.state.core 30 parentDecl = true := by decide +kernel
  obtain ⟨p,code,head,ue,acyclic⟩ :=
    checked_candidate_by_source_visits_exact427 (root:=0) (known:=1) (w:=⟨rootEsc,insideEsc⟩)
      (by decide +kernel) checked
  refine ⟨p,code,head,ue,?_⟩
  intro a seen
  have eq : a = point 0 := List.mem_singleton.mp seen
  cases eq
  exact acyclic

private theorem parent_local428 :
    structuralTestRules.elected mixedProblem.state mixedProblem.root parentNode [] :=
  ⟨rfl,⟨.outer rootPick frame rfl rfl (by decide +kernel) checked_parent_syntax428
    actualRecord actualVariable rfl parent_raw_exact428⟩⟩

private def oldFrame : AuthoredBodyFrame393 mixedProblem.state.core actualLegacy.root :=
  ⟨2,legacyDecl,by decide +kernel,by
    change legacyDecl ∈ visible actualLegacy.state.core actualLegacy.root
    rw [singleton_legacy]
    exact List.mem_cons_self,unusedPlacement403,
    preoutputInputOfHead399 oldRead.known.head (fun _ => emptyCapture403)⟩
def oldNode : Event mixedProblem.state actualLegacy.root :=
  originalNoOutputEvent427 mixedProblem.state.b6 oldFrame oldRead.known.head oldRead.known.noOutputs
private theorem true_old_local428 : Named409.R1.elected mixedProblem.state actualLegacy.root oldNode [] :=
  .inr ⟨rfl,⟨oldRead.known,rfl,rfl⟩⟩

def mixedRules : SourcePrimitives := ruleUnion428 RepeatedCenters421.R13 structuralTestRules

def newLeafTrace : SourceTrace mixedRules mixedProblem.state actualRecord.child
    (.selected selectedStruct.source.decl.id []) (some structNode) := by
  have clear : structNode.kids = [] := StructuralWhere427.closed_child_no_where427 selectedStruct.source
  let forest : WhereForest mixedRules mixedProblem.state structNode.kids [] :=
    clear.symm ▸ (WhereForest.nil : WhereForest mixedRules mixedProblem.state [] [])
  exact .selected structNode selectedStruct.rawSafe (.inr ⟨rfl,⟨.structural selectedStruct⟩⟩) .nil forest

def oldLeafTrace : SourceTrace mixedRules mixedProblem.state actualLegacy.root
    (.selected 88 []) (some oldNode) := by
  have clear : oldNode.kids = [] := by
    simp [oldNode,oldFrame,originalNoOutputEvent427,Event.kids,frameWhereKids400,
      AuthoredBodyFrame393.clauses,children,legacyDecl]
  let forest : WhereForest mixedRules mixedProblem.state oldNode.kids [] :=
    clear.symm ▸ (WhereForest.nil : WhereForest mixedRules mixedProblem.state [] [])
  exact .selected oldNode oldRead.rawSafe
    (.inl (old_named_local_election_is_still_R13_428 true_old_local428)) .nil forest

def actualBoth := assembleActualMixedSiblings428 (R:=mixedRules) parentNode actualRecord actualVariable
  (by decide +kernel) (rootPick.safe mixedProblem.state.b6) (.inr parent_local428) newLeafTrace oldLeafTrace

theorem exact_mixed_trace_has_no_support_or_requested_outputs428 :
    ZeroSupportSelected428 actualBoth := by
  apply mixed_original_siblings_preserve_empty_support_and_outputs428
  · rfl
  · exact selected_leaf_with_zero_outputs_and_no_where_has_no_support428 (R:=mixedRules) structNode
      selectedStruct.rawSafe (.inr ⟨rfl,⟨.structural selectedStruct⟩⟩)
      (closed_child_no_where427 selectedStruct.source) selectedStruct.source.noOutputs
  · apply selected_leaf_with_zero_outputs_and_no_where_has_no_support428 (R:=mixedRules) oldNode
      oldRead.rawSafe (.inl (old_named_local_election_is_still_R13_428 true_old_local428))
    · simp [oldNode,oldFrame,originalNoOutputEvent427,Event.kids,frameWhereKids400,
        AuthoredBodyFrame393.clauses,children,legacyDecl]
    · exact oldRead.known.noOutputs

private theorem dictionaryKey : selectedStruct.source.decl.id = 219 := by decide +kernel
theorem old_and_new_events_really_classify_same_original_parent428 :
    Classifies mixedRules mixedProblem.state mixedProblem.root (.selected (.node 218 [.node 219 [],.node 88 []])) := by
  refine ⟨_,_,⟨actualBoth⟩,?_⟩
  have rootKey : parentNode.frame.decl.id = 218 := by decide +kernel
  rw [rootKey,dictionaryKey]
  exact .selected (.cons (.selected .nil (.selected rfl))
    (.cons (.selected .nil (.selected rfl)) .nil)) (.selected rfl)

theorem real_mixed_old_and_new_trace_has_one_dictionary_in_every_fit428
    (m : I72.Model) (fit : I72.Fits mixedProblem.state m) :
    DictionaryEvidence mixedProblem.state m mixedProblem.root (.node 218 [.node 219 [],.node 88 []]) :=
  dictionary_sound_for_actual_mixed_named_rule_traces428 current_R13_local_law_for_mixed_named_traces428
    structural_local_same_model428 _ _ _
    old_and_new_events_really_classify_same_original_parent428 m fit

theorem mixed_trace_is_not_vacuous428 :
    I72.Fits mixedProblem.state fitModel ∧
      DictionaryEvidence mixedProblem.state fitModel mixedProblem.root (.node 218 [.node 219 [],.node 88 []]) :=
  ⟨genuine_mixed_problem_has_one_model428,
    real_mixed_old_and_new_trace_has_one_dictionary_in_every_fit428 fitModel genuine_mixed_problem_has_one_model428⟩

#print axioms old_named_local_election_is_still_R13_428
#print axioms assembleActualMixedSiblings428
#print axioms original_structural_and_variable_children_are_not_the_same428
#print axioms existing_actual_named_leaf_checker_runs_on_the_literal_sibling428
#print axioms existing_current_dispatch_uses_the_actual_legacy_named_sibling428
#print axioms named_leaf_checker_does_not_relabel_actual_structural_child428
#print axioms real_mixed_old_and_new_trace_has_one_dictionary_in_every_fit428
#print axioms mixed_trace_is_not_vacuous428
#print axioms exact_mixed_trace_has_no_support_or_requested_outputs428

end Yulang.GeneralDeclarativeI65.I72.StructuralWhereMixedSibling428
