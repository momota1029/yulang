import Yulang.GeneralDeclarativeI65I74StructuralWhereAssociatedLocal432
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapComposedAudit432
open GeneralDeclarativeI65 WhereAssociated432
open GeneralDeclarations (Declaration Clause OutputBinder)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeEmissionForest322 (Placement)
open CommonNominalFullCarrier (Ty record subtype_refl Equivalent nominal)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeHead320 (Read)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeWitnessConstructorModes357 (Use readUse)
open CommonRoleOutermostResolver (Summarizes)
open ClosedResidual415 (wholeExpr wholeOriginal residualExpr strRow)
open Checker408 (Problem Result)

def listCtor : Nat := 40
def binder : OutputBinder := ⟨9,50,51⟩
def authoredClause : Clause := ⟨50,7,[.var 8],[⟨51,3,.var 9⟩]⟩
def parentOut : GeneralDeclarations.Equation := ⟨52,6,.app listCtor [.var 9]⟩
def wrapDecl : Declaration :=
  ⟨218,20,[.app listCtor [.var 8]],[authoredClause],[parentOut],[binder]⟩
def containerOut : GeneralDeclarations.Equation := ⟨92,3,.var 8⟩
def containerDecl : Declaration :=
  ⟨57,7,[ExplicitPick419.pickSyntax 20 8 13],[],[containerOut],[]⟩

private def bits : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
private def inputBundle : InputBundle :=
  let catalogue : List Row := [⟨listCtor,some ⟨[.type],listCtor⟩,.invariant⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,
    ⟨1,[⟨7,1,[(3,none)]⟩,⟨20,1,[(6,none)]⟩]⟩,[wrapDecl,containerDecl]⟩
private def env? : Option Environment := do
  let program ← compile bits
  let bundle ← GeneralSourceMetadataBareBundle291.compile inputBundle
  pure ⟨0,0,0,bits,program,bundle⟩
def env : Environment := env?.get (by decide +kernel)

def rootRow : Equation := ⟨0,wholeExpr 20 1 21 2⟩
def xRow : Equation := OpenTail414.intRow 1
def yRow : Equation := strRow 2
def tailRow : Equation := ⟨3,residualExpr 21 2⟩
def splitRow : Equation := OpenTail414.openRow 0 20 1 3
def keptItem : Equation := ⟨4,.variable 1⟩
def parentHeadRow : Equation := ⟨6,.nominal listCtor [.variable 0]⟩
def parentOutRow : Equation := ⟨12,.nominal listCtor [.variable 4]⟩
def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[rootRow,xRow,yRow,tailRow,splitRow,keptItem,parentHeadRow,parentOutRow]⟩

def core : GeneralDeclarativeI65.State :=
  ⟨⟨env,raw,[]⟩,List.replicate 40 [] ++ [[(⟨.value,.invariant⟩ : Parameter)]],
    [⟨0,[44],wholeOriginal 20 1 21 2⟩],[]⟩

def nominalUse : Use core.current.environment listCtor 1 :=
  (readUse core.current.environment listCtor 1).get (by decide +kernel)
def param : Parameter := ⟨.value,.invariant⟩
def parentPlan : B6MixedRhs401 core false
    (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit parentOut))) :=
  invariantUnaryValuePlan432 listCtor binder.name param nominalUse (by decide +kernel) (by decide +kernel) rfl rfl

def atlas : B6OccurrenceAtlas401 core := ⟨fun q ordinal i body =>
  if q.occurrence == [72,0] && ordinal == 1 && i.val == 0 then
    if h : body = .explicit containerOut then
      some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 core false
        (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit containerOut)))))
    else none
  else if q.occurrence == [72] && ordinal == 0 && i.val == 0 then
    if h : body = .explicit parentOut then some (h.symm ▸ parentPlan) else none
  else none⟩

def state : I72.State := ⟨core,atlas⟩
def wrapRequest : Request := ⟨[72],⟨20,[point 6],[⟨6,12⟩]⟩⟩
def originalPlacement : Placement := ⟨fun _ _ => point 0,fun _ _ => 4⟩
def wrapFrame : AuthoredBodyFrame393 core wrapRequest :=
  ⟨0,wrapDecl,by decide +kernel,by decide +kernel,originalPlacement,fun n => if n = 8 then point 0 else point 6⟩

def containerRequest : Request :=
  ((frameWhereKids400 wrapFrame)[0]?).get (by decide +kernel)
def actualChild : Problem := ⟨state,containerRequest⟩
def pickWire : ExplicitPick419.PickWire := ⟨⟨0,0,1,2,3,4⟩,1,5,⟨[0,1,2,3,1,5,6,7,8,9,10,11,12],[0,1,1,2,2,2,2,2,2,2,2,2,2]⟩⟩
def exactChildReport : Result :=
  ⟨.selected 57 [],.selected (.node 57 []),
    [⟨[72,0],1,0,⟨3,4⟩,.explicit containerOut,.node 0 [8,1,1,1] []⟩]⟩
def childWitness : StructuralWhere431.Witness :=
  .previous (.previous (.previous (.previous (.explicitPick pickWire))))

theorem original_wrap_child_addresses432 :
    containerRequest.occurrence = [72,0] ∧
    containerRequest.demand.role = 7 ∧ containerRequest.demand.arguments = [point 0] ∧
    containerRequest.demand.outputs = [⟨3,4⟩] :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem selected_original_wrap_child_uses_public_R15_432 :
    StructuralWhere431.check actualChild exactChildReport childWitness = true := by
  decide +kernel

theorem original_wrap_child_is_classified_same_request432 :
    I72.Classifies StructuralWhere431.R15 state containerRequest (.selected (.node 57 [])) :=
  (StructuralWhere431.verified_R15_result_classifies_in_same_State431 _ _ _
      selected_original_wrap_child_uses_public_R15_432).1


def childPacket : ExplicitPick419.PickPacket actualChild :=
  (ExplicitPick419.replayPick419 actualChild pickWire).get (by decide +kernel)
open StructuralWhere428

theorem preserveR11 : NamedRuleMap428 ExplicitPick419.R11 StructuralWhere431.R15.named426 :=
  ⟨fun h => .inl (.inl (.inl h)),fun h => .inl (.inl h)⟩

private def oldSource : SourceTrace ExplicitPick419.R11 state containerRequest
    (.selected childPacket.declaration.decl.id []) (some childPacket.event) :=
  .selected childPacket.event childPacket.rawSafe (.inr ⟨rfl,⟨.actual childPacket⟩⟩) .nil
    ((ExplicitPick419.actual_pick_never_switches_to_a_where_child419 childPacket).symm ▸
      (.nil : WhereForest ExplicitPick419.R11 state [] []))

theorem actual_child_source_retains_the_origin_event_and_report432 :
    ∃ actual : SourceTrace StructuralWhere431.R15.named426 state containerRequest exactChildReport.tree
        (some childPacket.event), namedTraceWrites428 actual = exactChildReport.writes := by
  have declaration : childPacket.declaration.decl.id = 57 := by decide +kernel
  have ledger : exactChildReport.writes = [childPacket.retained.write] := by
    have oldAccept : ExplicitPick419.check actualChild exactChildReport (.explicitPick pickWire) = true :=
      selected_original_wrap_child_uses_public_R15_432
    obtain ⟨a,found,report⟩ := ExplicitPick419.checked_report_uses_original_pick419 oldAccept
    have foundExact : ExplicitPick419.replayPick419 actualChild pickWire = some childPacket :=
      Option.eq_some_of_isSome (by decide +kernel)
    have same := Option.some.inj (found.symm.trans foundExact)
    subst a
    exact congrArg (fun r : Result => r.writes) report
  let moved := mapNamedTrace428 preserveR11 oldSource
  have emptyWrites : ∀ qs (h : qs = []),
      namedForestWrites428 (h.symm ▸ (.nil : WhereForest ExplicitPick419.R11 state [] [])) = [] := by
    intro qs h
    cases h
    rfl
  have before : namedTraceWrites428 oldSource = exactChildReport.writes := by
    change Check408.encodedEventWrites childPacket.event ++ namedForestWrites428
      ((ExplicitPick419.actual_pick_never_switches_to_a_where_child419 childPacket).symm ▸
        (.nil : WhereForest ExplicitPick419.R11 state [] [])) = _
    rw [ExplicitPick419.actual_event_has_only_its_original_output419,
      emptyWrites _ (ExplicitPick419.actual_pick_never_switches_to_a_where_child419 childPacket),ledger]
    rfl
  have tree : (CommonRoleOutermostResolver.Tree.selected childPacket.declaration.decl.id []) =
      exactChildReport.tree := by rw [declaration]; rfl
  have unchanged : ∀ x (eq : CommonRoleOutermostResolver.Tree.selected childPacket.declaration.decl.id [] = x),
      namedTraceWrites428 (eq ▸ moved.val) = namedTraceWrites428 moved.val := by
    intro x eq
    cases eq
    rfl
  exact ⟨tree ▸ moved.val,(unchanged _ tree).trans (moved.property.1.trans before)⟩

def actualBinderOrigin : OriginalWhereBinder395 wrapFrame binder parentOut :=
  ⟨0,0,wrapFrame.whereFor authoredClause,⟨51,3,.var 9⟩,⟨3,4⟩,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem old_selected_child_has_actual_where_binder_output432
    (m : I72.Model) (fit : I72.Fits state m) :
    containerRequest = actualBinderOrigin.child ∧
    (childPacket.retained.output.receipt).occurrence = wrapRequest.occurrence ++ [0] ∧
    (childPacket.retained.output.receipt).outputOrdinal = 0 ∧
    (childPacket.retained.output.receipt).original = actualBinderOrigin.output ∧
    wrapFrame.slots (.explicit parentOut) binder.name = some (point 4) ∧
    (childPacket.retained.output.receipt).actualEquation m = some (4,(m.assignment 1).1) ∧
    Equivalent (m.assignment 4).1 (m.assignment 1).1 ∧
    DictionaryEvidence state m containerRequest (.node 57 []) := by
  have read := ExplicitPick419.retained_output_is_same_field_in_every_fitting_model419 childPacket m fit
  have sourceSlot : childPacket.rows.intSlot = 1 := by decide +kernel
  have targetSlot : actualChild.root.demand.outputs[
      ExplicitPick419.exactlyOneOutput actualChild childPacket.single].target = 4 := by
    rfl
  rw [sourceSlot,targetSlot] at read
  exact ⟨rfl,rfl,rfl,rfl,actualBinderOrigin.slot,read.1,read.2,
    StructuralWhere431.dictionary_sound_R15 _ _ _ original_wrap_child_is_classified_same_request432 m fit⟩

def actualResidual : Ty := record 21 (.base .str) .emptyRecord
def actualRecord : Ty := record 20 (.base .int) actualResidual
def fittingModel : I72.Model :=
  ⟨fun n => ((if n = 0 then actualRecord else if n = 2 then .base .str
                  else if n = 3 then actualResidual else if n = 6 then nominal listCtor [.inl actualRecord]
                  else if n = 12 then nominal listCtor [.inl (.base .int)] else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (wholeOriginal 20 1 21 2) else none⟩

theorem child_receipt_control_has_fitting_model432 : I72.Fits state fittingModel := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [rootRow,xRow,yRow,tailRow,splitRow,keptItem,parentHeadRow,parentOutRow] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ h; cases h
  · intro _ h
    cases List.mem_singleton.mp h
    rfl

theorem mismatched_child_write_not_accepted432 :
    StructuralWhere431.check actualChild {exactChildReport with writes := []} childWitness = false := by
  decide +kernel


def mainEscape : List410.ExactEscapeWire :=
  ⟨[0,1,2,3,1,5,6,7,8,9,10,11,12],[1,1,1,1,2,2,0,2,2,2,2,2,2]⟩
theorem real_parent_requested_root_is_safe432 : ¬ RootCycle state wrapRequest := by
  have safe : List410.checkExactEscape core.current.ordinary 6 mainEscape = true := by decide +kernel
  rintro ⟨arg,h,c⟩
  change arg ∈ [point 6] at h
  cases List.mem_singleton.mp h
  exact List410.exact_escape_refutes_raw_root_K2410 safe c

private def wrapHead : SourceHead core wrapRequest wrapDecl := by
  have payload : Read core.current.ordinary wrapFrame.input .actual 0 (.variable 8) :=
    .capture (Bound.refl 0) (Bound.refl 0)
  have original : Read core.current.ordinary wrapFrame.input .actual 6 (.nominal listCtor [.variable 8]) := by
    apply Read.nominal (n:=1) (fun _ => 0) (fun _ => .variable 8)
    · change parentHeadRow ∈ [rootRow,xRow,yRow,tailRow,splitRow,keptItem,parentHeadRow,parentOutRow]
      simp
    · exact fun _ => payload
  refine .ordered wrapFrame.input (.cons (.ordinary ⟨⟨.refl _,.refl _⟩,.nominal listCtor [.variable 8],
    ?_,.direct (.structural original)⟩) .nil)
  rfl

def parentOutAt : Fin wrapRequest.demand.outputs.length := ⟨0,by decide +kernel⟩
def namedParentRhs : NamedMixedTree401 core (wrapFrame.slots (.explicit parentOut)) false
    (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit parentOut))) :=
  .declaredApp (params := [param]) listCtor nominalUse (by decide +kernel) (by decide +kernel)
    (.cons (.valueInterval binder.name rfl rfl ⟨point 4,rfl⟩) .nil)

private def origParentOutput : NamedMixedOutput401 atlas wrapFrame parentOutAt :=
  ⟨.explicit parentOut,.explicit parentOut (by decide +kernel) rfl,parentPlan,
    rfl,namedParentRhs,by
      simp [parentPlan,invariantUnaryValuePlan432,namedParentRhs,substituteMixedRhs401,
        substituteMixedArgs401,substituteMixedArg401,instantiateName401]
      rfl⟩

def actualParent : Event state wrapRequest :=
  ⟨wrapFrame,wrapHead,fun i => (show parentOutAt = i from Fin.eq_of_val_eq (by
      have hi : i.val < 1 := i.isLt
      change 0 = i.val
      omega)) ▸ origParentOutput⟩


theorem actualWrapRegistryChecked : GeneralDeclarations.Checked
    (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry core.current) := by
  have full : GeneralSourceMetadataDeclarations291.explicitCheck
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry core.current)
      (GeneralSourceMetadataRows291.interpretation env.source.snapshot) = true := by decide +kernel
  have covered := (GeneralSourceMetadataDeclarations291.explicit_exact _ _).mp full
  refine ⟨by decide +kernel,?_⟩
  intro d member
  have source := covered d member
  change d ∈ [wrapDecl,containerDecl] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;>
    exact GeneralDeclarativeWitnessHeader349.decl_checked source (by decide +kernel)

theorem parent_is_sole_authored_visible432 : visible core wrapRequest = [wrapDecl] := by
  decide +kernel

theorem actual_wrap_retains_typed_output432 : RetainedTypedValueRows403 actualParent := by
  intro i
  have exactIndex : i = parentOutAt := Fin.eq_of_val_eq (by
    have bound : i.val < 1 := i.isLt
    change i.val = 0
    omega)
  subst i
  refine ⟨.nominal listCtor [.variable 4],rfl,?_⟩
  change parentOutRow ∈ raw.equations
  simp [raw]

def actualWrapScope : OriginalAssociatedWrap432 actualParent where
  checked := actualWrapRegistryChecked
  onlyVisible := parent_is_sole_authored_visible432
  rawRoot := real_parent_requested_root_is_safe432
  headBinder := 8
  ctor := listCtor
  arg := point 6
  input := rfl
  literalHead := rfl
  actualNames := rfl
  outputBinder := binder
  binderInSource := by decide +kernel
  literalRhs := parentOut
  origin := actualBinderOrigin
  originalWhere := rfl
  independentInput := rfl
  onlyParentOutput := rfl
  indexedParentOutput := parentOutAt
  body := rfl
  normalized := rfl
  parameter := param
  use := nominalUse
  authoredModes := by decide +kernel
  matchingModeTable := by decide +kernel
  valueKind := rfl
  invariant := rfl
  actualTypedRhs := HEq.rfl
  retained := actual_wrap_retains_typed_output432

abbrev composedRules : SourcePrimitives := associatedWhereKernel432.named426

theorem composed_named_source_has_same_model_soundness432 : DictionarySound composedRules :=
  dictionary_sound_from_actual_named_local_law428 associated_named_law432

def exactParentWrite : Check408.Write :=
  ⟨[72],0,0,⟨6,12⟩,.explicit parentOut,.node 4 [40] [.node 10 [0,2,9,4,4,4] []]⟩

theorem actual_wrap_encodes_original_typed_write432 :
    Check408.encodedEventWrites actualParent = [exactParentWrite] := by
  rfl

theorem exact_same_State_wrap_container_trace432 :
    ∃ (trace : SourceTrace composedRules state wrapRequest
        (.selected 218 [exactChildReport.tree]) (some actualParent))
      (actualChildTrace : SourceTrace composedRules state containerRequest exactChildReport.tree
        (some childPacket.event)),
      ActualWhereTraceAt432 trace 0 actualChildTrace ∧
      namedTraceWrites428 actualChildTrace = exactChildReport.writes ∧
      namedTraceWrites428 trace = exactParentWrite :: exactChildReport.writes ∧
      Summarizes (.selected 218 [exactChildReport.tree]) (.selected (.node 218 [.node 57 []])) := by
  obtain ⟨old,oldWrites⟩ := actual_child_source_retains_the_origin_event_and_report432
  let now := mapNamedTrace428 (left_named_rule_map428 StructuralWhere431.R15.named426 associatedWrapLocal432) old
  have whereSame : actualParent.kids = [containerRequest] := rfl
  let childForest : WhereForest composedRules state [containerRequest] [exactChildReport.tree] :=
    .cons now.val .nil
  let actual := SourceTrace.selected actualParent real_parent_requested_root_is_safe432
      (R:=composedRules)
      (.inr ⟨rfl,⟨actualWrapScope⟩⟩) .nil (whereSame.symm ▸ childForest)
  have attach : ActualWhereTraceAt432 actual 0 now.val := by
    have castKeeps : ∀ qs (eq : [containerRequest] = qs),
        ActualForestTraceAt432 composedRules state (eq ▸ childForest) 0 now.val := by
      intro qs eq
      cases eq
      exact .here now.val .nil
    exact castKeeps _ whereSame.symm
  have childOrder := now.property.1.trans oldWrites
  have castWrites : ∀ qs (eq : [containerRequest] = qs),
      namedForestWrites428 (eq ▸ childForest) = namedTraceWrites428 now.val := by
    intro qs eq
    cases eq
    change namedTraceWrites428 now.val ++ [] = namedTraceWrites428 now.val
    simp
  have originalOrder : namedTraceWrites428 actual =
      exactParentWrite :: exactChildReport.writes := by
    change Check408.encodedEventWrites actualParent ++
      namedForestWrites428 (whereSame.symm ▸ childForest) = _
    rw [actual_wrap_encodes_original_typed_write432,castWrites _ whereSame.symm,childOrder]
    rfl
  exact ⟨actual,now.val,attach,childOrder,originalOrder,
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem actual_composed_wrap_has_fixed_list_of_the_original_item432
    (m : I72.Model) (fit : I72.Fits state m) :
    DictionaryEvidence state m wrapRequest (.node 218 [.node 57 []]) ∧
      (actualParent.outputs parentOutAt).receipt.actualEquation m =
        some (12,nominal listCtor [.inl (m.assignment 4).1]) ∧
      Equivalent (m.assignment 12).1 (nominal listCtor [.inl (m.assignment 4).1]) := by
  obtain ⟨actual,_,_,_,_,summary⟩ := exact_same_State_wrap_container_trace432
  have source : Classifies composedRules state wrapRequest (.selected (.node 218 [.node 57 []])) :=
    ⟨_,_,⟨actual⟩,summary⟩
  have meaning := composed_named_source_has_same_model_soundness432 _ _ _ source m fit
  have exactOutput := actual_parent_unary_output_uses_exact_where_target432
    associated_named_law432
    actual actualBinderOrigin parentOutAt rfl
    (use:=nominalUse) (param:=param) (names:=by decide +kernel) (declared:=by decide +kernel)
    (kind:=rfl) (invariant:=rfl) rfl HEq.rfl m fit
  exact ⟨meaning,exactOutput⟩

theorem actual_composed_control_is_not_model_vacuous432 :
    I72.Fits state fittingModel ∧
    DictionaryEvidence state fittingModel wrapRequest (.node 218 [.node 57 []]) :=
  ⟨child_receipt_control_has_fitting_model432,
    (actual_composed_wrap_has_fixed_list_of_the_original_item432 fittingModel
      child_receipt_control_has_fitting_model432).1⟩

#print axioms actualWrapRegistryChecked
#print axioms actual_wrap_retains_typed_output432
#print axioms actual_wrap_encodes_original_typed_write432
#print axioms original_associated_wrap_local_law432
#print axioms dictionary_sound_for_associated_where_kernel432
#print axioms composed_named_source_has_same_model_soundness432
#print axioms exact_same_State_wrap_container_trace432
#print axioms actual_composed_wrap_has_fixed_list_of_the_original_item432
#print axioms actual_composed_control_is_not_model_vacuous432

#print axioms real_parent_requested_root_is_safe432

#print axioms original_wrap_child_addresses432
#print axioms selected_original_wrap_child_uses_public_R15_432
#print axioms original_wrap_child_is_classified_same_request432
#print axioms old_selected_child_has_actual_where_binder_output432
#print axioms actual_child_source_retains_the_origin_event_and_report432
#print axioms child_receipt_control_has_fitting_model432
#print axioms mismatched_child_write_not_accepted432

end Yulang.GeneralDeclarativeI65.I72.WrapComposedAudit432
