import Yulang.GeneralDeclarativeI65I74StructuralWhereSiblingReceipts433
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapSiblingAudit433
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
def siblingClause : Clause := ⟨54,8,[.var 8],[⟨55,5,.var 9⟩]⟩
def parentOut : GeneralDeclarations.Equation := ⟨52,6,.app listCtor [.var 9]⟩
def wrapDecl : Declaration :=
  ⟨218,20,[.app listCtor [.var 8]],[authoredClause,siblingClause],[parentOut],[binder]⟩
def containerOut : GeneralDeclarations.Equation := ⟨92,3,.var 8⟩
def containerDecl : Declaration :=
  ⟨57,7,[ExplicitPick419.pickSyntax 20 8 13],[],[containerOut],[]⟩

def siblingOut : GeneralDeclarations.Equation := ⟨93,5,.var 8⟩
def siblingDecl : Declaration :=
  ⟨58,8,[ExplicitPick419.pickSyntax 20 8 13],[],[siblingOut],[]⟩

private def bits : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
private def inputBundle : InputBundle :=
  let catalogue : List Row := [⟨listCtor,some ⟨[.type],listCtor⟩,.invariant⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,
    ⟨1,[⟨7,1,[(3,none)]⟩,⟨8,1,[(5,none)]⟩,⟨20,1,[(6,none)]⟩]⟩,[wrapDecl,containerDecl,siblingDecl]⟩
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
  else if q.occurrence == [72,1] && ordinal == 2 && i.val == 0 then
    if h : body = .explicit siblingOut then
      some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 core false
        (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit siblingOut)))))
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
def siblingRequest : Request :=
  ((frameWhereKids400 wrapFrame)[1]?).get (by decide +kernel)
def actualSibling : Problem := ⟨state,siblingRequest⟩
def siblingWire : ExplicitPick419.PickWire := {pickWire with declaration := 2}
def exactSiblingReport : Result :=
  ⟨.selected 58 [],.selected (.node 58 []),
    [⟨[72,1],2,0,⟨5,4⟩,.explicit siblingOut,.node 0 [8,1,1,1] []⟩]⟩
def childWitness : StructuralWhere431.Witness :=
  .previous (.previous (.previous (.previous (.explicitPick pickWire))))

def siblingWitness : StructuralWhere431.Witness :=
  .previous (.previous (.previous (.previous (.explicitPick siblingWire))))

theorem actual_both_siblings_pass_existing_public_check433 :
    StructuralWhere431.check actualChild exactChildReport childWitness = true ∧
    StructuralWhere431.check actualSibling exactSiblingReport siblingWitness = true := by
  decide +kernel

theorem original_both_siblings_keep_input_and_named_target433 :
    containerRequest.occurrence = [72,0] ∧ siblingRequest.occurrence = [72,1] ∧
    containerRequest.demand.arguments = [point 0] ∧ siblingRequest.demand.arguments = [point 0] ∧
    containerRequest.demand.outputs = [⟨3,4⟩] ∧ siblingRequest.demand.outputs = [⟨5,4⟩] :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

open StructuralWhere428
open CommonRoleOutermostResolver (Tree Dictionary)
open Checker408 (Problem Result)
def actualBinderOrigin : OriginalWhereBinder395 wrapFrame binder parentOut :=
  ⟨0,0,wrapFrame.whereFor authoredClause,⟨51,3,.var 9⟩,⟨3,4⟩,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

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
  change d ∈ [wrapDecl,containerDecl,siblingDecl] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl <;>
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

def originalTwoScope : OriginalTwoNamedWhere433 actualParent where
  checked := actualWrapRegistryChecked
  visibleOnly := parent_is_sole_authored_visible432
  rootSafe := real_parent_requested_root_is_safe432
  binder := binder
  declared := by decide +kernel
  body := parentOut
  origin := actualBinderOrigin
  sibling := siblingClause
  exactlyTwo := rfl
  inOrder := rfl
  headName := 8
  ctor := listCtor
  syntaxHead := rfl
  producerInput := rfl
  siblingInput := rfl
  siblingOutput := ⟨55,5,.var 9⟩
  siblingOutputAt := rfl
  siblingValue := rfl
  out := parentOutAt
  bodyAt := rfl
  normalized := rfl
  parameter := param
  use := nominalUse
  authoredModes := by decide +kernel
  matchingTable := by decide +kernel
  valueKind := rfl
  invariant := rfl
  literalTyped := HEq.rfl
  retained := actual_wrap_retains_typed_output432

abbrev sameNamedRules : SourcePrimitives :=
  ruleUnion428 StructuralWhere431.R15.named426 twoNamedWhereParentRule433

def producerPacket : ExplicitPick419.PickPacket actualChild :=
  (ExplicitPick419.replayPick419 actualChild pickWire).get (by decide +kernel)
def siblingPacket : ExplicitPick419.PickPacket actualSibling :=
  (ExplicitPick419.replayPick419 actualSibling siblingWire).get (by decide +kernel)

private noncomputable def liftPickData (q : Request) (a : ExplicitPick419.PickPacket ⟨state,q⟩) :
    SourceTrace sameNamedRules state q (.selected a.declaration.decl.id []) (some a.event) := by
  let before : SourceTrace ExplicitPick419.R11 state q
      (.selected a.declaration.decl.id []) (some a.event) :=
    .selected a.event a.rawSafe (.inr ⟨rfl,⟨.actual a⟩⟩) .nil
      ((ExplicitPick419.actual_pick_never_switches_to_a_where_child419 a).symm ▸
        (.nil : WhereForest ExplicitPick419.R11 state [] []))
  have embed : NamedRuleMap428 ExplicitPick419.R11 sameNamedRules :=
    ⟨fun h => .inl (.inl (.inl (.inl h))),fun h => .inl (.inl (.inl h))⟩
  exact (mapNamedTrace428 embed before).val

theorem producerId433 : producerPacket.declaration.decl.id = 57 := by decide +kernel
theorem siblingId433 : siblingPacket.declaration.decl.id = 58 := by decide +kernel

noncomputable def exactProducerTrace : SourceTrace sameNamedRules state containerRequest (.selected 57 [])
    (some producerPacket.event) :=
  congrArg (fun n => Tree.selected n []) producerId433 ▸ liftPickData containerRequest producerPacket
noncomputable def exactSiblingTrace : SourceTrace sameNamedRules state siblingRequest (.selected 58 [])
    (some siblingPacket.event) :=
  congrArg (fun n => Tree.selected n []) siblingId433 ▸ liftPickData siblingRequest siblingPacket

noncomputable def exactBothWhere : WhereForest sameNamedRules state [containerRequest,siblingRequest]
    [.selected 57 [],.selected 58 []] :=
  .cons exactProducerTrace (.cons exactSiblingTrace .nil)

noncomputable def actualParentTrace : SourceTrace sameNamedRules state wrapRequest
    (.selected 218 [.selected 57 [],.selected 58 []]) (some actualParent) :=
  .selected actualParent real_parent_requested_root_is_safe432 (.inr ⟨rfl,⟨originalTwoScope⟩⟩) .nil exactBothWhere

theorem actual_sibling_selected_at_literal_second_ordinal433 :
    ActualWhereTraceAt432 actualParentTrace 0 exactProducerTrace ∧
    ActualWhereTraceAt432 actualParentTrace 1 exactSiblingTrace :=
  ⟨.here exactProducerTrace _, .there exactProducerTrace (.here exactSiblingTrace .nil)⟩

theorem two_child_source_named_law433 : SelectedLaw428 sameNamedRules :=
  union_local_law428 StructuralWhere431.named_law431 original_two_named_where_parent_local_law433

private theorem lift_pick_keeps_source_write433
    (q : Request) (a : ExplicitPick419.PickPacket ⟨state,q⟩) :
    namedTraceWrites428 (liftPickData q a) = [a.retained.write] := by
  have empty : ∀ qs (h : qs = []),
      namedForestWrites428 (h.symm ▸ (.nil : WhereForest ExplicitPick419.R11 state [] [])) = [] := by
    intro qs h
    cases h
    rfl
  unfold liftPickData
  rw [(mapNamedTrace428 _ _).property.1]
  change Check408.encodedEventWrites a.event ++
    namedForestWrites428 ((ExplicitPick419.actual_pick_never_switches_to_a_where_child419 a).symm ▸
      (.nil : WhereForest ExplicitPick419.R11 state [] [])) = _
  rw [ExplicitPick419.actual_event_has_only_its_original_output419,
    empty _ (ExplicitPick419.actual_pick_never_switches_to_a_where_child419 a)]
  rfl

private theorem tree_cast_does_not_change_receipts433
    {q : Request} {a : Event state q} {t u : Tree}
    (same : t = u) (tr : SourceTrace sameNamedRules state q t (some a)) :
    namedTraceWrites428 (same ▸ tr) = namedTraceWrites428 tr := by
  cases same
  rfl

def exactTwoParentWrite : Check408.Write :=
  ⟨[72],0,0,⟨6,12⟩,.explicit parentOut,.node 4 [40] [.node 10 [0,2,9,4,4,4] []]⟩

theorem source_report_keeps_parent_then_original_sibling_order433 :
    namedTraceWrites428 actualParentTrace =
      exactTwoParentWrite :: ([producerPacket.retained.write,siblingPacket.retained.write]) := by
  have one : namedTraceWrites428 exactProducerTrace = [producerPacket.retained.write] := by
    unfold exactProducerTrace
    exact (tree_cast_does_not_change_receipts433 _ _).trans
      (lift_pick_keeps_source_write433 containerRequest producerPacket)
  have two : namedTraceWrites428 exactSiblingTrace = [siblingPacket.retained.write] := by
    unfold exactSiblingTrace
    exact (tree_cast_does_not_change_receipts433 _ _).trans
      (lift_pick_keeps_source_write433 siblingRequest siblingPacket)
  change Check408.encodedEventWrites actualParent ++
    (namedTraceWrites428 exactProducerTrace ++ (namedTraceWrites428 exactSiblingTrace ++ [])) = _
  rw [one,two]
  rfl

theorem actual_two_named_siblings_are_both_used_in_one_dictionary433
    (m : I72.Model) (fit : I72.Fits state m) :
    DictionaryEvidence state m wrapRequest (.node 218 [.node 57 [],.node 58 []]) ∧
    (producerPacket.retained.output.receipt).actualEquation m = some (4,(m.assignment 1).1) ∧
    (siblingPacket.retained.output.receipt).actualEquation m = some (4,(m.assignment 1).1) ∧
    (actualParent.outputs parentOutAt).receipt.actualEquation m =
      some (12,nominal listCtor [.inl (m.assignment 4).1]) := by
  have summary : Summarizes (.selected 218 [.selected 57 [],.selected 58 []])
      (.selected (.node 218 [.node 57 [],.node 58 []])) :=
    .selected (.cons (.selected .nil (.selected rfl)) (.cons (.selected .nil (.selected rfl)) .nil)) (.selected rfl)
  have parentMeaning := actual_named_trace_same_model_dictionary428
    two_child_source_named_law433 actualParentTrace m fit _ summary
  have prod := ExplicitPick419.retained_output_is_same_field_in_every_fitting_model419 producerPacket m fit
  have sib := ExplicitPick419.retained_output_is_same_field_in_every_fitting_model419 siblingPacket m fit
  have value := actual_parent_unary_output_uses_exact_where_target432 two_child_source_named_law433
    actualParentTrace actualBinderOrigin parentOutAt rfl
    (use:=nominalUse) (param:=param) (names:=by decide +kernel) (declared:=by decide +kernel)
    (kind:=rfl) (invariant:=rfl) rfl HEq.rfl m fit
  have pa : producerPacket.rows.intSlot = 1 := by decide +kernel
  have sa : siblingPacket.rows.intSlot = 1 := by decide +kernel
  have pb : actualChild.root.demand.outputs[
      ExplicitPick419.exactlyOneOutput actualChild producerPacket.single].target = 4 := rfl
  have sb : actualSibling.root.demand.outputs[
      ExplicitPick419.exactlyOneOutput actualSibling siblingPacket.single].target = 4 := rfl
  rw [pa,pb] at prod
  rw [sa,sb] at sib
  exact ⟨parentMeaning,prod.1,sib.1,value.1⟩

theorem actual_two_named_siblings_joint_model_is_not_vacuous433 :
    I72.Fits state fittingModel ∧
    DictionaryEvidence state fittingModel wrapRequest (.node 218 [.node 57 [],.node 58 []]) :=
  ⟨child_receipt_control_has_fitting_model432,
    (actual_two_named_siblings_are_both_used_in_one_dictionary433 fittingModel
      child_receipt_control_has_fitting_model432).1⟩

#print axioms actual_both_siblings_pass_existing_public_check433
#print axioms original_both_siblings_keep_input_and_named_target433
#print axioms actual_sibling_selected_at_literal_second_ordinal433
#print axioms source_report_keeps_parent_then_original_sibling_order433
#print axioms actual_two_named_siblings_are_both_used_in_one_dictionary433
#print axioms actual_two_named_siblings_joint_model_is_not_vacuous433
#print axioms selected_named_sibling_replays_same_fixed_target433
#print axioms original_two_named_where_parent_local_law433
#print axioms sibling_literal_position_and_exact_value433
end Yulang.GeneralDeclarativeI65.I72.WrapSiblingAudit433
