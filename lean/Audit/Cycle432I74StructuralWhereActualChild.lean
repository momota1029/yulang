import Yulang.GeneralDeclarativeI65I74StructuralWhereDeclaredOutput432
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapChildAudit432
open GeneralDeclarativeI65 WhereAssociated432
open GeneralDeclarations (Declaration Clause OutputBinder)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeEmissionForest322 (Placement)
open CommonNominalFullCarrier (Ty record subtype_refl Equivalent)
open CommonDeclaredNominalInspection (Parameter)
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
def raw : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[rootRow,xRow,yRow,tailRow,splitRow,keptItem]⟩

def core : GeneralDeclarativeI65.State :=
  ⟨⟨env,raw,[]⟩,List.replicate 40 [] ++ [[(⟨.value,.invariant⟩ : Parameter)]],
    [⟨0,[44],wholeOriginal 20 1 21 2⟩],[]⟩

def atlas : B6OccurrenceAtlas401 core := ⟨fun q ordinal i body =>
  if q.occurrence == [72,0] && ordinal == 1 && i.val == 0 then
    if h : body = .explicit containerOut then
      some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 core false
        (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit containerOut)))))
    else none
  else none⟩

def state : I72.State := ⟨core,atlas⟩
def wrapRequest : Request := ⟨[72],⟨20,[point 6],[⟨6,12⟩]⟩⟩
def originalPlacement : Placement := ⟨fun _ _ => point 0,fun _ _ => 4⟩
def wrapFrame : AuthoredBodyFrame393 core wrapRequest :=
  ⟨0,wrapDecl,by decide +kernel,by decide +kernel,originalPlacement,fun n => if n = 8 then point 0 else point 6⟩

def containerRequest : Request :=
  ((frameWhereKids400 wrapFrame)[0]?).get (by decide +kernel)
def actualChild : Problem := ⟨state,containerRequest⟩
def pickWire : ExplicitPick419.PickWire := ⟨⟨0,0,1,2,3,4⟩,1,5,⟨[0,1,2,3,1],[0,1,1,2]⟩⟩
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
                  else if n = 3 then actualResidual else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (wholeOriginal 20 1 21 2) else none⟩

theorem child_receipt_control_has_fitting_model432 : I72.Fits state fittingModel := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [rootRow,xRow,yRow,tailRow,splitRow,keptItem] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ h; cases h
  · intro _ h
    cases List.mem_singleton.mp h
    rfl

theorem mismatched_child_write_not_accepted432 :
    StructuralWhere431.check actualChild {exactChildReport with writes := []} childWitness = false := by
  decide +kernel

#print axioms original_wrap_child_addresses432
#print axioms selected_original_wrap_child_uses_public_R15_432
#print axioms original_wrap_child_is_classified_same_request432
#print axioms old_selected_child_has_actual_where_binder_output432
#print axioms actual_child_source_retains_the_origin_event_and_report432
#print axioms child_receipt_control_has_fitting_model432
#print axioms mismatched_child_write_not_accepted432

end Yulang.GeneralDeclarativeI65.I72.WrapChildAudit432
