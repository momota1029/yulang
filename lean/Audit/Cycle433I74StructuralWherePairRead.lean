import Yulang.GeneralDeclarativeI65I74StructuralWherePairTrace433
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapPairReadAudit433
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

def rootCert : List410.ExactEscapeWire :=
  ⟨[0,1,2,3,1,5,6,7,8,9,10,11,12],[1,1,1,1,2,2,0,2,2,2,2,2,2]⟩
def caller : Problem := ⟨state,wrapRequest⟩
def wire : TwoNamedWrapWire433 := ⟨0,6,7,rootCert,pickWire,siblingWire⟩

def readChildren (w : TwoNamedWrapWire433) :=
  (readTwoNamedWrap433 caller w).map fun p =>
    (p.first.declaration.decl.id,p.second.declaration.decl.id,
      p.original.origin.child.occurrence,
      (p.event.frame.whereFor p.original.sibling).demand.outputs.head?.map
        GeneralSourceState.Output.target)

theorem both_original_children_end_in_same_literal_target433 :
    readChildren wire = some (57,58,[72,0],some 4) := by decide +kernel

theorem swapped_caller_certificates_do_not_select_the_same_where433 :
    readChildren ⟨0,6,7,rootCert,siblingWire,pickWire⟩ = none := by decide +kernel

theorem other_fixed_row_for_second_original_child_fails433 :
    readChildren {wire with second := {siblingWire with outputRow := 7}} = none := by decide +kernel

def parentActualWrite : Check408.Write :=
  ⟨[72],0,0,⟨6,12⟩,.explicit parentOut,.node 4 [40] [.node 10 [0,2,9,4,4,4] []]⟩

def expectPair : Result :=
  ⟨.selected 218 [exactChildReport.tree,exactSiblingReport.tree],
    .selected (.node 218 [.node 57 [],.node 58 []]),
    [parentActualWrite] ++ exactChildReport.writes ++ exactSiblingReport.writes⟩

theorem two_distinct_children_data_read_has_exact_typed_order433 :
    (readTwoNamedWrap433 caller wire).map (fun x => matchesAssociatedReport432 expectPair x.report) =
      some true := by decide +kernel

theorem reordered_shared_target_is_not_accepted_as_original_receipts433 :
    (readTwoNamedWrap433 caller wire).map
      (fun x => matchesAssociatedReport432 {expectPair with writes := expectPair.writes.reverse} x.report) =
      some false := by decide +kernel

theorem original_public_singleton_scope_has_not_changed433 :
    check caller expectPair (.associatedWrap ⟨0,6,7,rootCert,pickWire⟩) = false := by decide +kernel

#print axioms two_distinct_children_data_read_has_exact_typed_order433
#print axioms reordered_shared_target_is_not_accepted_as_original_receipts433
#print axioms original_public_singleton_scope_has_not_changed433
#print axioms read_pair_exact_original_kids433
#print axioms read_pair_has_exact_source_trace_and_order433
#print axioms read_pair_same_model_dictionary433
#print axioms both_original_children_end_in_same_literal_target433
#print axioms swapped_caller_certificates_do_not_select_the_same_where433
#print axioms other_fixed_row_for_second_original_child_fails433
end Yulang.GeneralDeclarativeI65.I72.WrapPairReadAudit433
