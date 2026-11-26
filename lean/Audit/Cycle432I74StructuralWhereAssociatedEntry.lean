import Yulang.GeneralDeclarativeI65I74StructuralWhereAssociatedEntry432
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapPublicAudit432
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

def mainEscape : List410.ExactEscapeWire :=
  ⟨[0,1,2,3,1,5,6,7,8,9,10,11,12],[1,1,1,1,2,2,0,2,2,2,2,2,2]⟩
def parentProblem : Problem := ⟨state,wrapRequest⟩
def input : AssociatedWire432 := ⟨0,6,7,mainEscape,pickWire⟩
def parentWrite : Check408.Write :=
  ⟨[72],0,0,⟨6,12⟩,.explicit parentOut,.node 4 [40] [.node 10 [0,2,9,4,4,4] []]⟩
def actualReport : Result :=
  ⟨.selected 218 [exactChildReport.tree],.selected (.node 218 [.node 57 []]),
    parentWrite :: exactChildReport.writes⟩

theorem public_original_wrap_child_output432 :
    check parentProblem actualReport (.associatedWrap input) = true := by decide +kernel
theorem refuses_wrong_original_root_row432 :
    check parentProblem actualReport
      (.associatedWrap {input with parentHeadRow := 0}) = false := by decide +kernel

theorem refuses_wrong_source_declaration_ordinal432 :
    check parentProblem actualReport
      (.associatedWrap {input with parentDeclaration := 1}) = false := by decide +kernel

theorem rejects_wrong_parent_fixed_row432 :
    check parentProblem actualReport (.associatedWrap {input with parentOutputRow := 6}) = false := by decide +kernel
theorem rejects_wrong_original_child_output_row432 :
    check parentProblem actualReport
      (.associatedWrap {input with child := {pickWire with outputRow := 7}}) = false := by decide +kernel
theorem rejects_reordered_original_receipts432 :
    check parentProblem {actualReport with writes := actualReport.writes.reverse}
      (.associatedWrap input) = false := by decide +kernel
theorem existing_public_child_still_checks432 :
    check actualChild exactChildReport (.previous childWitness) = true := by decide +kernel
theorem no_data_no_acceptance432 :
    check parentProblem actualReport .unsupported = false := rfl

#print axioms public_original_wrap_child_output432
#print axioms refuses_wrong_original_root_row432
#print axioms refuses_wrong_source_declaration_ordinal432
#print axioms rejects_wrong_parent_fixed_row432
#print axioms rejects_wrong_original_child_output_row432
#print axioms rejects_reordered_original_receipts432
#print axioms existing_public_child_still_checks432
#print axioms no_data_no_acceptance432
#print axioms read_wrap_preserves_exact_selected_source_and_writes432
#print axioms exact_associated_report_classifies_R16_432
#print axioms dictionary_sound_R16
#print axioms WhereAssociated432.check_sound
#print axioms verified_R16_result_classifies_in_same_State432
#print axioms all_prior_verdicts_in_R16_432
#print axioms previous_R15_entry_is_identical432
end Yulang.GeneralDeclarativeI65.I72.WrapPublicAudit432
