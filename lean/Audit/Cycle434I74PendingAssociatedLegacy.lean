import Yulang.GeneralDeclarativeI65I74PendingAssociatedSeparation434
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.PendingLegacyAudit434
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

/- The values above deliberately recreate the real published C432 Wrap
fixture using production imports, rather than importing another Audit.
It is an already completed original where-source branch with two fixed
typed receipts; no accepted output was synthesized for the new case. -/
def dummyWire : PendingAssociated434.Wire := ⟨mainEscape,mainEscape,[6]⟩

theorem completed_original_wrap_through_public_R17_434 :
    PendingAssociated434.check parentProblem actualReport (.previous (.associatedWrap input)) = true := by
  decide +kernel

theorem genuine_completed_wrap_cannot_use_new_pending_434 :
    PendingAssociated434.check parentProblem PendingAssociated434.pendingReport
      (.pendingAssociated dummyWire) = false := by decide +kernel

theorem completed_child_keeps_exact_previous_report_434 :
    PendingAssociated434.check actualChild exactChildReport (.previous (.previous childWitness)) = true := by
  decide +kernel

theorem completed_wrap_keeps_actual_dictionary_and_receipts_434 :
    Classifies PendingAssociated434.R17 parentProblem.state parentProblem.root actualReport.verdict ∧
    ∀ m : I72.Model, Fits parentProblem.state m →
      PendingAssociated434.ReportEvidence parentProblem.state m parentProblem.root actualReport :=
  PendingAssociated434.verified_R17_result_classifies_in_same_State434 _ _ _
    completed_original_wrap_through_public_R17_434

theorem wrong_completed_original_receipt_order_still_fails_434 :
    PendingAssociated434.check parentProblem {actualReport with writes := actualReport.writes.reverse}
      (.previous (.associatedWrap input)) = false := by decide +kernel

#print axioms completed_original_wrap_through_public_R17_434
#print axioms genuine_completed_wrap_cannot_use_new_pending_434
#print axioms completed_child_keeps_exact_previous_report_434
#print axioms completed_wrap_keeps_actual_dictionary_and_receipts_434
#print axioms wrong_completed_original_receipt_order_still_fails_434
#print axioms PendingAssociated434.original_retained_output_is_known_raw_but_delayed_as_source434
#print axioms PendingAssociated434.checked_entry_reads_raw_nominal_but_derives_source_delay434

end Yulang.GeneralDeclarativeI65.I72.PendingLegacyAudit434
