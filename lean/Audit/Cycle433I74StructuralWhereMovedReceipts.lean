import Yulang.GeneralDeclarativeI65I74StructuralWhereSiblingPermutation433
import Yulang.GeneralDeclarativeI65I74StructuralWhereAssociatedEntry432
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapMovedAudit433
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
private def inputBundle (ownerDecl : Declaration) : InputBundle :=
  let catalogue : List Row := [⟨listCtor,some ⟨[.type],listCtor⟩,.invariant⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,
    ⟨1,[⟨7,1,[(3,none)]⟩,⟨8,1,[(5,none)]⟩,⟨20,1,[(6,none)]⟩]⟩,[ownerDecl,containerDecl,siblingDecl]⟩
private def env? (ownerDecl : Declaration) : Option Environment := do
  let program ← compile bits
  let bundle ← GeneralSourceMetadataBareBundle291.compile (inputBundle ownerDecl)
  pure ⟨0,0,0,bits,program,bundle⟩
def env : Environment := (env? wrapDecl).get (by decide +kernel)

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

def movedDecl : Declaration := {wrapDecl with requirements := [siblingClause,authoredClause]}
def movedEnv : Environment := (env? movedDecl).get (by decide +kernel)
def movedCore : GeneralDeclarativeI65.State :=
  {core with current := {core.current with environment := movedEnv}}
def movedUse : Use movedCore.current.environment listCtor 1 :=
  (readUse movedCore.current.environment listCtor 1).get (by decide +kernel)
def movedPlan : B6MixedRhs401 movedCore false
    (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit parentOut))) :=
  invariantUnaryValuePlan432 listCtor binder.name param movedUse (by decide +kernel) (by decide +kernel) rfl rfl

/-- The Bool toggles recomputing the real B6 occurrence at the moved
authored source clause. Both branches keep roles, ordinals of the
declarations, explicit original bodies and named physical destinations. -/
def movedAtlas (reflect : Bool) : B6OccurrenceAtlas401 movedCore := ⟨fun q ordinal i body =>
  if q.occurrence == (if reflect then [72,1] else [72,0]) && ordinal == 1 && i.val == 0 then
    if h : body = .explicit containerOut then
      some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 movedCore false
        (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit containerOut)))))
    else none
  else if q.occurrence == (if reflect then [72,0] else [72,1]) && ordinal == 2 && i.val == 0 then
    if h : body = .explicit siblingOut then
      some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 movedCore false
        (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit siblingOut)))))
    else none
  else if q.occurrence == [72] && ordinal == 0 && i.val == 0 then
    if h : body = .explicit parentOut then some (h.symm ▸ movedPlan) else none
  else none⟩

def movedSource : AuthoredBodyFrame393 movedCore wrapRequest :=
  ⟨0,movedDecl,by decide +kernel,by decide +kernel,originalPlacement,wrapFrame.input⟩

def relocatedProducer : Request :=
  ((frameWhereKids400 movedSource)[1]?).get (by decide +kernel)
def relocatedSibling : Request :=
  ((frameWhereKids400 movedSource)[0]?).get (by decide +kernel)

def relocateReport (orig : Result) (occ : List Nat) : Result :=
  {orig with writes := orig.writes.map fun w => {w with occurrence := occ}}
def movedProducerReport : Result := relocateReport exactChildReport [72,1]
def movedSiblingReport : Result := relocateReport exactSiblingReport [72,0]

def movedProducer (aligned : Bool) : Problem :=
  ⟨⟨movedCore,movedAtlas aligned⟩,relocatedProducer⟩
def movedSibling (aligned : Bool) : Problem :=
  ⟨⟨movedCore,movedAtlas aligned⟩,relocatedSibling⟩

theorem moved_source_keeps_both_targets_and_input433 :
    relocatedProducer.occurrence = [72,1] ∧ relocatedProducer.demand.arguments = [point 0] ∧
      relocatedProducer.demand.outputs = [⟨3,4⟩] ∧
    relocatedSibling.occurrence = [72,0] ∧ relocatedSibling.demand.arguments = [point 0] ∧
      relocatedSibling.demand.outputs = [⟨5,4⟩] :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def siblingWitness : StructuralWhere431.Witness :=
  .previous (.previous (.previous (.previous (.explicitPick siblingWire))))

theorem typed_atlas_cannot_keep_stale_occurrences_after_original_swap433 :
    check (movedProducer false) movedProducerReport (.previous childWitness) = false ∧
    check (movedSibling false) movedSiblingReport
      (.previous siblingWitness) = false := by
  decide +kernel

theorem exact_reindexed_typed_reads_both_pass_old_paths433 :
    check (movedProducer true) movedProducerReport (.previous childWitness) = true ∧
    check (movedSibling true) movedSiblingReport (.previous siblingWitness) = true := by
  decide +kernel

theorem stale_report_cannot_replace_actual_moved_occurrence433 :
    check (movedProducer true) exactChildReport (.previous childWitness) = false ∧
    check (movedSibling true) exactSiblingReport (.previous siblingWitness) = false := by
  decide +kernel

theorem actual_moved_child_reports_keep_fixed_same_model_meaning433
    (m : I72.Model) (fit : Fits (movedProducer true).state m) :
    ReportEvidence (movedProducer true).state m relocatedProducer movedProducerReport ∧
    ReportEvidence (movedSibling true).state m relocatedSibling movedSiblingReport :=
  ⟨(check_sound (movedProducer true) movedProducerReport (.previous childWitness)
      exact_reindexed_typed_reads_both_pass_old_paths433.1).2 m fit,
   (check_sound (movedSibling true) movedSiblingReport (.previous siblingWitness)
      exact_reindexed_typed_reads_both_pass_old_paths433.2).2 m fit⟩

#print axioms moved_source_keeps_both_targets_and_input433
#print axioms typed_atlas_cannot_keep_stale_occurrences_after_original_swap433
#print axioms exact_reindexed_typed_reads_both_pass_old_paths433
#print axioms stale_report_cannot_replace_actual_moved_occurrence433
#print axioms actual_moved_child_reports_keep_fixed_same_model_meaning433
end Yulang.GeneralDeclarativeI65.I72.WrapMovedAudit433
