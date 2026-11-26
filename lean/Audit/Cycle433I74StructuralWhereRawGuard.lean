import Yulang.GeneralDeclarativeI65I74StructuralWhereReceiptRefinement433
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapRawAudit433
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

def extendAt (atRoot : Nat) : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [⟨atRoot,.variant 90 (.variable atRoot)⟩]}

def shiftedCore (g : GeneralDeclarativeHead320.State) : GeneralDeclarativeI65.State :=
  {core with current := {core.current with ordinary := g}}

def shiftedParentPlan (g : GeneralDeclarativeHead320.State) : B6MixedRhs401 (shiftedCore g) false
    (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit parentOut))) :=
  invariantUnaryValuePlan432 listCtor binder.name param nominalUse
    (by change GeneralDeclarativeWitnessSparseIntervals357.names nominalUse.mode 1 = some [param]; decide +kernel)
    (by change core.modes[listCtor]? = some [param]; decide +kernel) rfl rfl

def shiftedAtlas (g : GeneralDeclarativeHead320.State) : B6OccurrenceAtlas401 (shiftedCore g) :=
  ⟨fun q ordinal i body =>
    if q.occurrence == [72,0] && ordinal == 1 && i.val == 0 then
      if h : body = .explicit containerOut then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 (shiftedCore g) false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit containerOut)))))
      else none
    else if q.occurrence == [72] && ordinal == 0 && i.val == 0 then
      if h : body = .explicit parentOut then some (h.symm ▸ shiftedParentPlan g) else none
    else none⟩

def shiftedState (g : GeneralDeclarativeHead320.State) : I72.State := ⟨shiftedCore g,shiftedAtlas g⟩
def cyclicRequest (n : Nat) : Problem := ⟨shiftedState (extendAt n),wrapRequest⟩

theorem added_variant_is_a_real_raw_cycle433 (i : Nat) :
    GeneralDeclarativeK2Alias321.AliasCycle (extendAt i)
      (GeneralDeclarativeGraphRows321.observed (extendAt i)) i := by
  have present : (⟨i,.variant 90 (.variable i)⟩ : Equation) ∈ (extendAt i).equations := by
    simp [extendAt]
  refine ⟨i,i,⟨.variant 90 i,GeneralDeclarativeGraphRows321.literal_head present rfl,?_⟩,
    .refl _,GeneralDeclarativeLowerKnown321.alias_refl _⟩
  simp [GeneralDeclarativeK2Graph321.Shape.children]

theorem original_supported_wrap_with_real_caller_K2_is_not_selected433 :
    RootCycle (cyclicRequest 6).state wrapRequest ∧
    check (cyclicRequest 6) actualReport (.associatedWrap input) = false := by
  refine ⟨⟨point 6,by simp [wrapRequest],added_variant_is_a_real_raw_cycle433 6⟩,?_⟩
  decide +kernel

private def outside (w : List410.ExactEscapeWire) : List410.ExactEscapeWire :=
  ⟨w.ranks ++ [13],w.palette ++ [2]⟩

def offSiteData : AssociatedWire432 :=
  ⟨input.parentDeclaration,input.parentHeadRow,input.parentOutputRow,outside input.parentEscape,
    ⟨input.child.rows,input.child.declaration,input.child.outputRow,outside input.child.rootEscape⟩⟩

theorem same_actual_wrap_still_checks_with_irrelevant_raw_cycle433 :
    GeneralDeclarativeK2Alias321.AliasCycle (extendAt 13)
      (GeneralDeclarativeGraphRows321.observed (extendAt 13)) 13 ∧
    check (cyclicRequest 13) actualReport (.associatedWrap offSiteData) = true :=
  ⟨added_variant_is_a_real_raw_cycle433 13,by decide +kernel⟩

private def offMuBody : CommonNominalSyntax.State Common.Row := .block [.variant 90 (.inl 0)] 0
private def offMu : Ty := .variant 90 offMuBody
private theorem off_mu_folds433 : Equivalent offMu (CommonNominalFullCarrier.variant 90 offMu) := by
  have same (k : Nat) : CommonNominalFullCarrier.observeTy k offMu =
      CommonNominalFullCarrier.observeTy k (CommonNominalFullCarrier.variant 90 offMu) := by
    cases k <;> rfl
  constructor <;> intro k <;> rw [←same k] <;> exact CommonNominalFullDemand.producerLe_refl _

def actualResidual : Ty := record 21 (.base .str) .emptyRecord
def actualRecord : Ty := record 20 (.base .int) actualResidual
def fittingOffRoute : I72.Model :=
  ⟨fun n => ((if n = 0 then actualRecord else if n = 2 then .base .str
                  else if n = 3 then actualResidual else if n = 6 then nominal listCtor [.inl actualRecord]
                  else if n = 12 then nominal listCtor [.inl (.base .int)]
                  else if n = 13 then offMu else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (wholeOriginal 20 1 21 2) else none⟩

theorem actual_off_route_model_fits433 : Fits (cyclicRequest 13).state fittingOffRoute := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [rootRow,xRow,yRow,tailRow,splitRow,keptItem,parentHeadRow,parentOutRow,
      ⟨13,.variant 90 (.variable 13)⟩] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨subtype_refl _,subtype_refl _⟩ | exact off_mu_folds433
  · intro _ h; cases h
  · intro _ h
    cases List.mem_singleton.mp h
    rfl

theorem off_route_literal_report_has_same_fitting_model433 :
    Classifies R16 (cyclicRequest 13).state wrapRequest actualReport.verdict ∧
    ReportEvidence (cyclicRequest 13).state fittingOffRoute wrapRequest actualReport :=
  let good := verified_R16_result_classifies_in_same_State432 (cyclicRequest 13) actualReport
    (.associatedWrap offSiteData) same_actual_wrap_still_checks_with_irrelevant_raw_cycle433.2
  ⟨good.1,good.2 _ actual_off_route_model_fits433⟩

#print axioms added_variant_is_a_real_raw_cycle433
#print axioms original_supported_wrap_with_real_caller_K2_is_not_selected433
#print axioms same_actual_wrap_still_checks_with_irrelevant_raw_cycle433
#print axioms actual_off_route_model_fits433
#print axioms off_route_literal_report_has_same_fitting_model433
end Yulang.GeneralDeclarativeI65.I72.WrapRawAudit433
