import Yulang.GeneralDeclarativeI65I74StructuralWherePairBindings433
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapPairBindingAudit433
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

def validatedPair : ReadTwoNamedWrap433 caller :=
  (readTwoNamedWrap433 caller wire).get (by decide +kernel)

theorem actual_read_dual_source_uses_original_fixed_addresses433 :
    validatedPair.first.retained.write.occurrence = [72,0] ∧
    validatedPair.second.retained.write.occurrence = [72,1] ∧
    validatedPair.first.retained.write.target = ⟨3,4⟩ ∧
    validatedPair.second.retained.write.target = ⟨5,4⟩ ∧
    validatedPair.first.retained.expr = validatedPair.second.retained.expr := by
  have positions := two_child_packet_retains_exact_original_output_bindings433 validatedPair
  refine ⟨positions.1,positions.2.1,?_,?_,two_child_same_fixed_slot_has_same_retained_literal433 validatedPair⟩
  · have before : validatedPair.original.origin.output = ⟨3,4⟩ := by decide +kernel
    exact positions.2.2.2.2.1.trans before
  · cases h : validatedPair.second.retained.write.target with
    | mk key dest =>
      have exactKey : key = 5 := (by
        have e := positions.2.2.2.2.2.1
        rw [h] at e
        exact e.trans (by decide +kernel))
      have exactDest : dest = 4 := (by
        have e := positions.2.2.2.2.2.2
        rw [h] at e
        exact e.trans (by decide +kernel))
      simp [exactKey,exactDest]

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

theorem actual_pair_read_has_nonvacuous_same_model_dictionary433 :
    I72.Fits state fittingModel ∧
      DictionaryEvidence state fittingModel wrapRequest (.node 218 [.node 57 [],.node 58 []]) := by
  have same : GeneralDeclarativeWitnessTree349.eqResult
    (.selected validatedPair.dictionary) (.selected (.node 218 [.node 57 [],.node 58 []])) = true := by
    decide +kernel
  have verdict := (GeneralDeclarativeWitnessTree349.eq_result _ _).mp same
  have dict : validatedPair.dictionary = .node 218 [.node 57 [],.node 58 []] := by
    injection verdict
  exact ⟨child_receipt_control_has_fitting_model432,dict ▸ read_pair_same_model_dictionary433
    validatedPair fittingModel child_receipt_control_has_fitting_model432⟩

#print axioms two_child_packet_retains_exact_original_output_bindings433
#print axioms two_child_same_fixed_slot_has_same_retained_literal433
#print axioms actual_read_dual_source_uses_original_fixed_addresses433
#print axioms actual_pair_read_has_nonvacuous_same_model_dictionary433
end Yulang.GeneralDeclarativeI65.I72.WrapPairBindingAudit433
