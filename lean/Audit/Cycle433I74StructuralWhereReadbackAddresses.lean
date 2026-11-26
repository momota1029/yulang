import Yulang.GeneralDeclarativeI65I74StructuralWhereReceiptRefinement433
import Yulang.GeneralDeclarativeI65I74ExplicitPickMeaning419

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.WrapWireReadbackAudit433
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
def aliasRow : Equation := ⟨14,.variable 1⟩
def sameValueAlternative : Equation := ⟨12,.nominal listCtor [.variable 14]⟩
def qualifiedRaw : GeneralDeclarativeHead320.State :=
  {raw with equations := raw.equations ++ [aliasRow,sameValueAlternative]}

def qualifiedProblem : Problem := ⟨shiftedState qualifiedRaw,wrapRequest⟩
private def withAlias (cert : List410.ExactEscapeWire) : List410.ExactEscapeWire :=
  ⟨cert.ranks ++ [13,1],cert.palette ++ [2,2]⟩

def exactWire : AssociatedWire432 :=
  ⟨0,6,7,withAlias input.parentEscape,
    ⟨input.child.rows,input.child.declaration,input.child.outputRow,withAlias input.child.rootEscape⟩⟩

def exactAlternateWire : AssociatedWire432 :=
  ⟨0,6,9,withAlias input.parentEscape,
    ⟨input.child.rows,input.child.declaration,8,withAlias input.child.rootEscape⟩⟩

def alternativeParentWrite : Check408.Write :=
  ⟨[72],0,0,⟨6,12⟩,.explicit parentOut,.node 4 [40] [.node 10 [0,2,9,14,14,14] []]⟩
def alternativeChildWrite : Check408.Write :=
  ⟨[72,0],1,0,⟨3,14⟩,.explicit containerOut,.node 0 [8,1,1,1] []⟩
def literalAlternativeReport : Result :=
  {actualReport with writes := [alternativeParentWrite,alternativeChildWrite]}

theorem consistent_original_requests_can_keep_two_distinct_readback_addresses433 :
    check qualifiedProblem actualReport (.associatedWrap exactWire) = true ∧
    check qualifiedProblem literalAlternativeReport (.associatedWrap exactAlternateWire) = true := by
  decide +kernel

theorem actual_same_dictionary_does_not_make_the_two_literal_reports_equal433 :
    literalAlternativeReport.verdict = actualReport.verdict ∧
    literalAlternativeReport ≠ actualReport := by
  refine ⟨rfl,?_⟩
  intro h
  have eq : literalAlternativeReport.writes[1]?.map (fun w => w.target.target) =
      actualReport.writes[1]?.map (fun w => w.target.target) :=
    congrArg (fun t : Result => t.writes[1]?.map (fun w => w.target.target)) h
  have impossible : (14 : Nat) = 4 := Option.some.inj eq
  omega

theorem opposite_literal_receipts_are_not_interchangeable433 :
    check qualifiedProblem actualReport (.associatedWrap exactAlternateWire) = false ∧
    check qualifiedProblem literalAlternativeReport (.associatedWrap exactWire) = false := by
  decide +kernel

def actualResidual : Ty := record 21 (.base .str) .emptyRecord
def actualRecord : Ty := record 20 (.base .int) actualResidual
def qualifiedModel : I72.Model :=
  ⟨fun n => ((if n = 0 then actualRecord else if n = 2 then .base .str
                  else if n = 3 then actualResidual else if n = 6 then nominal listCtor [.inl actualRecord]
                  else if n = 12 then nominal listCtor [.inl (.base .int)] else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (wholeOriginal 20 1 21 2) else none⟩

theorem aliases_physically_share_one_fitting_value433 :
    Fits qualifiedProblem.state qualifiedModel ∧
    qualifiedRaw.equations[7]? = some parentOutRow ∧
    qualifiedRaw.equations[9]? = some sameValueAlternative ∧
    parentOutRow.left = sameValueAlternative.left ∧
    GeneralDeclarativeWitnessLiteral349.eqExpr parentOutRow.right sameValueAlternative.right = false ∧
    qualifiedModel.assignment 4 = qualifiedModel.assignment 14 := by
  refine ⟨?_,rfl,rfl,rfl,by decide +kernel,rfl⟩
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro row h
    change row ∈ [rootRow,xRow,yRow,tailRow,splitRow,keptItem,parentHeadRow,parentOutRow,
      aliasRow,sameValueAlternative] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ h; cases h
  · intro _ h
    cases List.mem_singleton.mp h
    rfl

theorem both_literal_receipts_have_evidence_in_one_fitting_model433 :
    Fits qualifiedProblem.state qualifiedModel ∧
    ReportEvidence qualifiedProblem.state qualifiedModel wrapRequest actualReport ∧
    ReportEvidence qualifiedProblem.state qualifiedModel wrapRequest literalAlternativeReport := by
  have fit := aliases_physically_share_one_fitting_value433.1
  exact ⟨fit,
    (check_sound qualifiedProblem actualReport (.associatedWrap exactWire)
      consistent_original_requests_can_keep_two_distinct_readback_addresses433.1).2 _ fit,
    (check_sound qualifiedProblem literalAlternativeReport (.associatedWrap exactAlternateWire)
      consistent_original_requests_can_keep_two_distinct_readback_addresses433.2).2 _ fit⟩

/-- The counterexample does not make the checker nondeterministic
for one wire. A successful exact replay packet determines a single
literal output report; this is separate from global allocator identity. -/
theorem one_readback_wire_has_at_most_one_literal_report433
    (p : Problem) (w : AssociatedWire432) (a b : Result)
    (yes : check p a (.associatedWrap w) = true)
    (also : check p b (.associatedWrap w) = true) : a = b := by
  obtain ⟨x,hx,ax⟩ := checked_associated_report_replays_actual_data433 yes
  obtain ⟨y,hy,by'⟩ := checked_associated_report_replays_actual_data433 also
  have agree := Option.some.inj (hx.symm.trans hy)
  exact ax.trans ((congrArg ReadAssociatedWrap432.report agree).trans by'.symm)

#print axioms one_readback_wire_has_at_most_one_literal_report433
#print axioms consistent_original_requests_can_keep_two_distinct_readback_addresses433
#print axioms actual_same_dictionary_does_not_make_the_two_literal_reports_equal433
#print axioms opposite_literal_receipts_are_not_interchangeable433
#print axioms both_literal_receipts_have_evidence_in_one_fitting_model433
end Yulang.GeneralDeclarativeI65.I72.WrapWireReadbackAudit433
