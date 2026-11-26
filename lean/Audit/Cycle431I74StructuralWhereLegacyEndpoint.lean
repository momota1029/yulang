import Yulang.GeneralDeclarativeI65I74StructuralWhereEntry431
import Yulang.GeneralDeclarativeI65I74RecordEndpointsRuleBoundary422

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1800

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.LegacyR14Spec431
open GeneralDeclarativeI65
open CommonNominalFullCarrier (Equivalent Ty)

open Checker408 (Problem Result)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open OpenTail414 (openRow openTerm)
open ExplicitPick419 (pickSyntax)
open CommonNominalFullCarrier (subtype_refl)

-- Exact C425 split-state control, re-expressed for standalone audit.
-- The source identities, original bounds and typed plan match C423.
-- Slot 10 is unused by that original fixture and is reserved for the second retained row.
def fixtureBodies425 : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def authoredBody : GeneralDeclarations.Equation := ⟨92,3,.var 8⟩
def fixtureDecl425 : Declaration := ⟨57,7,[pickSyntax 20 8 13],[],[authoredBody],[]⟩
def otherDecl425 : Declaration := ⟨58,9,[],[],[],[]⟩
def fixtureSource425 : InputBundle :=
  ⟨⟨.absent,[]⟩,⟨.absent,[]⟩,⟨1,[⟨7,1,[(3,none)]⟩,⟨9,0,[]⟩]⟩,[otherDecl425,fixtureDecl425]⟩
def originalOrigins425 : List Origin :=
  [⟨0,[44],openTerm 20 3 5⟩,⟨2,[55],openTerm 20 4 6⟩]
def splitRows : List Equation :=
  [openRow 0 20 3 5,openRow 2 20 4 6,⟨12,.variable 11⟩]
def splitAtoms : List (PresenceNormalForm.Atom Nat) :=
  [requiredLower 20 11 1,requiredUpper 20 11 1]

def actualBuild425 (rows : List Equation) (atoms : List (PresenceNormalForm.Atom Nat))
    (sources : List Origin := originalOrigins425) :
    Option Problem := do
  let program ← compile fixtureBodies425
  let bundle ← GeneralSourceMetadataBareBundle291.compile fixtureSource425
  let env : Environment := ⟨0,0,0,fixtureBodies425,program,bundle⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨env,⟨⟨atoms,[(0,1),(1,2)]⟩,rows⟩,[]⟩,[],sources,[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun q decl i body =>
    if q.occurrence == [61,423] && decl == 1 && i.val == 0 then
      if h : body = .explicit authoredBody then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 s false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit authoredBody)))))
      else none
    else none⟩
  pure ⟨⟨s,atlas⟩,⟨[61,423],⟨7,[⟨0,1,2⟩],[⟨3,12⟩]⟩⟩⟩

def splitProblem : Problem :=
  (actualBuild425 splitRows splitAtoms).get (by decide +kernel)
def sourceWire425 : RecordEndpoints422.Wire :=
  ⟨⟨0,0⟩,⟨1,1⟩,1,⟨[0,0,0,1,1,1,1,1,0,0,1,1,1],[0,1]⟩⟩
def splitInput : PrepareWire := ⟨sourceWire425,.requiredChannel ⟨2,0,1⟩⟩
def preparedSplit : PreparedWrite splitProblem :=
  (readRetainedPickWrite423 splitProblem splitInput).get (by decide +kernel)
def onlyRequired426 : ProjectedRowsWire426 := ⟨sourceWire425,⟨2,0,1⟩⟩
def exactProjectedReport426 : Result :=
  ⟨.selected 57 [],.selected (.node 57 []),[encodeProjectedWrite425 EndpointProjection426.projectedTag preparedSplit]⟩


theorem prior_endpoint_rule_survives_actual_R15_entry431 :
    StructuralWhere431.check splitProblem exactProjectedReport426
      (.previous (.projectedRecord onlyRequired426)) = true := by decide +kernel

theorem endpoint_old_path_rejects_altered_writes431 :
    StructuralWhere431.check splitProblem {exactProjectedReport426 with writes := []}
      (.previous (.projectedRecord onlyRequired426)) = false := by decide +kernel

theorem previous_R14_endpoint_classifies_actual_R15_request431 :
    I72.Classifies StructuralWhere431.R15 splitProblem.state splitProblem.root
      exactProjectedReport426.verdict :=
  (StructuralWhere431.verified_R15_result_classifies_in_same_State431 _ _ _
    prior_endpoint_rule_survives_actual_R15_entry431).1

#print axioms prior_endpoint_rule_survives_actual_R15_entry431
#print axioms endpoint_old_path_rejects_altered_writes431
#print axioms previous_R14_endpoint_classifies_actual_R15_request431

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.LegacyR14Spec431
