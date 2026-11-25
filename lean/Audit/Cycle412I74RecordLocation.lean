import Yulang.GeneralDeclarativeI65I74RecordLocation412

namespace Yulang.GeneralDeclarativeI65.I72.RecordK2412.LocationControls
open GeneralDeclarativeI65 (B6OccurrenceAtlas401)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty Equivalent record)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def implCheck : Declaration :=
  ⟨218,19,[closedHead412 20 21 9 3],[⟨6,19,[closedWhere412 20 9 3],[]⟩],[],[]⟩
def surface : InputBundle :=
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,[implCheck]⟩
def outerRow : Equation := recordRow412 0 20 1
def loopRow : Equation := recordRow412 1 21 1
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[outerRow,loopRow]⟩
def request : Demand := ⟨19,[⟨0,0,0⟩],[]⟩
def problem : Option Problem := do
  let graph ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile surface
  let environment : Environment := ⟨0,0,0,bodies,graph,source⟩
  let core : GeneralDeclarativeI65.State :=
    ⟨⟨environment,ordinary,[]⟩,[],[⟨0,[32],recordInput412 20 1⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 core := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨core,atlas⟩,⟨[71],request⟩⟩

def wire : FieldWire := ⟨0,0,⟨[0,1],[0,1]⟩,⟨⟨1,.same,1⟩,[],.same⟩⟩
def expected : Result := Check408.rawReport
def test (p : Option Problem := problem) (r : Result := expected)
    (w : Witness := .fieldCycle wire) : Bool := (p.map fun q => check q r w).getD false

def atOriginal : FieldLocation := ⟨[71],218,0,20,0,1⟩
theorem x10_location_is_original_head_field412 :
    (problem.bind fun p => locate p expected wire) = some atOriginal := by decide +kernel
theorem x10_location_cannot_be_made_from_a_where_report412 :
    (problem.bind fun p => locate p (WhereCycle411.expected411 implCheck) wire) = none := by decide +kernel
#eval problem.bind fun p => locate p expected wire
#print axioms location_exists_exactly_for_field_branch412
#print axioms located_record_diagnostic_keeps_actual_path412
#print axioms x10_location_is_original_head_field412
#print axioms x10_location_cannot_be_made_from_a_where_report412
end Yulang.GeneralDeclarativeI65.I72.RecordK2412.LocationControls
