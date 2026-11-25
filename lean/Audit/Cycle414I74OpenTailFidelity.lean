import Yulang.GeneralDeclarativeI65I74OpenTailFidelity414

namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414.FidelityX4
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty Equivalent record)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def original : Declaration := ⟨57,7,[openHead 20 9 8],[tailRequirement 7 8 66],[],[]⟩

def surface (rows : List Declaration) : InputBundle :=
  let primitives : List Row := [⟨9,some ⟨[],9⟩,.primitive (.scalar .int)⟩]
  ⟨⟨.absent,primitives⟩,⟨.absent,primitives⟩,⟨0,[⟨7,1,[]⟩]⟩,rows⟩

def raw : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[openRow 0 20 1 2,intRow 1]⟩

def build (rows : List Declaration := [original]) (ordinary : GeneralDeclarativeHead320.State := raw)
    (origins : List GeneralDeclarativeI65.Origin := [⟨0,[22],openTerm 20 1 2⟩]) :
    Option Problem := do
  let program ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile (surface rows)
  let environment : Environment := ⟨0,0,0,bodies,program,source⟩
  let s : GeneralDeclarativeI65.State := ⟨⟨environment,ordinary,[]⟩,[],origins,[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩],[]⟩⟩⟩

def wire : OpenWire := ⟨0,⟨[0,1,2],[0,1,1]⟩⟩
def checkOpt (p : Option Problem) (r : Result := pendingReport) (w : Witness := .openTail wire) :
    Bool := (p.map fun q => check q r w).getD false

def coordinates (p : Option Problem) (w : OpenWire := wire) : Option PendingLocation := do
  let p ← p
  locate p w

def withExtraOrigin : Option Problem := build [original] raw [
  ⟨41,[93],.ordinary (.base .int)⟩,⟨0,[22],openTerm 20 1 2⟩]

theorem actual_X4_pending_keeps_input_and_clause_coordinates414 :
    coordinates build = some ⟨[61],7,57,66,0,20,1,2,8⟩ ∧
    coordinates withExtraOrigin {wire with original := 1} =
      some ⟨[61],7,57,66,0,20,1,2,8⟩ ∧
    coordinates withExtraOrigin = none := by decide +kernel

def givenBadRoute : Option Problem := do
  let p ← build
  let s : GeneralDeclarativeI65.State :=
    {p.state.core with routes := [⟨2,1,[66]⟩]}
  pure ⟨⟨s,⟨fun _ _ _ _ => none⟩⟩,p.root⟩
def givenNativeRow : Option Problem := do
  let p ← build
  let s : GeneralDeclarativeI65.State :=
    {p.state.core with current := {p.state.core.current with visible := [⟨1,90,2,[]⟩]}}
  pure ⟨⟨s,⟨fun _ _ _ _ => none⟩⟩,p.root⟩
def givenExtraTarget : Option Problem := do
  let p ← build
  pure {p with root := {p.root with demand := {p.root.demand with outputs := [⟨3,53⟩]}}}
def givenNonpoint : Option Problem := do
  let p ← build
  pure {p with root := {p.root with demand := {p.root.demand with arguments := [⟨0,0,2⟩]}}}
def wrongChild : Declaration := {original with requirements := [tailRequirement 7 17 66]}
def wrongField : Declaration := {original with head := [openHead 22 9 8]}

theorem no_pending_evidence_from_unrepresented_source_authorities414 :
    checkOpt givenBadRoute = false ∧ checkOpt givenNativeRow = false ∧
    checkOpt givenExtraTarget = false ∧ checkOpt givenNonpoint = false ∧
    checkOpt (build [wrongChild]) = false ∧ checkOpt (build [wrongField]) = false := by decide +kernel

#eval [coordinates build,coordinates withExtraOrigin,coordinates withExtraOrigin {wire with original := 1}]
#eval [checkOpt givenBadRoute,checkOpt givenNativeRow,checkOpt givenExtraTarget,checkOpt givenNonpoint,
  checkOpt (build [wrongChild]),checkOpt (build [wrongField])]

#print axioms literal_open_coordinates_cohere414
#print axioms exact_checked_open_locations_are_coherent414
#print axioms two_wires_cannot_reassign_the_checked_tail414
#print axioms no_pending_trace_can_issue_a_where_or_fixed_write414
#print axioms actual_X4_pending_keeps_input_and_clause_coordinates414
#print axioms no_pending_evidence_from_unrepresented_source_authorities414

end Yulang.GeneralDeclarativeI65.I72.OpenTail414.FidelityX4
