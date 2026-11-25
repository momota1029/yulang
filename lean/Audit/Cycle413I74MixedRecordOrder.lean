import Yulang.GeneralDeclarativeI65I74MixedRecordConservative413

namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413.OrderControls
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible SourceHead)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty Equivalent record)
open RecordK2412 (closedWhere412 closedHead412 recordInput412 recordRow412)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def bindingOnly : Declaration := ⟨56,7,[closedWhere412 20 9 3],[],[],[]⟩
def bindingOther : Declaration := ⟨58,7,[closedWhere412 20 9 13],[],[],[]⟩
def inspecting : Declaration := ⟨57,7,[closedHead412 20 21 9 8],[],[],[]⟩

def surface (rows : List Declaration) : InputBundle :=
  let primitives : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,primitives⟩,⟨.absent,primitives⟩,⟨0,[⟨7,1,[]⟩]⟩,rows⟩

def outer : Equation := recordRow412 0 20 1
def cycle : Equation := recordRow412 1 21 1
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[outer,cycle]⟩

def build (rows : List Declaration) (raw : GeneralDeclarativeHead320.State := ordinary) :
    Option Problem := do
  let program ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile (surface rows)
  let environment : Environment := ⟨0,0,0,bodies,program,source⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨environment,raw,[]⟩,[],[⟨0,[22],recordInput412 20 1⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩],[]⟩⟩⟩

def wire : MixedWire := ⟨⟨0,0,⟨[0,1],[0,1]⟩⟩,⟨⟨1,.same,1⟩,[],.same⟩⟩
def report : Result := Check408.rawReport
def checkOpt (p : Option Problem) (r : Result := report) (w : Witness := .mixedHead wire) : Bool :=
  (p.map fun data => check data r w).getD false

def normal := build [bindingOnly,inspecting]
def reversed := build [inspecting,bindingOnly]
def three := build [bindingOnly,inspecting,bindingOther]

def allOrders : List (List Declaration) :=
  [[bindingOnly,inspecting,bindingOther], [bindingOnly,bindingOther,inspecting],
   [inspecting,bindingOnly,bindingOther], [inspecting,bindingOther,bindingOnly],
   [bindingOther,bindingOnly,inspecting], [bindingOther,inspecting,bindingOnly]]

def located (rows : List Declaration) : Option MixedLocation :=
  (build rows).bind fun p => locate p report wire

theorem x11_with_two_other_matching_declarations_in_every_order413 :
    allOrders.all (fun rows => checkOpt (build rows)) = true := by decide +kernel

theorem full_actual_locations_retain_every_source_order413 :
    allOrders.map located =
      [some ⟨[61],[56,57,58],1,57,20,0,1⟩,some ⟨[61],[56,58,57],2,57,20,0,1⟩,
       some ⟨[61],[57,56,58],0,57,20,0,1⟩,some ⟨[61],[57,58,56],0,57,20,0,1⟩,
       some ⟨[61],[58,56,57],2,57,20,0,1⟩,some ⟨[61],[58,57,56],1,57,20,0,1⟩] := by
  decide +kernel

theorem three_row_example_has_two_actual_matching_heads_and_K2_413 {p : Problem}
    (got : three = some p) :
    ∃ v : MixedVerified p, replayMixed413 p wire = some v ∧
      ∃ (i j : Nat) (d e : Declaration), Rival413 v.rejection i d ∧ Rival413 v.rejection j e ∧ d.id ≠ e.id := by
  have trueTest : checkOpt three = true := by decide +kernel
  unfold checkOpt at trueTest
  simp only [got,Option.map_some,Option.getD_some] at trueTest
  obtain ⟨v,replay,_⟩ := checked_mixed_head_reflects_original413 p report wire trueTest
  have allRows : visible p.state.core p.root = [bindingOnly,inspecting,bindingOther] := by
    unfold three build at got
    cases sem : compile bodies with
    | none => simp [sem] at got
    | some graph =>
      cases found : GeneralSourceMetadataBareBundle291.compile
            (surface [bindingOnly,inspecting,bindingOther]) with
      | none => simp [sem,found] at got
      | some table =>
        simp only [sem,found,Option.pure_def] at got
        cases got
        have exact : table.declarations = [bindingOnly,inspecting,bindingOther] :=
          congrArg InputBundle.declarations (GeneralSourceMetadataBareBundle291.preserves_input _ _ found).1
        change table.declarations.filter (fun d => d.role == 7) = _
        rw [exact]
        rfl
  exact ⟨v,replay,two_distinct_actual_matches_when_three413 v.rejection (by rw [allRows]; decide +kernel)⟩

#eval allOrders.map located
#print axioms full_scan_flags_exact413
#print axioms full_scan_shape_independent_of_order413
#print axioms mixed_scan_recovers_tape_after_permutation413
#print axioms actual_rival_cannot_be_missing413
#print axioms two_distinct_actual_matches_when_three413
#print axioms same_exact_report_controls_location413
#print axioms checked_location_is_original_candidate_and_visit413
#print axioms same_tape_and_trace_before_models413
#print axioms previous_success_trace413
#print axioms selected_exact_reports_conservative413
#print axioms selected_classification_conservative413
#print axioms x11_with_two_other_matching_declarations_in_every_order413
#print axioms full_actual_locations_retain_every_source_order413
#print axioms three_row_example_has_two_actual_matching_heads_and_K2_413
end Yulang.GeneralDeclarativeI65.I72.MixedRecord413.OrderControls
