import Yulang.GeneralDeclarativeI65I74MixedRecordEntry413

namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413.SpecX11
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

theorem x11_both_actual_orders_report_K2_413 :
    checkOpt normal = true ∧ checkOpt reversed = true := by decide +kernel

theorem x11_two_other_safe_matches_do_not_mask_K2_413 :
    checkOpt three = true ∧ checkOpt (build [inspecting,bindingOther,bindingOnly]) = true ∧
    checkOpt (build [bindingOther,bindingOnly,inspecting]) = true := by decide +kernel

def observedOrdinal (p : Option Problem) : Option (Nat × Nat) := do
  let actual ← p
  let packet ← replayMixed413 actual wire
  pure (packet.rejection.tape.opening.ordinal,packet.rejection.tape.opening.decl.id)

theorem x11_actual_deep_ordinal_tracks_visible_order413 :
    observedOrdinal normal = some (1,57) ∧ observedOrdinal reversed = some (0,57) ∧
    observedOrdinal three = some (1,57) := by decide +kernel

def rootReturn : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ⟨1,.variable 0⟩ :: ordinary.equations}
def oldRootWire : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,⟨1,.same,1⟩,[],.forward 0⟩
def wrongSite : MixedWire := {wire with path := ⟨⟨1,.same,2⟩,[],.same⟩}
def noCycle : GeneralDeclarativeHead320.State := {ordinary with equations := [outer]}
def offPathCycle : GeneralDeclarativeHead320.State := {ordinary with equations := [outer,recordRow412 2 21 2]}
def malformed : Declaration := {bindingOnly with id := 59,head := [.var 9]}
def duplicated : Declaration := {bindingOther with id := bindingOnly.id}

theorem x11_cannot_hide_visible_rows_or_forge_K2_413 :
    checkOpt (build [bindingOnly,bindingOther]) = false ∧
    checkOpt (build [inspecting]) = false ∧
    checkOpt (build [bindingOnly,inspecting,malformed]) = false ∧
    checkOpt (build [bindingOnly,inspecting,duplicated]) = false ∧
    checkOpt (build [bindingOnly,inspecting] noCycle) = false ∧
    checkOpt (build [bindingOnly,inspecting] offPathCycle) report (.mixedHead wrongSite) = false ∧
    checkOpt normal (Check408.nullaryReport bindingOnly) = false ∧
    checkOpt normal (WhereCycle411.expected411 inspecting) = false := by decide +kernel

theorem x11_actual_parent_priority_still_separate413 :
    checkOpt (build [bindingOnly,inspecting] rootReturn)
        report (.mixedHead {wire with root := {wire.root with outerRow := 1}}) = false ∧
    checkOpt (build [bindingOnly,inspecting] rootReturn)
        report (.previous (.previous (.previous (.previous (.previous (.rawRoot oldRootWire)))))) = true := by
  decide +kernel

def muBlock : CommonNominalSyntax.State Common.Row :=
  .block [.record 21 (.inl 0) .emptyRecord] 0
def mu : Ty := .record 21 muBlock .emptyRecord

theorem recursive_record_unfolds413 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth mu =
      CommonNominalFullCarrier.observeTy depth (record 21 mu .emptyRecord) := by
  cases depth <;> rfl

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then record 20 mu .emptyRecord else mu),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (recordInput412 20 1) else none⟩

theorem actual_X11_snapshot_fits413 {p : Problem} {rows : List Declaration} (ready : build rows = some p) :
    I72.Fits p.state model := by
  unfold build at ready
  cases sem : compile bodies with
  | none => simp [sem] at ready
  | some graph =>
    cases source : GeneralSourceMetadataBareBundle291.compile (surface rows) with
    | none => simp [sem,source] at ready
    | some bundle =>
      simp only [sem,source,Option.pure_def] at ready
      cases ready
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ empty; cases empty
      · intro _ empty; cases empty
      · intro e member
        have choices : e = outer ∨ e = cycle := by
          simpa only [ordinary,List.mem_cons,List.not_mem_nil,or_false] using member
        rcases choices with rfl|rfl
        · exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
        · change Equivalent mu (record 21 mu .emptyRecord)
          constructor <;> intro n <;> rw [← recursive_record_unfolds413 n] <;>
            exact CommonNominalFullDemand.producerLe_refl _
      · intro _ empty; cases empty
      · intro o exactOrigin
        obtain rfl := List.mem_singleton.mp exactOrigin
        rfl

theorem executed_X11_has_genuine_same_model_evidence413 (rows : List Declaration)
    (yes : checkOpt (build rows) = true) :
    ∃ p, build rows = some p ∧ I72.Fits p.state model ∧ ReportEvidence p.state model p.root report := by
  unfold checkOpt at yes
  cases ready : build rows with
  | none => simp [ready] at yes
  | some p =>
    have matchResult : check p report (.mixedHead wire) = true := by simpa [ready] using yes
    have fit := actual_X11_snapshot_fits413 ready
    exact ⟨p,rfl,fit,(check_sound p report _ matchResult).2 model fit⟩

theorem X11_all_checked_input_orders_have_report_evidence413 :
    (∃ p, normal = some p ∧ I72.Fits p.state model ∧ ReportEvidence p.state model p.root report) ∧
    (∃ p, reversed = some p ∧ I72.Fits p.state model ∧ ReportEvidence p.state model p.root report) ∧
    (∃ p, three = some p ∧ I72.Fits p.state model ∧ ReportEvidence p.state model p.root report) :=
  ⟨executed_X11_has_genuine_same_model_evidence413 _ x11_both_actual_orders_report_K2_413.1,
   executed_X11_has_genuine_same_model_evidence413 _ x11_both_actual_orders_report_K2_413.2,
   executed_X11_has_genuine_same_model_evidence413 _ x11_two_other_safe_matches_do_not_mask_K2_413.1⟩

#eval [checkOpt normal,checkOpt reversed,checkOpt three,
  checkOpt (build [bindingOnly,bindingOther]),checkOpt (build [inspecting]),
  checkOpt (build [bindingOnly,inspecting,malformed]),checkOpt (build [bindingOnly,inspecting] noCycle),
  checkOpt (build [bindingOnly,inspecting] rootReturn)
    report (.previous (.previous (.previous (.previous (.previous (.rawRoot oldRootWire))))))]
#eval [observedOrdinal normal,observedOrdinal reversed,observedOrdinal three]

#print axioms x11_both_actual_orders_report_K2_413
#print axioms x11_two_other_safe_matches_do_not_mask_K2_413
#print axioms x11_actual_deep_ordinal_tracks_visible_order413
#print axioms x11_cannot_hide_visible_rows_or_forge_K2_413
#print axioms x11_actual_parent_priority_still_separate413
#print axioms actual_X11_snapshot_fits413
#print axioms executed_X11_has_genuine_same_model_evidence413
#print axioms X11_all_checked_input_orders_have_report_evidence413
end Yulang.GeneralDeclarativeI65.I72.MixedRecord413.SpecX11
