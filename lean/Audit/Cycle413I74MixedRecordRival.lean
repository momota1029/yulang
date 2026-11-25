import Yulang.GeneralDeclarativeI65I74MixedRecordRival413

namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413.RivalTest
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

def observedOrdinal (p : Option Problem) : Option (Nat × Nat) := do
  let actual ← p
  let packet ← replayMixed413 actual wire
  pure (packet.rejection.tape.opening.ordinal,packet.rejection.tape.opening.decl.id)

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

theorem same_X11_with_two_semantic_leaf_rivals_and_no_win413 :
    ∃ p, three = some p ∧ I72.Fits p.state model ∧
      I72.DictionaryEvidence p.state model p.root (.node 56 []) ∧
      I72.DictionaryEvidence p.state model p.root (.node 58 []) ∧
      ¬I72.Classifies R5 p.state p.root (.selected (.node 56 [])) ∧
      ¬I72.Classifies R5 p.state p.root (.selected (.node 58 [])) ∧
      ReportEvidence p.state model p.root report := by
  have actual : checkOpt three = true := by decide +kernel
  have ordinal : observedOrdinal three = some (1,57) := by decide +kernel
  unfold checkOpt at actual
  cases got : three with
  | none => simp [got] at actual
  | some p =>
    have yes : check p report (.mixedHead wire) = true := by simpa [got] using actual
    have fit := actual_X11_snapshot_fits413 got
    obtain ⟨v,replayed,_⟩ := checked_mixed_head_reflects_original413 p report wire yes
    have atOne : v.rejection.tape.opening.ordinal = 1 := by
      have pair : (v.rejection.tape.opening.ordinal,v.rejection.tape.opening.decl.id) = (1,57) := by
        simpa [observedOrdinal,got,replayed] using ordinal
      exact congrArg Prod.fst pair
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
          have eq : table.declarations = [bindingOnly,inspecting,bindingOther] :=
            congrArg InputBundle.declarations (GeneralSourceMetadataBareBundle291.preserves_input _ _ found).1
          change table.declarations.filter (fun d => d.role == 7) = _
          rw [eq]
          rfl
    have b0 : (visible p.state.core p.root)[0]? = some bindingOnly := by rw [allRows]; rfl
    have b2 : (visible p.state.core p.root)[2]? = some bindingOther := by rw [allRows]; rfl
    have different0 : 0 ≠ v.rejection.tape.opening.ordinal := by rw [atOne]; decide
    have different2 : 2 ≠ v.rejection.tape.opening.ordinal := by rw [atOne]; decide
    have bind0 : Rival413 v.rejection 0 bindingOnly :=
      ⟨b0,different0,matched_rival_is_real413 v.rejection 0 b0 different0⟩
    have bind2 : Rival413 v.rejection 2 bindingOther :=
      ⟨b2,different2,matched_rival_is_real413 v.rejection 2 b2 different2⟩
    obtain ⟨valid0,notChosen0⟩ := every_matching_rival_has_payload_but_cannot_win413 v 0 bind0 model fit
    obtain ⟨valid2,notChosen2⟩ := every_matching_rival_has_payload_but_cannot_win413 v 2 bind2 model fit
    exact ⟨p,rfl,fit,valid0,valid2,notChosen0,notChosen2,(check_sound p report _ yes).2 model fit⟩

#print axioms MixedTape.actual_rival
#print axioms actual_plain_rival_has_a_typed_leaf_payload413
#print axioms every_matching_rival_has_payload_but_cannot_win413
#print axioms same_X11_with_two_semantic_leaf_rivals_and_no_win413
end Yulang.GeneralDeclarativeI65.I72.MixedRecord413.RivalTest
