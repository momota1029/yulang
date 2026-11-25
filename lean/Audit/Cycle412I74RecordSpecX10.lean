import Yulang.GeneralDeclarativeI65I74RecordPriority412

namespace Yulang.GeneralDeclarativeI65.I72.RecordK2412.SpecX10
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

theorem x10_exact_field_cycle_executes412 : test = true := by decide +kernel

theorem x10_exact_internal_field_cycle412 :
    GeneralDeclarativeK2Alias321.AliasCycle ordinary
      (GeneralDeclarativeGraphRows321.observed ordinary) 1 :=
  cycle_at_sound412 (w := wire.cycle) (by decide +kernel)

theorem x10_parent_itself_is_not_raw_K2412 : ¬ GeneralDeclarativePriority321.RootRecurs ordinary request := by
  rintro ⟨a,mem,cycle⟩
  change a ∈ [⟨0,0,0⟩] at mem
  cases List.mem_singleton.mp mem
  exact List410.exact_escape_refutes_raw_root_K2410 (w := wire.escape) (by decide +kernel) cycle

def rewriteOrdinary (p : Problem) (raw : GeneralDeclarativeHead320.State) : Problem :=
  let s := {p.state.core with current := {p.state.core.current with ordinary := raw}}
  ⟨⟨s,⟨fun _ _ _ _ => none⟩⟩,p.root⟩
def rootReturn : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ⟨1,.variable 0⟩ :: ordinary.equations}
def noLoop : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [outerRow]}
def disconnectedLoop : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [outerRow,recordRow412 2 21 2]}
def counterfeitElsewhere : FieldWire := {wire with cycle := ⟨⟨1,.same,2⟩,[],.same⟩}
def rootCycleWire : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,⟨1,.same,1⟩,[],.forward 0⟩
def cycleAsParent : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,wire.cycle.first,[],.same⟩

theorem x10_omitted_or_counterfeit_visit_is_not_checked412 :
    test (problem.map (fun p => rewriteOrdinary p noLoop)) = false ∧
    test (problem.map (fun p => rewriteOrdinary p disconnectedLoop)) expected
      (.fieldCycle counterfeitElsewhere) = false ∧
    test problem expected (.fieldCycle {wire with outerRowOrdinal := 1}) = false ∧
    test problem expected (.fieldCycle {wire with originOrdinal := 4}) = false ∧
    test problem (WhereCycle411.expected411 implCheck) = false := by
  decide +kernel

theorem x10_root_branch_remains_separate_and_has_priority412 :
    test problem expected (.previous (.previous (.previous (.previous (.rawRoot cycleAsParent))))) = false ∧
    test (problem.map (fun p => rewriteOrdinary p rootReturn)) = false ∧
    test (problem.map (fun p => rewriteOrdinary p rootReturn)) expected
      (.previous (.previous (.previous (.previous (.rawRoot rootCycleWire))))) = true := by
  decide +kernel

def muState : CommonNominalSyntax.State Common.Row :=
  .block [.record 21 (.inl 0) .emptyRecord] 0

def mu : Ty := .record 21 muState .emptyRecord

theorem mu_observations_unfold412 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth mu =
      CommonNominalFullCarrier.observeTy depth (record 21 mu .emptyRecord) := by
  cases depth <;> rfl

theorem mu_equivalent_unfold412 : Equivalent mu (record 21 mu .emptyRecord) := by
  constructor <;> intro depth <;> rw [← mu_observations_unfold412 depth] <;>
    exact CommonNominalFullDemand.producerLe_refl _

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then record 20 mu .emptyRecord else mu),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (recordInput412 20 1) else none⟩

theorem x10_cyclic_record_model_fits412 {p : Problem} (built : problem = some p) :
    I72.Fits p.state model := by
  unfold problem at built
  cases sparse : compile bodies with
  | none => simp [sparse] at built
  | some graph =>
    cases authored : GeneralSourceMetadataBareBundle291.compile surface with
    | none => simp [sparse,authored] at built
    | some src =>
      simp only [sparse,authored,Option.pure_def] at built
      cases built
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ empty; cases empty
      · intro _ empty; cases empty
      · intro eq seen
        change eq ∈ [outerRow,loopRow] at seen
        have two : eq = outerRow ∨ eq = loopRow := by
          simpa only [List.mem_cons,List.not_mem_nil,or_false] using seen
        rcases two with rfl|rfl
        · exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
        · exact mu_equivalent_unfold412
      · intro _ empty; cases empty
      · intro item present
        have one : item = (⟨0,[32],recordInput412 20 1⟩ : GeneralDeclarativeI65.Origin) :=
          List.mem_singleton.mp present
        cases one
        rfl

theorem x10_exact_same_cyclic_snapshot_has_report_evidence412 :
    ∃ p, problem = some p ∧ check p expected (.fieldCycle wire) = true ∧
      I72.Fits p.state model ∧ ReportEvidence p.state model p.root expected := by
  have run := x10_exact_field_cycle_executes412
  unfold test at run
  cases got : problem with
  | none => simp [got] at run
  | some p =>
    have accepted : check p expected (.fieldCycle wire) = true := by simpa [got] using run
    have fit := x10_cyclic_record_model_fits412 got
    exact ⟨p,rfl,accepted,fit,(check_sound p expected _ accepted).2 model fit⟩

open GeneralDeclarativeI65 (visible Origin)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeGraphRows321 (structural)

theorem x10_exact_candidate_box_tick_visit412 {p : Problem} (built : problem = some p) :
    ∃ (a : ActualRecordField p.state p.root implCheck),
      a.box = 20 ∧ a.tick = 21 ∧ a.site = 1 ∧
      Visit (structural p.state.core.current.ordinary) a.input.lower
        (query412 20 21 a.binder) 1 ∧ ¬RootCycle p.state p.root := by
  have run := x10_exact_field_cycle_executes412
  unfold test at run
  simp only [built,Option.map_some,Option.getD_some] at run
  obtain ⟨d,_,verified,_,_⟩ := checked_field_reflects_actual_original_rejection412 p expected wire run
  have originals : p.state.core.origins = [⟨0,[32],recordInput412 20 1⟩] ∧
      visible p.state.core p.root = [implCheck] := by
    unfold problem at built
    cases sparse : compile bodies with
    | none => simp [sparse] at built
    | some graph =>
      cases authored : GeneralSourceMetadataBareBundle291.compile surface with
      | none => simp [sparse,authored] at built
      | some src =>
        simp only [sparse,authored,Option.pure_def] at built
        cases built
        refine ⟨rfl,?_⟩
        have actual : src.declarations = surface.declarations :=
          congrArg InputBundle.declarations
            (GeneralSourceMetadataBareBundle291.preserves_input surface src authored).1
        change src.declarations.filter (fun d => d.role == 19) = _
        rw [actual]
        rfl
  have decl : verified.rejection.decl = implCheck :=
    (List.cons.inj (verified.rejection.field.only.symm.trans originals.2)).1
  let a : ActualRecordField p.state p.root implCheck := decl ▸ verified.rejection.field
  have found := a.original
  rw [originals.1] at found
  have source := a.endpoint
  rw [List.mem_singleton.mp found] at source
  change recordInput412 20 1 = recordInput412 a.box a.site at source
  have ⟨box,site⟩ : a.box = 20 ∧ a.site = 1 := by
    injection source with proof
    injection proof with label payload _
    exact ⟨label.symm,(Core.PresenceGeneration.TyTerm.var.inj payload).symm⟩
  have tick : a.tick = 21 := by
    have normal := (List.cons.inj a.head).1
    change closedHead412 20 21 9 3 = closedHead412 a.box a.tick a.empty a.binder at normal
    injection normal with _ inner _
    have innerL := (GeneralDeclarationPatterns.Pattern.record.inj inner).1
    exact innerL.symm
  have visit := actual_record_field_is_entered412 a
  rw [box,tick,site] at visit
  exact ⟨a,box,tick,site,visit,verified.rootSafe⟩

#eval [test,
  test (problem.map (fun p => rewriteOrdinary p noLoop)),
  test (problem.map (fun p => rewriteOrdinary p disconnectedLoop)) expected (.fieldCycle counterfeitElsewhere),
  test problem expected (.fieldCycle {wire with outerRowOrdinal := 1}),
  test problem expected (.fieldCycle {wire with originOrdinal := 4}),
  test problem (WhereCycle411.expected411 implCheck),
  test problem expected (.previous (.previous (.previous (.previous (.rawRoot cycleAsParent))))),
  test (problem.map (fun p => rewriteOrdinary p rootReturn)),
  test (problem.map (fun p => rewriteOrdinary p rootReturn)) expected
    (.previous (.previous (.previous (.previous (.rawRoot rootCycleWire)))))]

#print axioms x10_exact_candidate_box_tick_visit412
#print axioms x10_exact_field_cycle_executes412
#print axioms x10_exact_internal_field_cycle412
#print axioms x10_parent_itself_is_not_raw_K2412
#print axioms x10_omitted_or_counterfeit_visit_is_not_checked412
#print axioms x10_root_branch_remains_separate_and_has_priority412
#print axioms mu_observations_unfold412
#print axioms mu_equivalent_unfold412
#print axioms x10_cyclic_record_model_fits412
#print axioms x10_exact_same_cyclic_snapshot_has_report_evidence412
end Yulang.GeneralDeclarativeI65.I72.RecordK2412.SpecX10
