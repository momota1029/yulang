import Yulang.GeneralDeclarativeI65I74RecordFidelity412

namespace Yulang.GeneralDeclarativeI65.I72.RecordK2412.PositionControls
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 Origin)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty Equivalent record)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def implCheck : Declaration :=
  ⟨152,43,[closedHead412 31 4 18 29],[⟨13,43,[closedWhere412 31 18 29],[]⟩],[],[]⟩
def table : InputBundle :=
  let catalogue : List Row := [⟨18,some ⟨[],18⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨43,1,[]⟩]⟩,[implCheck]⟩

def firstRow : Equation := recordRow412 8 4 11
def outerRow : Equation := recordRow412 5 31 8
def lastRow : Equation := recordRow412 11 15 8
def extra : Origin := ⟨3,[29],.ordinary .emptyRecord⟩
def genuine : Origin := ⟨5,[52,1],recordInput412 31 8⟩
def ordinary : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[]⟩,[firstRow,outerRow,lastRow]⟩

def build (source : InputBundle := table) (raw : GeneralDeclarativeHead320.State := ordinary)
    (origins : List Origin := [extra,genuine]) : Option Problem := do
  let sem ← compile bodies
  let copied ← GeneralSourceMetadataBareBundle291.compile source
  let env : Environment := ⟨0,0,0,bodies,sem,copied⟩
  let s : GeneralDeclarativeI65.State := ⟨⟨env,raw,[]⟩,[],origins,[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[31,0],⟨43,[⟨5,5,5⟩],[]⟩⟩⟩

def rank : List Nat := (List.range 12).map (fun n => if n = 5 then 0 else if n = 8 ∨ n = 11 then 1 else 2)
def wire : FieldWire := ⟨1,1,⟨rank,[0,1,2]⟩,⟨⟨0,.same,11⟩,[⟨2,.same,8⟩],.same⟩⟩
def run (p : Option Problem := build) (w : FieldWire := wire) : Bool :=
  (p.map fun data => check data Check408.rawReport (.fieldCycle w)).getD false

theorem actual_two_hop_nonzero_ordinals412 : run = true := by decide +kernel

def wrongLabel : Declaration :=
  {implCheck with head := [closedHead412 30 4 18 29], requirements := [⟨13,43,[closedWhere412 30 18 29],[]⟩]}
def variableOnly : Declaration :=
  {implCheck with head := [closedWhere412 31 18 29],requirements := []}
def separateRole : InputBundle := {table with roles := {table.roles with rows := [],fallbackArity := 1}}
def disguised : List Origin := [extra,⟨5,[52,1],recordInput412 31 11⟩]
def wrongClosure : FieldCycleWire := ⟨⟨0,.same,11⟩,[],.same⟩

/-- No guessed origin, chosen field, unrelated lexical candidate, or
failed closure can become the diagnostic for the genuine site. -/
theorem alternate_X10_scope_controls412 :
    run build {wire with originOrdinal := 0} = false ∧
    run build {wire with outerRowOrdinal := 0} = false ∧
    run build {wire with cycle := wrongClosure} = false ∧
    run (build table ordinary disguised) = false ∧
    run (build {table with declarations := [wrongLabel]}) = false ∧
    run (build {table with declarations := [variableOnly]}) = false ∧
    run (build separateRole) = false := by decide +kernel

def a0 : CommonNominalSyntax.State Common.Row :=
  .block [.record 4 (.inl 1) .emptyRecord,.record 15 (.inl 0) .emptyRecord] 0
def a1 : CommonNominalSyntax.State Common.Row :=
  .block [.record 4 (.inl 1) .emptyRecord,.record 15 (.inl 0) .emptyRecord] 1
def mu0 : Ty := .record 4 a1 .emptyRecord
def mu1 : Ty := .record 15 a0 .emptyRecord

theorem two_node_first_unfolds412 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth mu0 =
      CommonNominalFullCarrier.observeTy depth (record 4 mu1 .emptyRecord) := by
  cases depth <;> rfl
theorem two_node_last_unfolds412 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth mu1 =
      CommonNominalFullCarrier.observeTy depth (record 15 mu0 .emptyRecord) := by
  cases depth <;> rfl

def model : I72.Model :=
  ⟨fun n => ((if n = 5 then record 31 mu0 .emptyRecord else if n = 8 then mu0 else mu1),Common.rowEmpty),
    fun _ => none,fun n => if n = 5 then some genuine.endpoint else if n = 3 then some extra.endpoint else none⟩

theorem alternate_record_snapshot_fits412 {p : Problem} (read : build = some p) :
    I72.Fits p.state model := by
  unfold build at read
  cases sparse : compile bodies with
  | none => simp [sparse] at read
  | some sem =>
    cases compiledSource : GeneralSourceMetadataBareBundle291.compile table with
    | none => simp [sparse,compiledSource] at read
    | some env =>
      simp only [sparse,compiledSource,Option.pure_def] at read
      cases read
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ empty; cases empty
      · intro _ empty; cases empty
      · intro e inside
        change e ∈ [firstRow,outerRow,lastRow] at inside
        have h : e = firstRow ∨ e = outerRow ∨ e = lastRow := by
          simpa only [List.mem_cons,List.not_mem_nil,or_false] using inside
        rcases h with rfl|rfl|rfl
        · change Equivalent mu0 (record 4 mu1 .emptyRecord)
          constructor <;> intro n <;> rw [← two_node_first_unfolds412 n] <;>
            exact CommonNominalFullDemand.producerLe_refl _
        · exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
        · change Equivalent mu1 (record 15 mu0 .emptyRecord)
          constructor <;> intro n <;> rw [← two_node_last_unfolds412 n] <;>
            exact CommonNominalFullDemand.producerLe_refl _
      · intro _ empty; cases empty
      · intro item used
        change item ∈ [extra,genuine] at used
        have occurs : item = extra ∨ item = genuine := by
          simpa only [List.mem_cons,List.not_mem_nil,or_false] using used
        rcases occurs with rfl|rfl <;> rfl

theorem two_hop_actual_record_report_in_same_model412 :
    ∃ p, build = some p ∧ I72.Fits p.state model ∧
      ReportEvidence p.state model p.root Check408.rawReport := by
  have yes := actual_two_hop_nonzero_ordinals412
  unfold run at yes
  cases read : build with
  | none => simp [read] at yes
  | some p =>
    have checked : check p Check408.rawReport (.fieldCycle wire) = true := by simpa [read] using yes
    have fit := alternate_record_snapshot_fits412 read
    exact ⟨p,rfl,fit,(check_sound p _ _ checked).2 model fit⟩

open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeK2Graph321 (View)
open GeneralDeclarativeInspect321 (Visit fieldPatterns variable_has_no_visit)

theorem only_binding_record_field_does_not_visit_inner_site412
    {v : View} {root label binder site : Nat}
    (entered : Visit v root (.record label (.variable binder) (.primitive .emptyRecord [])) site) :
    site = root := by
  cases entered with
  | here => rfl
  | field _ _ found rest =>
    change _ ∈ [(label, Expr.variable binder)] at found
    have exactQuery := (Prod.mk.inj (List.mem_singleton.mp found)).2
    rw [exactQuery] at rest
    exact False.elim (variable_has_no_visit rest)

theorem original_outer_record_is_seen_and_holds_in_same_model412 {s q d}
    (p : ActualRecordField s q d) (m : I72.Model) (fit : Fits s m) :
    m.nativeSyntax p.input.lower = some (recordInput412 p.box p.site) ∧
    Equivalent (m.assignment p.input.lower).1
      (record p.box (m.assignment p.site).1 .emptyRecord) := by
  have seen := fit.2 _ p.original
  rw [p.originLower,p.endpoint] at seen
  exact ⟨seen,fit.1.1.2 _ p.ordinaryRow⟩

#eval [run,run build {wire with originOrdinal := 0},
  run build {wire with outerRowOrdinal := 0},run build {wire with cycle := wrongClosure},
  run (build table ordinary disguised),run (build {table with declarations := [wrongLabel]}),
  run (build {table with declarations := [variableOnly]}),run (build separateRole)]

#print axioms only_binding_record_field_does_not_visit_inner_site412
#print axioms original_outer_record_is_seen_and_holds_in_same_model412
#print axioms actual_two_hop_nonzero_ordinals412
#print axioms alternate_X10_scope_controls412
#print axioms two_node_first_unfolds412
#print axioms two_node_last_unfolds412
#print axioms alternate_record_snapshot_fits412
#print axioms two_hop_actual_record_report_in_same_model412
end Yulang.GeneralDeclarativeI65.I72.RecordK2412.PositionControls
