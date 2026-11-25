import Yulang.GeneralDeclarativeI65I74RecordLocation412

namespace Yulang.GeneralDeclarativeI65.I72.RecordK2412.AliasControls
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

def flat : Equation := ⟨11,.variable 8⟩
def closesByAlias : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [firstRow,outerRow,flat]}
def aliasWire : FieldWire := {wire with cycle := ⟨⟨0,.same,11⟩,[],.forward 2⟩}
def oneWayOnly : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[(11,8)]⟩,[firstRow,outerRow]⟩
def fakeFlat : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [firstRow,outerRow,⟨11,.variable 5⟩]}

theorem actual_leaf_can_close_through_real_raw_alias412 :
    run (build table closesByAlias) aliasWire = true := by decide +kernel

theorem a_one_way_bound_is_not_the_checked_flat_alias412 :
    run (build table oneWayOnly) aliasWire = false ∧
    run (build table fakeFlat) aliasWire = false ∧
    run (build table closesByAlias) {aliasWire with cycle := ⟨⟨0,.same,11⟩,[],.same⟩} = false := by
  decide +kernel

def cycleState : CommonNominalSyntax.State Common.Row :=
  .block [.record 4 (.inl 0) .emptyRecord] 0
def mu : Ty := .record 4 cycleState .emptyRecord

theorem alias_regular_model_unfolds412 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth mu =
      CommonNominalFullCarrier.observeTy depth (record 4 mu .emptyRecord) := by
  cases depth <;> rfl

def model : I72.Model :=
  ⟨fun n => ((if n = 5 then record 31 mu .emptyRecord else mu),Common.rowEmpty),
    fun _ => none,fun n => if n = 5 then some genuine.endpoint else if n = 3 then some extra.endpoint else none⟩

theorem alias_closed_snapshot_fits412 {p : Problem} (read : build table closesByAlias = some p) :
    I72.Fits p.state model := by
  unfold build at read
  cases sparse : compile bodies with
  | none => simp [sparse] at read
  | some sem =>
    cases compiled : GeneralSourceMetadataBareBundle291.compile table with
    | none => simp [sparse,compiled] at read
    | some env =>
      simp only [sparse,compiled,Option.pure_def] at read
      cases read
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ empty; cases empty
      · intro _ empty; cases empty
      · intro e inside
        change e ∈ [firstRow,outerRow,flat] at inside
        have h : e = firstRow ∨ e = outerRow ∨ e = flat := by
          simpa only [List.mem_cons,List.not_mem_nil,or_false] using inside
        rcases h with rfl|rfl|rfl
        · change Equivalent mu (record 4 mu .emptyRecord)
          constructor <;> intro n <;> rw [← alias_regular_model_unfolds412 n] <;>
            exact CommonNominalFullDemand.producerLe_refl _
        · exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
        · exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
      · intro _ empty; cases empty
      · intro item used
        change item ∈ [extra,genuine] at used
        have occurs : item = extra ∨ item = genuine := by
          simpa only [List.mem_cons,List.not_mem_nil,or_false] using used
        rcases occurs with rfl|rfl <;> rfl

theorem alias_closed_actual_report_in_same_fitting_model412 :
    ∃ p, build table closesByAlias = some p ∧ I72.Fits p.state model ∧
      ReportEvidence p.state model p.root Check408.rawReport := by
  have yes := actual_leaf_can_close_through_real_raw_alias412
  unfold run at yes
  cases read : build table closesByAlias with
  | none => simp [read] at yes
  | some p =>
    have checked : check p Check408.rawReport (.fieldCycle aliasWire) = true := by simpa [read] using yes
    have fit := alias_closed_snapshot_fits412 read
    exact ⟨p,rfl,fit,(check_sound p _ _ checked).2 model fit⟩

theorem alias_closure_does_not_move_the_diagnostic_site412 :
    (build table closesByAlias).bind (fun p => locate p Check408.rawReport aliasWire) =
      some (⟨[31,0],152,0,31,5,8⟩ : FieldLocation) := by decide +kernel

#eval [run (build table closesByAlias) aliasWire, run (build table oneWayOnly) aliasWire,
  run (build table fakeFlat) aliasWire,
  run (build table closesByAlias) {aliasWire with cycle := ⟨⟨0,.same,11⟩,[],.same⟩}]

#print axioms alias_closure_does_not_move_the_diagnostic_site412
#print axioms actual_leaf_can_close_through_real_raw_alias412
#print axioms a_one_way_bound_is_not_the_checked_flat_alias412
#print axioms alias_regular_model_unfolds412
#print axioms alias_closed_snapshot_fits412
#print axioms alias_closed_actual_report_in_same_fitting_model412
end Yulang.GeneralDeclarativeI65.I72.RecordK2412.AliasControls
