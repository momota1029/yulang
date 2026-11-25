import Yulang.GeneralDeclarativeI65I74X6AmbiguousEntry417

namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417.SpecX6
open GeneralDeclarativeI65 (B6OccurrenceAtlas401)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty variant subtype_refl)
open PlainMerged416 (sourceX6 variantRow416 idempotentRow originX6)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def actual : Declaration := ⟨57,7,[sourceX6 20 8 13],[],[],[]⟩
def ground : Declaration := ⟨58,7,[.variant 20 (.app 9 [])],[],[],[]⟩

def surface (ds : List Declaration) (declared : Bool) : InputBundle :=
  let tags : List Row := [⟨9,some ⟨[],9⟩,.primitive (.scalar .int)⟩]
  ⟨⟨.absent,tags⟩,⟨.absent,tags⟩,⟨1,if declared then [⟨7,1,[]⟩] else []⟩,ds⟩

def rootRow : Equation := variantRow416 0 20 1
def intRow : Equation := OpenTail414.intRow 1
def joinRow : Equation := idempotentRow 0
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[rootRow,intRow,joinRow]⟩

def build (ds : List Declaration := [actual])
    (raw : GeneralDeclarativeHead320.State := ordinary) (declared : Bool := true) :
    Option Problem := do
  let program ← compile bodies
  let src ← GeneralSourceMetadataBareBundle291.compile (surface ds declared)
  let e : Environment := ⟨0,0,0,bodies,program,src⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨e,raw,[]⟩,[],[⟨0,[44],originX6 20 1⟩],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩],[]⟩⟩⟩


def wire : AmbiguityWire := ⟨0,0,1,2,0,1,⟨[0,1],[0,1]⟩,⟨[0,1],[2,0]⟩⟩
def reverse : AmbiguityWire := {wire with plainOrdinal := 1, groundOrdinal := 0}

def checkOpt (p : Option Problem := build [actual,ground]) (r : Result := report417)
    (w : Witness := .x6Ambiguity wire) : Bool :=
  (p.map fun data => check data r w).getD false

theorem both_authored_orders_report_only_ambiguity417 :
    checkOpt = true ∧ checkOpt (build [ground,actual]) report417 (.x6Ambiguity reverse) = true :=
  by decide +kernel

theorem neither_candidate_is_selected_and_no_receipt_is_fabricated417 :
    checkOpt (build [actual,ground]) (Check408.nullaryReport actual) = false ∧
    checkOpt (build [actual,ground]) (Check408.nullaryReport ground) = false ∧
    checkOpt (build [actual,ground]) Check408.rawReport = false ∧
    checkOpt (build [actual,ground]) {report417 with
      writes := [⟨[61],0,0,⟨9,9⟩,.default 7 9 (.var 0),.node 0 [] []⟩]} = false :=
  by decide +kernel

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then variant 20 (.base .int) else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (originX6 20 1) else none⟩

theorem actual_X6_ambiguity_source_fits417 {p : Problem} (ds : List Declaration) (ready : build ds = some p) : Fits p.state model := by
  unfold build at ready
  cases cp : compile bodies with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile (surface ds true) with
    | none => simp [cp,cm] at ready
    | some bundle =>
      simp only [cp,cm,Option.pure_def] at ready
      cases ready
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ no; cases no
      · intro _ no; cases no
      · intro x found
        change x ∈ [rootRow,intRow,joinRow] at found
        simp only [List.mem_cons,List.not_mem_nil,or_false] at found
        rcases found with rfl|rfl|rfl
        · exact ⟨subtype_refl _,subtype_refl _⟩
        · exact ⟨subtype_refl _,subtype_refl _⟩
        · exact PlainMerged416.idempotent_row_adds_no_model_requirement416 0 model
      · intro _ no; cases no
      · intro x found
        obtain rfl := List.mem_singleton.mp found
        rfl


theorem genuine_X6_model_has_two_actual_matches_and_ambiguous_report417 :
    ∃ p, build [actual,ground] = some p ∧ Fits p.state model ∧
      ∃ a : Ambiguous p.state p.root, replayAmbiguity417 p wire = some a ∧
      ∀ m, Fits p.state m → ClassifiedAs p.state p.root report417 ∧
        ReportEvidence p.state m p.root report417 := by
  have good := both_authored_orders_report_only_ambiguity417.1
  cases ready : build [actual,ground] with
  | none => simp [checkOpt,ready] at good
  | some p =>
    have yes : check p report417 (.x6Ambiguity wire) = true := by simpa [checkOpt,ready] using good
    obtain ⟨witness,replay,_⟩ := checked_x6_reflects_exact_candidates_and_report417 p report417 wire yes
    refine ⟨p,rfl,actual_X6_ambiguity_source_fits417 _ ready,witness,replay,
      fun m fit => ⟨(check_sound _ _ _ yes).1,(check_sound _ _ _ yes).2 m fit⟩⟩

#eval [checkOpt,checkOpt (build [ground,actual]) report417 (.x6Ambiguity reverse),
  checkOpt (build [actual,ground]) (Check408.nullaryReport actual)]
#print axioms both_authored_orders_report_only_ambiguity417
#print axioms neither_candidate_is_selected_and_no_receipt_is_fabricated417
#print axioms actual_X6_ambiguity_source_fits417
#print axioms genuine_X6_model_has_two_actual_matches_and_ambiguous_report417
end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417.SpecX6
