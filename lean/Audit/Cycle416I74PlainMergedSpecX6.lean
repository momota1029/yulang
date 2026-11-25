import Yulang.GeneralDeclarativeI65I74PlainMergedEntry416

namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416.SpecX6
open GeneralDeclarativeI65 (B6OccurrenceAtlas401)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open Checker408 (Problem Result)
open CommonNominalFullCarrier (Ty variant subtype_refl)

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

def wire : PlainWire := ⟨0,0,1,2,0,⟨[0,1],[0,1]⟩⟩
def report : Result := Check408.nullaryReport actual
def checkOpt (p : Option Problem := build) (r : Result := report)
    (w : Witness := .plainMerged wire) : Bool :=
  (p.map fun data => check data r w).getD false

theorem actual_X6_selects_both_plain_binders416 : checkOpt = true := by decide +kernel

def noJoin : GeneralDeclarativeHead320.State := {ordinary with equations := [rootRow,intRow]}
def splitJoin : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [rootRow,intRow,⟨0,.join (.variable 0) (.variable 1)⟩]}
def differentTag : Declaration :=
  {actual with head := [.join (.variant 20 (.var 8)) (.variant 21 (.var 13))]}
def sameBinder : Declaration := {actual with head := [sourceX6 20 8 8]}
def noInt : GeneralDeclarativeHead320.State :=
  {ordinary with equations := [rootRow,ClosedResidual415.strRow 1,joinRow]}

theorem X6_controls_leave_ground_rival_unclassified416 :
    checkOpt (build [actual,ground]) = false ∧
    checkOpt (build [ground,actual]) = false ∧
    checkOpt (build [actual] ordinary false) = false ∧
    checkOpt (build [actual] noJoin) = false ∧
    checkOpt (build [actual] splitJoin) = false ∧
    checkOpt (build [actual] noInt) = false ∧
    checkOpt (build [differentTag]) = false ∧
    checkOpt (build [sameBinder]) = false ∧
    checkOpt build report (.plainMerged {wire with declaration := 1}) = false ∧
    checkOpt build Check408.rawReport = false := by decide +kernel

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then variant 20 (.base .int) else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (originX6 20 1) else none⟩

theorem actual_X6_source_fits416 {p : Problem} (ready : build = some p) : Fits p.state model := by
  unfold build at ready
  cases cp : compile bodies with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile (surface [actual] true) with
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
        · exact idempotent_row_adds_no_model_requirement416 0 model
      · intro _ no; cases no
      · intro x found
        obtain rfl := List.mem_singleton.mp found
        rfl

theorem genuine_X6_has_its_semantic_report_and_dictionary416 :
    ∃ p, build = some p ∧ Fits p.state model ∧
      ∀ m, Fits p.state m → ReportEvidence p.state m p.root report ∧
        DictionaryEvidence p.state m p.root (.node 57 []) := by
  have good := actual_X6_selects_both_plain_binders416
  cases ready : build with
  | none => simp [checkOpt,ready] at good
  | some p =>
    have yes : check p report (.plainMerged wire) = true := by simpa [checkOpt,ready] using good
    have checked := check_sound p report (.plainMerged wire) yes
    refine ⟨p,rfl,actual_X6_source_fits416 ready,fun m fit => ⟨checked.2 m fit,?_⟩⟩
    exact dictionary_sound_R8 p.state p.root _ (exact_report_is_R8_classification416 checked.1) m fit

#eval [checkOpt,checkOpt (build [actual,ground]),checkOpt (build [actual] splitJoin),
  checkOpt (build [actual] noJoin),checkOpt (build [actual] noInt)]
#print axioms actual_X6_selects_both_plain_binders416
#print axioms X6_controls_leave_ground_rival_unclassified416
#print axioms actual_X6_source_fits416
#print axioms genuine_X6_has_its_semantic_report_and_dictionary416
end Yulang.GeneralDeclarativeI65.I72.PlainMerged416.SpecX6
