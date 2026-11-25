import Yulang.GeneralDeclarativeI65I74RigidRivalEntry418

namespace Yulang.GeneralDeclarativeI65.I72.RigidRival418.SpecWitness
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible)
open X6Ambiguous417 (integerOriginSyntax)
open CommonNominalFullCarrier (Subtype)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
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
def ground : Declaration := ⟨58,7,[.variant 20 (.app 10 [])],[],[],[]⟩

def surface (ds : List Declaration) (declared : Bool) : InputBundle :=
  let tags : List Row := [⟨9,some ⟨[],9⟩,.primitive (.scalar .int)⟩,⟨10,some ⟨[],10⟩,.primitive (.scalar .str)⟩]
  ⟨⟨.absent,tags⟩,⟨.absent,tags⟩,⟨1,if declared then [⟨7,1,[]⟩,⟨17,1,[]⟩] else [⟨17,1,[]⟩]⟩,ds⟩

def rootRow : Equation := variantRow416 0 20 1
def intRow : Equation := OpenTail414.intRow 1
def joinRow : Equation := idempotentRow 0
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[rootRow,intRow,joinRow]⟩

def build (ds : List Declaration := [actual])
    (raw : GeneralDeclarativeHead320.State := ordinary) (declared : Bool := true) (typed : Bool := true) :
    Option Problem := do
  let program ← compile bodies
  let src ← GeneralSourceMetadataBareBundle291.compile (surface ds declared)
  let e : Environment := ⟨0,0,0,bodies,program,src⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨e,raw,[]⟩,[],[⟨0,[44],originX6 20 1⟩] ++
      (if typed then [⟨1,[44,0],integerOriginSyntax⟩] else []),[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[61],⟨7,[⟨0,0,0⟩],[]⟩⟩⟩


def wire : RivalWire := ⟨0,1,0,1,2,0,1,⟨[0,1],[0,1]⟩,⟨[0,1],[2,0]⟩⟩
def reverse : RivalWire := {wire with plainOrdinal := 1, rivalOrdinal := 0}

def report418 : Result := Check408.nullaryReport actual

def checkOpt (p : Option Problem := build [actual,ground]) (r : Result := report418)
    (w : Witness := .rigidRival wire) : Bool :=
  (p.map fun data => check data r w).getD false

theorem actual_two_candidates_select_only_the_plain_match418 :
    checkOpt = true ∧ checkOpt (build [ground,actual]) report418 (.rigidRival reverse) = true ∧
    checkOpt (build [actual,ground]) (Check408.nullaryReport ground) = false ∧
    checkOpt (build [actual,ground]) ⟨.ambiguous,.ambiguous,[]⟩ = false :=
  by decide +kernel

def model : I72.Model :=
  ⟨fun n => ((if n = 0 then variant 20 (.base .int) else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (originX6 20 1) else
      if n = 1 then some integerOriginSyntax else none⟩

theorem actual_rigid_source_fits418 {p : Problem} (ds : List Declaration) (ready : build ds = some p) : Fits p.state model := by
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
        change x ∈ [⟨0,[44],originX6 20 1⟩,⟨1,[44,0],integerOriginSyntax⟩] at found
        simp only [List.mem_cons,List.not_mem_nil,or_false] at found
        rcases found with rfl|rfl <;> rfl


theorem build_preserves_authored_table418 {ds : List Declaration} {p : Problem}
    (ready : build ds = some p) :
    (authoredRegistry p.state.core.current).declarations = ds := by
  unfold build at ready
  cases cp : compile bodies with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile (surface ds true) with
    | none => simp [cp,cm] at ready
    | some bundle =>
      simp only [cp,cm,Option.pure_def] at ready
      cases ready
      exact congrArg InputBundle.declarations
        (GeneralSourceMetadataBareBundle291.preserves_input _ _ cm).1

def realOverlap : Declaration := {ground with head := [.variant 20 (.app 9 [])]}
def wrongTag : Declaration := {ground with head := [.variant 21 (.app 10 [])]}
def extra : Declaration := {ground with id := 59}
def rootCycle : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [⟨1,.variable 0⟩]}
def payloadCycle : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [variantRow416 1 20 1]}
def offRoute : GeneralDeclarativeHead320.State :=
  {ordinary with equations := ordinary.equations ++ [variantRow416 2 20 2]}
def offRouteWire : RivalWire :=
  {wire with
    rootEscape := ⟨[0,1,2],[0,1,2]⟩
    payloadEscape := ⟨[0,1,2],[2,0,2]⟩}
def rawWire : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,⟨0,.same,1⟩,[],.forward 3⟩

theorem unavailable_wrong_root_and_overlap_are_not_mismatch418 :
    checkOpt (build [actual,realOverlap]) = false ∧
    checkOpt (build [actual,wrongTag]) = false ∧
    checkOpt (build [actual,ground,extra]) = false ∧
    checkOpt (build [actual,ground] ordinary true false) = false ∧
    checkOpt (build [actual,ground]) report418 (.rigidRival {wire with rivalOrdinal := 0}) = false ∧
    checkOpt (build [actual]) = false ∧
    checkOpt (build [actual,ground] ordinary false) = false := by decide +kernel

theorem actual_visits_keep_raw_K2_and_off_route_distinct418 :
    checkOpt (build [actual,ground] rootCycle) = false ∧
    checkOpt (build [actual,ground] payloadCycle) = false ∧
    checkOpt (build [actual,ground] offRoute) report418 (.rigidRival offRouteWire) = true ∧
    checkOpt (build [actual,ground] rootCycle true false) Check408.rawReport
      (.previous (.previous (.previous (.previous (.previous (.previous
        (.previous (.previous (.previous (.previous (.rawRoot rawWire))))))))))) = true :=
  by decide +kernel

theorem old_C09_actual_overlap_is_still_ambiguous_not_C10_418 :
    checkOpt (build [actual,realOverlap]) X6Ambiguous417.report417
      (.previous (.x6Ambiguity ⟨0,1,0,1,2,0,1,wire.rootEscape,wire.payloadEscape⟩)) = true ∧
    checkOpt (build [actual,realOverlap]) report418 = false := by decide +kernel

theorem actual_sole_winner_has_same_model_dictionary_and_rival_fails418 :
    ∃ p, build [actual,ground] = some p ∧ Fits p.state model ∧
      ∃ a : Winner p.state p.root, replayWinner418 p wire = some a ∧
        ∀ m, Fits p.state m →
          ReportEvidence p.state m p.root report418 ∧
          DictionaryEvidence p.state m p.root (.node 57 []) ∧
          ¬ Subtype (m.assignment a.rows.payload).1 (.base .str) := by
  have good := actual_two_candidates_select_only_the_plain_match418.1
  cases ready : build [actual,ground] with
  | none => simp [checkOpt,ready] at good
  | some p =>
    have yes : check p report418 (.rigidRival wire) = true := by simpa [checkOpt,ready] using good
    obtain ⟨a,atWire,_⟩ := checked_plain_merge_reflects_original418 p report418 wire yes
    refine ⟨p,rfl,actual_rigid_source_fits418 _ ready,a,atWire,?_⟩
    intro m fit
    have h := check_sound p report418 (.rigidRival wire) yes
    exact ⟨h.2 m fit,
      dictionary_sound_R10 _ _ _ (exact_report_is_R10_classification418 h.1) m fit,
      (original_int_point_cannot_fit_str418 a.mismatch m fit).2⟩

#eval [checkOpt,checkOpt (build [ground,actual]) report418 (.rigidRival reverse),
  checkOpt (build [actual,realOverlap]),checkOpt (build [actual,ground] payloadCycle)]
#print axioms actual_two_candidates_select_only_the_plain_match418
#print axioms unavailable_wrong_root_and_overlap_are_not_mismatch418
#print axioms actual_visits_keep_raw_K2_and_off_route_distinct418
#print axioms old_C09_actual_overlap_is_still_ambiguous_not_C10_418
#print axioms actual_sole_winner_has_same_model_dictionary_and_rival_fails418

end Yulang.GeneralDeclarativeI65.I72.RigidRival418.SpecWitness
