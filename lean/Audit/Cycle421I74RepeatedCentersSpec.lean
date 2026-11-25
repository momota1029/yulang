import Yulang.GeneralDeclarativeI65I74RepeatedCentersEntry421

namespace Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421.SpecRepeated
open GeneralDeclarativeI65 (B6OccurrenceAtlas401)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeEntailment320 (appendFacts)
open CommonNominalFullCarrier (Ty Subtype variant observeTy subtype_refl)
open Checker408 (Problem Result)

def bodySource : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def actual : Declaration := ⟨57,7,[.var 8,.var 8],[],[],[]⟩
def distinct : Declaration := {actual with head := [.var 8,.var 9]}
def unrelated : Declaration := ⟨58,9,[],[],[],[]⟩
def surface (table : List Declaration) : InputBundle :=
  ⟨⟨.absent,[]⟩,⟨.absent,[]⟩,⟨0,[⟨7,2,[]⟩,⟨9,0,[]⟩]⟩,table⟩

def exactTie : Equation := ⟨4,.variable 1⟩
def endpointRanges : List (Nat × Nat) := [(0,1),(1,2),(3,4),(4,2)]
def payloadColor (mismatch : Bool) : Color := if mismatch then .boolean else .integer
def raw (mismatch tie cycle : Bool) : GeneralDeclarativeHead320.State :=
  ⟨⟨[],endpointRanges⟩,[variantRow 0 20 5,variantRow 3 20 6,
    variantRow 1 20 5,variantRow 4 20 6,⟨5,colorExpr .integer⟩,⟨6,colorExpr (payloadColor mismatch)⟩] ++
    (if tie then [exactTie] else []) ++ (if cycle then [⟨6,.variable 3⟩] else [])⟩

def build (mismatch : Bool := false) (tie : Bool := true) (cycle : Bool := false)
    (table : List Declaration := [unrelated,actual]) (origins : Bool := true) : Option Problem := do
  let program ← compile bodySource
  let bundle ← GeneralSourceMetadataBareBundle291.compile (surface table)
  let env : Environment := ⟨0,0,0,bodySource,program,bundle⟩
  let state : GeneralDeclarativeI65.State := ⟨⟨env,raw mismatch tie cycle,[]⟩,[],
    if origins then [⟨0,[44],literalVariant 20 5⟩,⟨3,[55],literalVariant 20 6⟩] else [],[]⟩
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨state,atlas⟩,⟨[61,0],⟨7,[⟨0,1,2⟩,⟨3,4,2⟩],[]⟩⟩⟩

def escape : List410.ExactEscapeWire := ⟨[0,1,2,0,1,3,3],[0,2,2,1]⟩
def wire : Wire := ⟨⟨⟨0,0⟩,⟨1,1⟩,1,escape,escape⟩,⟨⟨2,4⟩,⟨3,5⟩,6⟩⟩
def selected : Result := Check408.nullaryReport actual
def postConflict : Result := ⟨.rejected,.rejected,[]⟩
def probe (p : Option Problem := build) (r : Result := selected)
    (w : Witness := .repeatedCenters wire) : Bool :=
  (p.map fun data => check data r w).getD false

def electedBeforeTie (p : Option Problem) : Bool :=
  (p.map fun data => (readChoice421 data wire.pre).isSome).getD false

theorem both_nonpoint_inputs_elect_before_reading_center_tie421 :
    electedBeforeTie (build false false) = true ∧
    electedBeforeTie (build true false) = true ∧
    electedBeforeTie (build false true) = true := by decide +kernel

theorem actual_shared_binder_accepts_compatible_retained_centers421 :
    probe = true := by decide +kernel

theorem actual_incompatible_centers_reject_only_after_electing421 :
    probe (build true false) postConflict = true ∧
    probe (build true false) selected = false := by decide +kernel

theorem missing_tie_alone_is_neither_rejection_nor_success421 :
    probe (build false false) selected = false ∧
    probe (build false false) postConflict = false ∧
    probe (build false true) selected (.repeatedCenters {wire with post := {wire.post with tieRow := 5}}) = false := by
  decide +kernel

theorem witnessed_prechoice_is_not_a_claim_about_another_candidate_or_source421 :
    probe (build (table := [unrelated,distinct])) = false ∧
    probe (build (origins := false)) = false ∧
    probe build selected (.repeatedCenters {wire with pre := {wire.pre with ordinal := 0}}) = false ∧
    probe (build true false) postConflict
      (.repeatedCenters {wire with post := {wire.post with second := ⟨2,5⟩}}) = false ∧
    probe (build true true) selected = false := by decide +kernel

def rawWire : GeneralDeclarativeWitnessCycle350.Wire := ⟨1,⟨1,.same,6⟩,[],.forward 6⟩
def legacyRaw : Witness :=
  .previous (.previous (.previous (.previous (.previous (.previous
    (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.rawRoot rawWire)))))))))))))

theorem second_raw_root_cycle_still_precedes_center_conflict421 :
    probe (build true false true) postConflict = false ∧
    probe (build true false true) postConflict legacyRaw = true := by decide +kernel

def firstTy : Ty := variant 20 (.base .int)
def secondTy (mismatch : Bool) : Ty := variant 20 (.base (payloadColor mismatch).base)
def model (mismatch : Bool) : I72.Model :=
  ⟨fun n => (if n = 0 ∨ n = 1 then firstTy else if n = 2 then .union firstTy (secondTy mismatch)
    else if n = 3 ∨ n = 4 then secondTy mismatch else if n = 6 then .base (payloadColor mismatch).base
    else .base .int,Common.rowEmpty),fun _ => none,
    fun n => if n = 0 then some (literalVariant 20 5) else if n = 3 then some (literalVariant 20 6) else none⟩

private theorem union_left (a b : Ty) : Subtype a (.union a b) := by
  intro d
  exact CommonNominalFullDemand.producerLe_union_left (observeTy d a) (observeTy d b)

private theorem union_right (a b : Ty) : Subtype b (.union a b) := by
  intro d
  exact CommonNominalFullDemand.producerLe_union_right (observeTy d a) (observeTy d b)

theorem both_tied_or_conflicting_before_tie_original_states_have_models421
    {p : Problem} (bad : Bool) (ready : build bad (!bad) = some p) : Fits p.state (model bad) := by
  unfold build at ready
  cases cp : compile bodySource with
  | none => simp [cp] at ready
  | some program =>
    cases cm : GeneralSourceMetadataBareBundle291.compile (surface [unrelated,actual]) with
    | none => simp [cp,cm] at ready
    | some bundle =>
      simp only [cp,cm,Option.pure_def] at ready
      cases Option.some.inj ready
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ no; cases no
      · intro pair observed
        change pair ∈ [(0,1),(1,2),(3,4),(4,2)] at observed
        simp only [List.mem_cons,List.not_mem_nil,or_false] at observed
        rcases observed with rfl|rfl|rfl|rfl
        · exact subtype_refl _
        · exact union_left _ _
        · exact subtype_refl _
        · exact union_right _ _
      · intro e carried
        cases bad
        · change e ∈ [variantRow 0 20 5,variantRow 3 20 6,variantRow 1 20 5,variantRow 4 20 6,
            ⟨5,colorExpr .integer⟩,⟨6,colorExpr .integer⟩,exactTie] at carried
          simp only [List.mem_cons,List.not_mem_nil,or_false] at carried
          rcases carried with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
        · change e ∈ [variantRow 0 20 5,variantRow 3 20 6,variantRow 1 20 5,variantRow 4 20 6,
            ⟨5,colorExpr .integer⟩,⟨6,colorExpr .boolean⟩] at carried
          simp only [List.mem_cons,List.not_mem_nil,or_false] at carried
          rcases carried with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
      · intro _ none; cases none
      · intro origin inSource
        change origin ∈ [⟨0,[44],literalVariant 20 5⟩,⟨3,[55],literalVariant 20 6⟩] at inSource
        simp only [List.mem_cons,List.not_mem_nil,or_false] at inSource
        rcases inSource with rfl|rfl <;> rfl

theorem actual_positive_two_nonpoint_input_same_model_dictionary421 :
    ∃ p, build = some p ∧ Fits p.state (model false) ∧
      ReportEvidence p.state (model false) p.root selected ∧
      DictionaryEvidence p.state (model false) p.root (.node 57 []) := by
  have yes := actual_shared_binder_accepts_compatible_retained_centers421
  cases got : build with
  | none => simp [probe,got] at yes
  | some p =>
    have checked : check p selected (.repeatedCenters wire) = true := by simpa [probe,got] using yes
    have fit := both_tied_or_conflicting_before_tie_original_states_have_models421 false got
    have report := check_sound p selected _ checked
    exact ⟨p,rfl,fit,report.2 _ fit,dictionary_sound_R13 _ _ _
      (exact_report_is_R13_classification421 report.1) _ fit⟩

theorem actual_negative_pre_state_fits_but_exact_new_tie_is_impossible421 :
    ∃ p, build true false = some p ∧ Fits p.state (model true) ∧
      ClassifiedAs p.state p.root postConflict ∧
      ∃ a : Choice p, readChoice421 p wire.pre = some a ∧ a.tie = exactTie ∧
        ∀ m : I72.Model, ¬ Models (appendFacts p.state.core.current.ordinary [a.tie]) m.assignment := by
  have yes := actual_incompatible_centers_reject_only_after_electing421.1
  cases got : build true false with
  | none => simp [probe,got] at yes
  | some p =>
    have checked : check p postConflict (.repeatedCenters wire) = true := by simpa [probe,got] using yes
    have fit := both_tied_or_conflicting_before_tie_original_states_have_models421 true got
    have report := check_sound p postConflict _ checked
    obtain ⟨a,after,pre,_,result⟩ := accepted_report_has_exact_pre_then_post_evidence421 checked
    have actualArgs : p.root.demand.arguments = [⟨0,1,2⟩,⟨3,4,2⟩] := by
      unfold build at got
      dsimp only at got
      repeat' (first | split at got | contradiction)
      cases Option.some.inj got
      rfl
    have initial := List.cons.inj (a.originalArgs.symm.trans actualArgs)
    have latter := (List.cons.inj initial.2).1
    have tie : a.tie = exactTie := by simp [Choice.tie,initial.1,latter,exactTie]
    cases after with
    | accepted b =>
      have bad : CommonRoleOutermostResolver.Tree.rejected = .selected a.decl.id [] :=
        congrArg (fun r : Result => r.tree) result
      cases bad
    | incompatible b =>
      exact ⟨p,rfl,fit,report.1,a,pre,tie,actual_conflict_makes_selected_batch_unsatisfiable421 b⟩

#print axioms both_nonpoint_inputs_elect_before_reading_center_tie421
#print axioms actual_shared_binder_accepts_compatible_retained_centers421
#print axioms actual_incompatible_centers_reject_only_after_electing421
#print axioms missing_tie_alone_is_neither_rejection_nor_success421
#print axioms witnessed_prechoice_is_not_a_claim_about_another_candidate_or_source421
#print axioms second_raw_root_cycle_still_precedes_center_conflict421
#print axioms both_tied_or_conflicting_before_tie_original_states_have_models421
#print axioms actual_positive_two_nonpoint_input_same_model_dictionary421
#print axioms actual_negative_pre_state_fits_but_exact_new_tie_is_impossible421
end Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421.SpecRepeated
