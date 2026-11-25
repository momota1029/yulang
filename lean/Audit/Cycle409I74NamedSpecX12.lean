import Yulang.GeneralDeclarativeI65I74NamedEntry409

namespace Yulang.GeneralDeclarativeI65.I72.Named409.SpecX12
open GeneralDeclarativeI65 (B6OccurrenceAtlas401)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open Checker408 (Problem Result)

/-- X12 / spec §6 K2: a named recursive enum `tree` with recursive
and base arms. Even with zero type parameters the authored body is
genuinely recursive and the checked role head is the name, not that body. -/
def bodySource : Source 3 0 0 :=
  ⟨[⟨90,[]⟩],
    fun i => if i.val = 0 then .union (.variant 3 (.inl 1)) (.variant 4 (.inl 2))
      else if i.val = 1 then .nominal 90 [] else .base .unit,
    fun i => i.elim0⟩

def implShowTree : Declaration := ⟨88,7,[.app 90 []],[],[],[]⟩

def surfaceInput (authored : Bool := true) : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,if authored then [⟨7,1,[]⟩] else []⟩,[implShowTree]⟩

def problem (authored : Bool := true) : Option Problem := do
  let implemented ← compile bodySource
  let written ← GeneralSourceMetadataBareBundle291.compile (surfaceInput authored)
  let environment : Environment := ⟨3,0,0,bodySource,implemented,written⟩
  let state : GeneralDeclarativeI65.State :=
    ⟨⟨environment,⟨⟨[],[]⟩,[⟨9,.nominal 90 []⟩]⟩,[]⟩,
      List.replicate 91 [],[⟨9,[42],.nominal 90 []⟩],[]⟩
  let b6 : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨state,b6⟩,⟨[27],⟨7,[⟨9,9,9⟩],[]⟩⟩⟩

def expected : Result := Check408.nullaryReport implShowTree

def probe (p : Option Problem := problem) (r : Result := expected)
    (tag : Witness := .bareName ⟨0,[]⟩) : Bool :=
  (p.map fun data => check data r tag).getD false

def changedOrigin (key : Nat) (p : Problem) : Problem :=
  let state := {p.state.core with origins := [⟨9,[42],.nominal key []⟩]}
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  ⟨⟨state,atlas⟩,p.root⟩

def unnamedRawCycle (p : Problem) : Problem :=
  let state := {p.state.core with current := {p.state.core.current with ordinary :=
    {p.state.core.current.ordinary with equations :=
      ⟨9,.variant 13 (.variable 9)⟩ :: p.state.core.current.ordinary.equations}}}
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  ⟨⟨state,atlas⟩,p.root⟩

theorem x12_uses_genuinely_recursive_source_body409 :
    bodySource.bodies 1 = .nominal 90 [] := by rfl

theorem x12_named_recursive_enum_passes_check409 : probe = true := by decide +kernel

theorem x12_wrong_origin_ordinal_is_not_a_named_source409 :
    probe problem expected (.bareName ⟨1,[]⟩) = false := by decide +kernel

theorem x12_matching_width_does_not_supply_wrong_name409 :
    probe ((problem).map (changedOrigin 91)) = false := by decide +kernel

theorem x12_raw_structural_cycle_cannot_be_hidden409 :
    probe ((problem).map unnamedRawCycle) = false := by decide +kernel

theorem x12_wrong_dictionary_is_not_the_original_report409 :
    probe problem {expected with verdict := .selected (.node 89 [])} = false := by decide +kernel

theorem x12_opaque_name_was_unsupported_by_old_check409 :
    probe problem expected (.previous .nullary) = false := by decide +kernel

def model : I72.Model :=
  ⟨fun _ => (CommonNominalFullCarrier.nominal 90 [],Common.rowEmpty),
    fun _ => none,fun n => if n = 9 then some (.nominal 90 []) else none⟩

theorem x12_exact_problem_fits_one_model409 {p : Problem} (got : problem = some p) :
    I72.Fits p.state model := by
  unfold problem at got
  cases sparse : compile bodySource with
  | none => simp [sparse] at got
  | some sem =>
    cases authored : GeneralSourceMetadataBareBundle291.compile (surfaceInput true) with
    | none => simp [sparse,authored] at got
    | some tbl =>
      simp only [sparse,authored,Option.pure_def] at got
      cases got
      refine ⟨⟨⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩,?_⟩,?_⟩
      · intro _ absent; cases absent
      · intro item atRow
        have eq : item = (⟨9,.nominal 90 []⟩ : GeneralDeclarativeHead320.Equation) :=
          List.mem_singleton.mp atRow
        cases eq
        exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
      · intro _ absent; cases absent
      · intro item atOrigin
        have eq : item = (⟨9,[42],.nominal 90 []⟩ : GeneralDeclarativeI65.Origin) :=
          List.mem_singleton.mp atOrigin
        cases eq
        rfl

theorem x12_checked_name_has_real_same_model_dictionary409 :
    ∃ p, problem = some p ∧ check p expected (.bareName ⟨0,[]⟩) = true ∧
      I72.Fits p.state model ∧ I72.DictionaryEvidence p.state model p.root (.node 88 []) := by
  have yes := x12_named_recursive_enum_passes_check409
  unfold probe at yes
  cases got : problem with
  | none => simp [got] at yes
  | some p =>
    have accepted : check p expected (.bareName ⟨0,[]⟩) = true := by simpa [got] using yes
    have fit := x12_exact_problem_fits_one_model409 got
    have same := exact_report_is_R1_classification409 (check_sound p expected _ accepted).1
    exact ⟨p,rfl,accepted,fit,dictionary_sound_R1 _ _ _ same model fit⟩

#print axioms x12_exact_problem_fits_one_model409
#print axioms x12_checked_name_has_real_same_model_dictionary409
#print axioms x12_uses_genuinely_recursive_source_body409
#print axioms x12_named_recursive_enum_passes_check409
#print axioms x12_wrong_origin_ordinal_is_not_a_named_source409
#print axioms x12_matching_width_does_not_supply_wrong_name409
#print axioms x12_raw_structural_cycle_cannot_be_hidden409
#print axioms x12_wrong_dictionary_is_not_the_original_report409
#print axioms x12_opaque_name_was_unsupported_by_old_check409

end Yulang.GeneralDeclarativeI65.I72.Named409.SpecX12
