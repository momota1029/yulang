import Yulang.GeneralDeclarativeI65I74ProjectedRetentionMeaning423

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1600
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec
open GeneralDeclarativeI65
open RecordEndpoints422 (readEndpoints422 Read readProjectedOutput422 ProjectedOutput NoCenterRecord)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open CommonNominalFullCarrier (Ty record Equivalent Subtype subtype_refl subtype_trans
  common_record_mono observeTy)
open GeneralDeclarativeRecordIntervals330 (direct projected_below)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open OpenTail414 (openRow openTerm)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open Checker408 (Problem)
open ExplicitPick419 (pickSyntax)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def authoredBody : GeneralDeclarations.Equation := ⟨92,3,.var 8⟩
def impl : Declaration := ⟨57,7,[pickSyntax 20 8 13],[],[authoredBody],[]⟩
def unrelated : Declaration := ⟨58,9,[],[],[],[]⟩
def surface : InputBundle :=
  ⟨⟨.absent,[]⟩,⟨.absent,[]⟩,⟨1,[⟨7,1,[(3,none)]⟩,⟨9,0,[]⟩]⟩,[unrelated,impl]⟩

def outRow : Equation := ⟨12,.variable 7⟩
def rootRows : List Equation :=
  [openRow 0 20 3 5,openRow 2 20 4 6,openRow 8 20 7 5,openRow 9 20 7 6]
def allOrigins : List Origin :=
  [⟨0,[44],openTerm 20 3 5⟩,⟨2,[55],openTerm 20 4 6⟩,
   ⟨8,[63],openTerm 20 7 5⟩,⟨9,[79],openTerm 20 7 6⟩]
def outputRows (mode : Nat) : List Equation :=
  if mode = 0 then [outRow] else if mode = 1 then [] else
    if mode = 2 then [⟨12,.variable 4⟩] else [⟨13,.variable 7⟩]

def raw (mode : Nat := 0) (withTightBounds : Bool := true) :
    GeneralDeclarativeHead320.State :=
  ⟨⟨[],[(0,1),(1,2)] ++ if withTightBounds then [(8,1),(1,9)] else []⟩,
    rootRows ++ outputRows mode⟩

def build (mode : Nat := 0) (withTightBounds : Bool := true) (withAnchorOrigins : Bool := true) :
    Option Problem := do
  let program ← compile bodies
  let bundle ← GeneralSourceMetadataBareBundle291.compile surface
  let env : Environment := ⟨0,0,0,bodies,program,bundle⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨env,raw mode withTightBounds,[]⟩,[],if withAnchorOrigins then allOrigins else allOrigins.take 2,[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun q decl i body =>
    if q.occurrence == [61,423] && decl == 1 && i.val == 0 then
      if h : body = .explicit authoredBody then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 s false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit authoredBody)))))
      else none
    else none⟩
  pure ⟨⟨s,atlas⟩,⟨[61,423],⟨7,[⟨0,1,2⟩],[⟨3,12⟩]⟩⟩⟩

def rootWire : RecordEndpoints422.Wire :=
  ⟨⟨0,0⟩,⟨1,1⟩,1,⟨[0,0,0,1,1,1,1,1,0,0,0,0,1,1],[0,1]⟩⟩
def retainedWire : Wire := ⟨8,9,⟨2,2⟩,⟨3,3⟩,4⟩
def probe (p : Option Problem := build) (w : Wire := retainedWire) : Option Bool := do
  let original ← p
  let r ← readEndpoints422 original rootWire
  let _ ← readProjectedOutput422 r
  pure (readAnchoredRetention423 r w).isSome

theorem independent_source_and_B6_do_not_fake_retention423 :
    probe = some true ∧
    probe (build 1) = some false ∧
    probe (build 2) = some false ∧
    probe (build 3) = some false ∧
    probe (build 0 false) = some false ∧
    probe (build 0 true false) = some false ∧
    probe build {retainedWire with targetRow := 3} = some false := by
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · constructor
      · decide +kernel
      · constructor
        · decide +kernel
        · constructor
          · decide +kernel
          · constructor <;> decide +kernel

def concrete : Problem := build.get (by decide +kernel)
def source : Read concrete := (readEndpoints422 concrete rootWire).get (by decide +kernel)
def typed : ProjectedOutput source := (readProjectedOutput422 source).get (by decide +kernel)
def retained : Retained source := (readAnchoredRetention423 source retainedWire).get (by decide +kernel)

theorem all_original_addresses_survive_the_tighter_bounds423 :
    source.arg.lower = 0 ∧ source.arg.center = 1 ∧ source.arg.upper = 2 ∧
    source.low.field = 3 ∧ source.high.field = 4 ∧ source.ordinal = 1 ∧
    retained.anchors.lower.field = 7 ∧ retained.anchors.upper.field = 7 ∧
    retained.anchors.lowerName = 8 ∧ retained.anchors.upperName = 9 ∧
    retained.rowOrdinal = 4 := by
  decide +kernel

theorem no_stored_record_at_actual_center423 : NoCenterRecord source := by
  intro k l r present
  rw [all_original_addresses_survive_the_tighter_bounds423.2.1] at present
  change (⟨1,.record k l r⟩ : Equation) ∈
    [openRow 0 20 3 5,openRow 2 20 4 6,openRow 8 20 7 5,openRow 9 20 7 6,outRow] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with h|h|h|h|h <;> cases h

def loField : Ty := .base .int
def actualField : Ty := .union (.base .int) (.base .bool)
def hiField : Ty := .union actualField (.base .str)
def loTail : Ty := record 21 loField .emptyRecord
def hiTail : Ty := record 21 actualField .emptyRecord
def loType : Ty := record 20 loField loTail
def hiType : Ty := record 20 hiField hiTail
def anchorLo : Ty := record 20 actualField loTail
def anchorHi : Ty := record 20 actualField hiTail

private theorem unionLeft (a b : Ty) : Subtype a (.union a b) := by
  intro d
  exact CommonNominalFullDemand.producerLe_union_left (observeTy d a) (observeTy d b)

private theorem unionRight (a b : Ty) : Subtype b (.union a b) := by
  intro d
  exact CommonNominalFullDemand.producerLe_union_right (observeTy d a) (observeTy d b)

private theorem lower_then_anchor : Subtype loType anchorLo :=
  common_record_mono 20 (unionLeft _ _) (subtype_refl _)

private theorem anchorLo_to_anchorHi : Subtype anchorLo anchorHi :=
  common_record_mono 20 (subtype_refl _)
    (common_record_mono 21 (unionLeft _ _) (subtype_refl _))

private theorem anchor_then_upper : Subtype anchorHi hiType :=
  common_record_mono 20 (unionLeft _ _) (subtype_refl _)

def model (largeTail : Bool) : I72.Model :=
  ⟨fun n =>
    ((if n = 0 then loType else if n = 1 then (if largeTail then anchorHi else anchorLo)
      else if n = 2 then hiType else if n = 3 then loField else if n = 4 then hiField
      else if n = 5 then loTail else if n = 6 then hiTail
      else if n = 7 ∨ n = 12 then actualField else if n = 8 then anchorLo
      else if n = 9 then anchorHi else .base .int),Common.rowEmpty),
    fun _ => none,fun n =>
      if n = 0 then some (openTerm 20 3 5) else if n = 2 then some (openTerm 20 4 6)
      else if n = 8 then some (openTerm 20 7 5) else if n = 9 then some (openTerm 20 7 6) else none⟩

theorem both_retained_states_fit_the_same_original_problem423 (large : Bool) :
    I72.Fits concrete.state (model large) := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ none; cases none
  · intro pair kept
    change pair ∈ [(0,1),(1,2),(8,1),(1,9)] at kept
    simp only [List.mem_cons,List.not_mem_nil,or_false] at kept
    rcases kept with rfl|rfl|rfl|rfl <;> cases large
    · exact lower_then_anchor
    · exact subtype_trans lower_then_anchor anchorLo_to_anchorHi
    · exact subtype_trans anchorLo_to_anchorHi anchor_then_upper
    · exact anchor_then_upper
    · exact subtype_refl _
    · exact anchorLo_to_anchorHi
    · exact anchorLo_to_anchorHi
    · exact subtype_refl _
  · intro e kept
    change e ∈ [openRow 0 20 3 5,openRow 2 20 4 6,openRow 8 20 7 5,openRow 9 20 7 6,outRow] at kept
    simp only [List.mem_cons,List.not_mem_nil,or_false] at kept
    rcases kept with rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ none; cases none
  · intro o kept
    change o ∈ allOrigins at kept
    simp only [allOrigins,List.mem_cons,List.not_mem_nil,or_false] at kept
    rcases kept with rfl|rfl|rfl|rfl <;> rfl

private theorem mid_not_below_low : ¬ Subtype actualField loField := by
  intro h
  let env : CommonNominalFullDemand.Environment Common.Row := ⟨fun _ => .bottom,fun _ => [.base .int]⟩
  have yes : CommonNominalFullDemand.ProbeAt Common.rowLe 0 env (observeTy 1 loField) (.role 0) := by
    simp [loField,env,observeTy,CommonNominalSyntax.Layer.evalAt,
      CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep]
  have bad := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (h 1) 0 env (.role 0) yes
  simp [actualField,env,observeTy,CommonNominalSyntax.Layer.evalAt,
    CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at bad

private theorem high_not_below_mid : ¬ Subtype hiField actualField := by
  intro h
  let env : CommonNominalFullDemand.Environment Common.Row :=
    ⟨fun _ => .bottom,fun _ => [.base .int,.base .bool]⟩
  have yes : CommonNominalFullDemand.ProbeAt Common.rowLe 0 env (observeTy 1 actualField) (.role 0) := by
    simp [actualField,env,observeTy,CommonNominalSyntax.Layer.evalAt,
      CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep]
  have bad := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (h 1) 0 env (.role 0) yes
  simp [hiField,actualField,env,observeTy,CommonNominalSyntax.Layer.evalAt,
    CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at bad

theorem real_projected_field_differs_from_both_authored_endpoint_fields423 :
    ¬ Equivalent actualField loField ∧ ¬ Equivalent actualField hiField :=
  ⟨fun h => mid_not_below_low h.1,fun h => high_not_below_mid h.2⟩

theorem projected_field_stays_fixed_but_real_residual_varies423 :
    project 20 false [] ((model false).assignment 1).1 = some actualField ∧
    project 20 false [] ((model true).assignment 1).1 = some actualField ∧
    ¬ Equivalent ((model false).assignment 1).1 ((model true).assignment 1).1 := by
  refine ⟨direct 20 false actualField loTail,direct 20 false actualField hiTail,?_⟩
  intro h
  have known : project 21 false [] ((model true).assignment 1).1 = some actualField := rfl
  have different : project 21 false [] ((model false).assignment 1).1 = some loField := rfl
  exact mid_not_below_low (projected_below 21 false known different h.2)

theorem actual_B6_associated_field_is_retained_in_two_different_models423 (large : Bool) :
    typed.actualRightValue (model large) = some ([61,423],1,0,12,actualField) ∧
    Equivalent ((model large).assignment 12).1 actualField := by
  have fit := both_retained_states_fit_the_same_original_problem423 large
  obtain ⟨seen⟩ := RecordEndpoints422.same_model_endpoints_support_both_projected_channels422
    source (model large) fit.1.1
  have f := RecordEndpoints422.original_B6_binder_yields_required_projection_and_exact_addresses422 typed (model large) seen
  have center : source.arg.center = 1 := all_original_addresses_survive_the_tighter_bounds423.2.1
  have label : source.low.label = 20 := by decide +kernel
  have actual := seen.atRequired
  rw [center,label] at actual
  have value : seen.required = actualField := by
    cases large
    · exact Option.some.inj (actual.symm.trans projected_field_stays_fixed_but_real_residual_varies423.1)
    · exact Option.some.inj (actual.symm.trans projected_field_stays_fixed_but_real_residual_varies423.2.1)
  have ordinal : source.ordinal = 1 := by decide +kernel
  rw [ordinal,value] at f
  exact ⟨f,⟨subtype_refl _,subtype_refl _⟩⟩

theorem exact_target_retention_does_not_supply_missing_fixed_head423
    (R : SourcePrimitives) (d : CommonRoleOutermostResolver.Dictionary) :
    ¬ I72.Classifies R concrete.state concrete.root (.selected d) := by
  apply RecordEndpoints422.primitives_only_cannot_add_genuine_nonpoint_record_selection422
    source no_stored_record_at_actual_center423 (model false)
    (both_retained_states_fit_the_same_original_problem423 false).1.1
  rw [all_original_addresses_survive_the_tighter_bounds423.1,
    all_original_addresses_survive_the_tighter_bounds423.2.2.1]
  change ¬ Equivalent loType hiType
  intro assumed
  have bad := projected_below 20 false (direct 20 false hiField hiTail)
    (direct 20 false loField loTail) assumed.2
  exact mid_not_below_low (subtype_trans (unionLeft _ _) bad)

theorem unchanged_R13_entry_cannot_select_even_with_retained_projection423 (report : Checker408.Result)
    (wire : RepeatedCenters421.Witness) (dictionary : CommonRoleOutermostResolver.Dictionary)
    (selected : report.verdict = .selected dictionary) :
    RepeatedCenters421.check concrete report wire = false := by
  cases accepted : RepeatedCenters421.check concrete report wire with
  | false => rfl
  | true =>
    have exact := RepeatedCenters421.exact_report_is_R13_classification421
      (RepeatedCenters421.check_has_exact_original_report421 concrete report wire accepted)
    rw [selected] at exact
    exact False.elim (exact_target_retention_does_not_supply_missing_fixed_head423 _ _ exact)

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec

open Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423.Spec
#print axioms independent_source_and_B6_do_not_fake_retention423
#print axioms all_original_addresses_survive_the_tighter_bounds423
#print axioms no_stored_record_at_actual_center423
#print axioms both_retained_states_fit_the_same_original_problem423
#print axioms real_projected_field_differs_from_both_authored_endpoint_fields423
#print axioms projected_field_stays_fixed_but_real_residual_varies423
#print axioms actual_B6_associated_field_is_retained_in_two_different_models423
#print axioms exact_target_retention_does_not_supply_missing_fixed_head423
#print axioms unchanged_R13_entry_cannot_select_even_with_retained_projection423
