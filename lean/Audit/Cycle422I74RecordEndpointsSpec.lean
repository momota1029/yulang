import Yulang.GeneralDeclarativeI65I74RecordEndpointsProjectedOutput422

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1200
namespace Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422.SpecRecord
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralDeclarativeHead320 (Equation Models)
open CommonNominalFullCarrier (Ty Subtype Equivalent record observeTy subtype_refl subtype_trans)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (common_record_mono)
open GeneralDeclarativeRecordIntervals330 (direct projected_below)
open Checker408 (Problem)
open ExplicitPick419 (pickSyntax)
open OpenTail414 (openRow openTerm)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def exactBody : GeneralDeclarations.Equation := ⟨92,3,.var 8⟩
def actualImpl : Declaration := ⟨57,7,[pickSyntax 20 8 13],[],[exactBody],[]⟩
def unrelated : Declaration := ⟨58,9,[],[],[],[]⟩
def surface : InputBundle :=
  ⟨⟨.absent,[]⟩,⟨.absent,[]⟩,⟨1,[⟨7,1,[(3,none)]⟩,⟨9,0,[]⟩]⟩,[unrelated,actualImpl]⟩

def lowRow := openRow 0 20 3 5
def highRow := openRow 2 20 4 6
def raw : GeneralDeclarativeHead320.State := ⟨⟨[],[(0,1),(1,2)]⟩,[lowRow,highRow]⟩
def inputOrigins (dropUpper : Bool) : List Origin :=
  [⟨0,[44],openTerm 20 3 5⟩] ++ if dropUpper then [] else [⟨2,[55],openTerm 20 4 6⟩]

def build (dropUpper : Bool := false) : Option Problem := do
  let program ← compile bodies
  let bundle ← GeneralSourceMetadataBareBundle291.compile surface
  let env : Environment := ⟨0,0,0,bodies,program,bundle⟩
  let s : GeneralDeclarativeI65.State := ⟨⟨env,raw,[]⟩,[],inputOrigins dropUpper,[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun q ordinal i body =>
    if q.occurrence == [61,422] && ordinal == 1 && i.val == 0 then
      if h : body = .explicit exactBody then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 s false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit exactBody)))))
      else none
    else none⟩
  pure ⟨⟨s,atlas⟩,⟨[61,422],⟨7,[⟨0,1,2⟩],[⟨3,12⟩]⟩⟩⟩

def wire : Wire := ⟨⟨0,0⟩,⟨1,1⟩,1,⟨[0,0,0,1,1,1,1],[0,1]⟩⟩

theorem endpoint_read_needs_both_authored_origins_but_not_a_center_row422 :
    ((build.map fun p => (readEndpoints422 p wire).isSome).getD false = true) ∧
    (((build true).map fun p => (readEndpoints422 p wire).isSome).getD false = false) ∧
    ((build.map fun p => (readEndpoints422 p {wire with high := ⟨1,0⟩}).isSome).getD false = false) := by
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

def concrete : Problem := build.get (by decide +kernel)
def read : Read concrete := (readEndpoints422 concrete wire).get (by decide +kernel)

theorem actual_literal_binders_and_endpoint_names_are_not_swapped422 :
    read.arg.lower = 0 ∧ read.arg.center = 1 ∧ read.arg.upper = 2 ∧
    read.low.field = 3 ∧ read.high.field = 4 ∧ read.low.residual = 5 ∧
    read.high.residual = 6 ∧ read.fieldBinder = 8 ∧ read.residualBinder = 13 ∧
    read.decl.id = 57 ∧ read.ordinal = 1 := by
  decide +kernel

theorem no_actual_center_record_exists422 : NoCenterRecord read := by
  intro label field tail kept
  rw [actual_literal_binders_and_endpoint_names_are_not_swapped422.2.1] at kept
  change (⟨1,.record label field tail⟩ : Equation) ∈ [lowRow,highRow] at kept
  simp only [List.mem_cons,List.not_mem_nil,or_false] at kept
  rcases kept with h|h <;> cases h

def lowField : Ty := .base .int
def highField : Ty := .union (.base .int) (.base .bool)
def lowTail : Ty := record 21 lowField .emptyRecord
def highTail : Ty := record 21 highField .emptyRecord
def lowTy : Ty := record 20 lowField lowTail
def highTy : Ty := record 20 highField highTail

private theorem leftSubtype (a b : Ty) : Subtype a (.union a b) := by
  intro d
  exact CommonNominalFullDemand.producerLe_union_left (observeTy d a) (observeTy d b)

private theorem rightSubtype (a b : Ty) : Subtype b (.union a b) := by
  intro d
  exact CommonNominalFullDemand.producerLe_union_right (observeTy d a) (observeTy d b)

theorem low_below_high422 : Subtype lowTy highTy :=
  common_record_mono 20 (leftSubtype _ _)
    (common_record_mono 21 (leftSubtype _ _) (subtype_refl _))

private theorem bool_not_below_int : ¬ Subtype (.base .bool) (.base .int) := by
  intro h
  let env : CommonNominalFullDemand.Environment Common.Row := ⟨fun _ => .bottom,fun _ => [.base .int]⟩
  have yes : CommonNominalFullDemand.ProbeAt Common.rowLe 0 env (.base .int) (.role 0) := by
    simp [CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,
      CommonNominalFullDemand.MaskedProbeStep,env]
  have atOne := h 1
  change CommonNominalFullDemand.ProducerLe Common.rowLe (.base .bool) (.base .int) at atOne
  have no := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp atOne 0 env (.role 0) yes
  simp [CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,
    CommonNominalFullDemand.MaskedProbeStep,env] at no

theorem endpoints_have_unequal_semantic_record_types422 : ¬ Equivalent lowTy highTy := by
  intro h
  have wrong : Subtype highField lowField :=
    projected_below 20 false (direct 20 false highField highTail)
      (direct 20 false lowField lowTail) h.2
  exact bool_not_below_int (subtype_trans (rightSubtype _ _) wrong)

def model (upperCenter : Bool) : I72.Model :=
  ⟨fun n =>
      (if n = 0 then lowTy else if n = 1 then (if upperCenter then highTy else lowTy)
       else if n = 2 then highTy else if n = 3 then lowField else if n = 4 then highField
       else if n = 5 then lowTail else if n = 6 then highTail else lowField,Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (openTerm 20 3 5)
      else if n = 2 then some (openTerm 20 4 6) else none⟩

theorem both_distinct_real_centers_fit_the_same_original_source422 (upper : Bool) :
    Fits concrete.state (model upper) := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ none; cases none
  · intro pair kept
    change pair ∈ [(0,1),(1,2)] at kept
    simp only [List.mem_cons,List.not_mem_nil,or_false] at kept
    rcases kept with rfl|rfl
    · cases upper
      · exact subtype_refl _
      · exact low_below_high422
    · cases upper
      · exact low_below_high422
      · exact subtype_refl _
  · intro e kept
    change e ∈ [lowRow,highRow] at kept
    simp only [List.mem_cons,List.not_mem_nil,or_false] at kept
    rcases kept with rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ none; cases none
  · intro o owned
    change o ∈ [⟨0,[44],openTerm 20 3 5⟩,⟨2,[55],openTerm 20 4 6⟩] at owned
    simp only [List.mem_cons,List.not_mem_nil,or_false] at owned
    rcases owned with rfl|rfl <;> rfl

theorem actual_spec_pick_source_cannot_be_added_by_primitive_union422
    (R : SourcePrimitives) (d : CommonRoleOutermostResolver.Dictionary) :
    ¬ I72.Classifies R concrete.state concrete.root (.selected d) := by
  apply primitives_only_cannot_add_genuine_nonpoint_record_selection422
    read no_actual_center_record_exists422 (model false)
    (both_distinct_real_centers_fit_the_same_original_source422 false).1.1
  rw [actual_literal_binders_and_endpoint_names_are_not_swapped422.1,
    actual_literal_binders_and_endpoint_names_are_not_swapped422.2.2.1]
  exact endpoints_have_unequal_semantic_record_types422

theorem original_B6_typed_field_body_is_present422 :
    (concrete.state.b6.read concrete.root 1
      (⟨0,by decide +kernel⟩ : Fin concrete.root.demand.outputs.length)
      (.explicit exactBody)).isSome = true := by decide +kernel

theorem projected_actual_fields_differ_between_fits_of_same_source422 :
    GeneralDeclarativeRecordChannel330.project 20 false [] ((model false).assignment 1).1 = some lowField ∧
    GeneralDeclarativeRecordChannel330.project 20 false [] ((model true).assignment 1).1 = some highField := by
  exact ⟨direct 20 false lowField lowTail,direct 20 false highField highTail⟩

/-- This uses the actual unchanged R13 public entry and its proven
soundness for every witness, not just a wrong attempted locator. -/
theorem unchanged_public_entry_cannot_emit_selected_fixture422
    (out : Checker408.Result) (w : RepeatedCenters421.Witness)
    (d : CommonRoleOutermostResolver.Dictionary) (h : out.verdict = .selected d) :
    RepeatedCenters421.check concrete out w = false := by
  cases checked : RepeatedCenters421.check concrete out w with
  | false => rfl
  | true =>
    have proof := RepeatedCenters421.check_has_exact_original_report421 concrete out w checked
    have selected := RepeatedCenters421.exact_report_is_R13_classification421 proof
    rw [h] at selected
    exact False.elim (actual_spec_pick_source_cannot_be_added_by_primitive_union422 _ _ selected)

open GeneralDeclarativeI65
open CommonNominalFullCarrier (Subtype Equivalent subtype_trans)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDeclarativeRecordIntervals330 (projected_below direct present)
open GeneralDeclarativeRecordChannel330 (project)

/-- Not even a shadow choice of a fixed scalar name could represent the
actual projection across all original fitting models. The two worlds
agree on all of the original names except the whole record center. -/
theorem no_existing_name_can_denote_this_real_field_in_all_fits422 (n : Nat) :
    ¬ (Equivalent ((model false).assignment n).1 lowField ∧
      Equivalent ((model true).assignment n).1 highField) := by
  intro both
  by_cases center : n = 1
  · subst n
    have back : Subtype lowField (CommonNominalFullCarrier.record 20 lowField lowTail) := both.1.2
    obtain ⟨f,h⟩ := present 20 false back
    simp [lowField,project] at h
  · have fixed : ((model false).assignment n).1 = ((model true).assignment n).1 := by
      unfold model
      simp [center]
    rw [fixed] at both
    have same : Equivalent lowField highField := eqv_trans ⟨both.1.2,both.1.1⟩ both.2
    exact endpoints_have_unequal_semantic_record_types422
      (GeneralNominalCenteredHeadMatPatternSemantics.record_congr 20 same
        (GeneralNominalCenteredHeadMatPatternSemantics.record_congr 21 same
          (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _)))

theorem residual_masks_hide_the_actual_captured_label_without_pointing_tail422 :
    let r₀ := CommonNominalFullCarrier.mask [20] ((model false).assignment 1).1
    let r₁ := CommonNominalFullCarrier.mask [20] ((model true).assignment 1).1
    project 20 false [] r₀ = none ∧ project 20 false [] r₁ = none ∧
    project 21 false [] r₀ = some lowField ∧ project 21 false [] r₁ = some highField := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem both_examples_allow_a_separate_named_projection_without_touching_output422 (side : Bool) :
    ∃ next : GeneralNominalCommonBridge.Assignment,
      Models (GeneralDeclarativeRecordNames330.expose concrete.state.core.current.ordinary
        read.arg.center read.low.label read.protected) next ∧
      project read.low.label false [] ((model side).assignment read.arg.center).1 =
        some (next read.fieldNames.center).1 ∧
      GeneralDeclarativeWhere319.InInterval ((model side).assignment 3).1 ((model side).assignment 4).1
        (next read.fieldNames.center).1 ∧
      next 12 = (model side).assignment 12 := by
  have names := actual_literal_binders_and_endpoint_names_are_not_swapped422
  have fieldLabel : read.low.label = 20 := by decide +kernel
  have agreement : GeneralDeclarativeRecordNames330.Agreement read.low.label
      ((model side).assignment read.arg.center).1 := by
    rw [fieldLabel,names.2.1]
    cases side
    · exact ⟨lowField,lowField,direct 20 false lowField lowTail,direct 20 true lowField lowTail,
        eqv_refl _⟩
    · exact ⟨highField,highField,direct 20 false highField highTail,direct 20 true highField highTail,
        eqv_refl _⟩
  obtain ⟨next,models,field,lo,hi,span,_,output⟩ :=
    relative_extension_keeps_real_field_triple_and_fixed_addresses422 read (model side)
      (both_distinct_real_centers_fit_the_same_original_source422 side).1.1 agreement
  refine ⟨next,models,field,?_,?_⟩
  · rw [lo,hi, names.2.2.2.1,names.2.2.2.2.1] at span
    exact span
  · exact output ⟨3,12⟩ (by decide +kernel)

/-- The required/optional channel countermodel now inhabits the *same*
actual authored Pick, not an unrelated hypothetical carrier type. -/
def splitModel : I72.Model :=
  {model false with assignment := fun n =>
    ((if n = 0 then GeneralDeclarativeRecordSplit330.lo 20
      else if n = 1 then GeneralDeclarativeRecordSplit330.hidden 20
      else if n = 2 then GeneralDeclarativeRecordSplit330.hi 20
      else if n = 3 then .bottom
      else if n = 4 then .top
      else .exactEmpty),Common.rowEmpty)}

theorem split_channel_model_fits_the_identical_authored_request422 :
    Fits concrete.state splitModel := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ none; cases none
  · intro pair kept
    change pair ∈ [(0,1),(1,2)] at kept
    simp only [List.mem_cons,List.not_mem_nil,or_false] at kept
    rcases kept with rfl|rfl
    · exact (GeneralDeclarativeRecordSplit330.interval 20).1
    · exact (GeneralDeclarativeRecordSplit330.interval 20).2
  · intro e kept
    change e ∈ [lowRow,highRow] at kept
    simp only [List.mem_cons,List.not_mem_nil,or_false] at kept
    rcases kept with rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ none; cases none
  · intro o owned
    change o ∈ [⟨0,[44],openTerm 20 3 5⟩,⟨2,[55],openTerm 20 4 6⟩] at owned
    simp only [List.mem_cons,List.not_mem_nil,or_false] at owned
    rcases owned with rfl|rfl <;> rfl

theorem same_source_does_not_force_projection_channels_to_agree422 :
    ¬ GeneralDeclarativeRecordNames330.Agreement read.low.label
      (splitModel.assignment read.arg.center).1 := by
  have label : read.low.label = 20 := by decide +kernel
  rw [label,actual_literal_binders_and_endpoint_names_are_not_swapped422.2.1]
  intro ⟨f,o,req,opt,agreement⟩
  have span := GeneralDeclarativeRecordSplit330.interval 20
  obtain ⟨field,tail,recombined⟩ :=
    (GeneralDeclarativeRecordReconstruct330.exact span.1 span.2 req opt).mpr agreement
  exact GeneralDeclarativeRecordSplit330.no_literal 20 field tail recombined

theorem stating_only_fresh_names_does_not_solve_uniform_model_transport422 :
    ¬ (∃ next : GeneralNominalCommonBridge.Assignment,
      Models (GeneralDeclarativeRecordNames330.expose concrete.state.core.current.ordinary
        read.arg.center read.low.label read.protected) next ∧
      (∀ n ∈ GeneralDeclarativeOpaqueNames328.kept concrete.state.core.current.ordinary
        read.arg.center read.protected, next n = splitModel.assignment n)) := by
  intro lifted
  exact same_source_does_not_force_projection_channels_to_agree422
    ((fresh_record_model_extension_exactly_when_channels_agree422 read splitModel).mp lifted).2

/-- Positive substitute for unjustified reassembly: both projected
intervals exist in the actual model that forbids a literal peel. -/
theorem both_channels_exist_in_the_fitting_model_that_forbids_reassembly422 :
    ∃ evidence : ProjectedRecordChannels read splitModel,
      ¬ Equivalent evidence.required evidence.optional := by
  obtain ⟨evidence⟩ := same_model_endpoints_support_both_projected_channels422 read splitModel
    split_channel_model_fits_the_identical_authored_request422.1.1
  refine ⟨evidence,?_⟩
  intro same
  exact same_source_does_not_force_projection_channels_to_agree422
    ⟨evidence.required,evidence.optional,evidence.atRequired,evidence.atOptional,same⟩

/-- The actual split-channel source distinguishes a conservative
two-name projection from fabricating a literal record equation.
This proof keeps the old State and all original targets, yet produces
a fresh assignment (not evidence in the original assignment). -/
theorem same_split_source_admits_fresh_projections_without_a_literal_row422 :
    ∃ (a : ProjectedRecordChannels read splitModel) (next : I72.Model),
      Fits concrete.state next ∧
      next.assignment 1 = splitModel.assignment 1 ∧
      next.assignment 12 = splitModel.assignment 12 ∧
      (next.assignment read.fieldNames.center).1 = a.required ∧
      (next.assignment read.freshTail).1 =
        CommonNominalFullCarrier.mask [read.low.label] (splitModel.assignment read.arg.center).1 ∧
      ¬ Equivalent a.required a.optional := by
  obtain ⟨a,assignment,valid,stable,payload,residue⟩ :=
    fresh_projection_names_exist_without_required_optional_agreement422 read splitModel
      split_channel_model_fits_the_identical_authored_request422.1.1
  let m := {splitModel with assignment := assignment}
  refine ⟨a,m,⟨⟨valid,?_⟩,?_⟩,?_,?_,payload,residue,?_⟩
  · intro _ no; cases no
  · exact split_channel_model_fits_the_identical_authored_request422.2
  · apply stable
    rw [← actual_literal_binders_and_endpoint_names_are_not_swapped422.2.1]
    exact List.mem_append_right _ List.mem_cons_self
  · apply stable
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    change 12 ∈ [read.low.field,read.high.field,read.low.residual,read.high.residual] ++ [12]
    exact List.mem_append_right _ List.mem_cons_self
  · intro same
    exact same_source_does_not_force_projection_channels_to_agree422
      ⟨a.required,a.optional,a.atRequired,a.atOptional,same⟩

theorem exact_compiled_record_endpoint_output_is_found422 :
    (readProjectedOutput422 read).isSome = true := by decide +kernel

def projectedOutput : ProjectedOutput read :=
  (readProjectedOutput422 read).get (by decide +kernel)

theorem original_compiler_RHS_tracks_two_real_center_types_at_one_target422 (high : Bool) :
    projectedOutput.actualRightValue (model high) =
      some ([61,422],1,0,12,if high then highField else lowField) := by
  obtain ⟨w⟩ := same_model_endpoints_support_both_projected_channels422 read (model high)
    (both_distinct_real_centers_fit_the_same_original_source422 high).1.1
  have actual := original_B6_binder_yields_required_projection_and_exact_addresses422 projectedOutput (model high) w
  have center := actual_literal_binders_and_endpoint_names_are_not_swapped422.2.1
  have label : read.low.label = 20 := by decide +kernel
  have projected := w.atRequired
  rw [label,center] at projected
  have exactField : w.required = if high then highField else lowField := by
    cases high
    · exact Option.some.inj (projected.symm.trans projected_actual_fields_differ_between_fits_of_same_source422.1)
    · exact Option.some.inj (projected.symm.trans projected_actual_fields_differ_between_fits_of_same_source422.2)
  have ordinal : read.ordinal = 1 := by decide +kernel
  rw [actual,ordinal,exactField]
  rfl

theorem actual_split_case_also_evaluates_original_B6_without_literal_reassembly422 :
    projectedOutput.actualRightValue splitModel = some ([61,422],1,0,12,.top) := by
  obtain ⟨w,neq⟩ := both_channels_exist_in_the_fitting_model_that_forbids_reassembly422
  have actual := original_B6_binder_yields_required_projection_and_exact_addresses422 projectedOutput splitModel w
  have center := actual_literal_binders_and_endpoint_names_are_not_swapped422.2.1
  have label : read.low.label = 20 := by decide +kernel
  have projected := w.atRequired
  rw [label,center] at projected
  have exactField : w.required = .top :=
    Option.some.inj (projected.symm.trans (GeneralDeclarativeRecordSplit330.required_top 20))
  have ordinal : read.ordinal = 1 := by decide +kernel
  rw [actual,ordinal,exactField]
  rfl

end Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422.SpecRecord

open Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
open SpecRecord
#print axioms primitives_only_cannot_add_genuine_nonpoint_record_selection422
#print axioms endpoint_read_needs_both_authored_origins_but_not_a_center_row422
#print axioms actual_literal_binders_and_endpoint_names_are_not_swapped422
#print axioms no_actual_center_record_exists422
#print axioms low_below_high422
#print axioms endpoints_have_unequal_semantic_record_types422
#print axioms both_distinct_real_centers_fit_the_same_original_source422
#print axioms actual_spec_pick_source_cannot_be_added_by_primitive_union422
#print axioms original_B6_typed_field_body_is_present422
#print axioms projected_actual_fields_differ_between_fits_of_same_source422
#print axioms unchanged_public_entry_cannot_emit_selected_fixture422


#print axioms no_existing_name_can_denote_this_real_field_in_all_fits422

#print axioms residual_masks_hide_the_actual_captured_label_without_pointing_tail422

#print axioms both_examples_allow_a_separate_named_projection_without_touching_output422

#print axioms split_channel_model_fits_the_identical_authored_request422
#print axioms same_source_does_not_force_projection_channels_to_agree422
#print axioms stating_only_fresh_names_does_not_solve_uniform_model_transport422

#print axioms both_channels_exist_in_the_fitting_model_that_forbids_reassembly422

#print axioms same_split_source_admits_fresh_projections_without_a_literal_row422

#print axioms exact_compiled_record_endpoint_output_is_found422
#print axioms original_compiler_RHS_tracks_two_real_center_types_at_one_target422
#print axioms actual_split_case_also_evaluates_original_B6_without_literal_reassembly422
