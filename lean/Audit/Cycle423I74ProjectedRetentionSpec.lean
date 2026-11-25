import Yulang.GeneralDeclarativeI65I74ProjectedRetentionCoherence423

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

/-- The same case with three distinct field addresses: the lower
anchor uses 7, upper uses 10, and literal target equation uses 11. -/
def transportRows : List Equation :=
  [openRow 0 20 3 5,openRow 2 20 4 6,openRow 8 20 7 5,openRow 9 20 10 6,⟨12,.variable 11⟩]

def transportOrigins : List Origin :=
  [⟨0,[44],openTerm 20 3 5⟩,⟨2,[55],openTerm 20 4 6⟩,
   ⟨8,[63],openTerm 20 7 5⟩,⟨9,[79],openTerm 20 10 6⟩]

def transportArcs (noDown noUp : Bool) : List (Nat × Nat) :=
  [(0,1),(1,2),(8,1),(1,9)] ++ (if noDown then [] else [(11,7)]) ++ (if noUp then [] else [(10,11)])

def transportProblem (noDown noUp : Bool := false) : Problem :=
  let core0 := concrete.state.core
  let core1 := {core0 with current := {core0.current with ordinary :=
    ⟨⟨[],transportArcs noDown noUp⟩,transportRows⟩}, origins := transportOrigins}
  let atlas : B6OccurrenceAtlas401 core1 := ⟨fun q decl i body =>
    if q.occurrence == [61,423] && decl == 1 && i.val == 0 then
      if h : body = .explicit authoredBody then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 core1 false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit authoredBody)))))
      else none
    else none⟩
  ⟨⟨core1,atlas⟩,concrete.root⟩

def transportWire : RecordEndpoints422.Wire :=
  ⟨⟨0,0⟩,⟨1,1⟩,1,⟨[0,0,0,1,1,1,1,1,0,0,1,1,1],[0,1]⟩⟩

def transportProbe (p : Problem) : Option Bool := do
  let r ← readEndpoints422 p transportWire
  let _ ← readProjectedOutput422 r
  pure (readTransportedRetention423 r retainedWire).isSome

theorem distinct_names_are_accepted_and_directions_are_checked423 :
    transportProbe transportProblem = some true ∧
    transportProbe (transportProblem true false) = some false ∧
    transportProbe (transportProblem false true) = some false := by
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

def transportRead (noDown noUp : Bool := false) :
    Read (transportProblem noDown noUp) :=
  (readEndpoints422 (transportProblem noDown noUp) transportWire).get (by
    cases noDown <;> cases noUp <;> decide +kernel)

def wiredTransport : TransportedRetained transportRead :=
  (readTransportedRetention423 transportRead retainedWire).get (by decide +kernel)

theorem actual_target_rhs_does_not_substitute_either_anchor_name423 :
    wiredTransport.bracket.lower.field = 7 ∧
    wiredTransport.bracket.upper.field = 10 ∧ wiredTransport.fieldAddress = 11 ∧
    wiredTransport.rowOrdinal = 4 := by decide +kernel

def changedModel (ty : Ty) : I72.Model :=
  ⟨fun n => if n = 10 then (actualField,Common.rowEmpty) else if n = 11 ∨ n = 12
      then (ty,Common.rowEmpty) else (model false).assignment n,
    fun _ => none,
    fun n => if n = 0 then some (openTerm 20 3 5) else if n = 2 then some (openTerm 20 4 6)
      else if n = 8 then some (openTerm 20 7 5) else if n = 9 then some (openTerm 20 10 6) else none⟩

theorem transported_model_fit423 (ty : Ty) (noDown noUp : Bool)
    (down : noDown = false → Subtype ty actualField)
    (up : noUp = false → Subtype actualField ty) :
    I72.Fits (transportProblem noDown noUp).state (changedModel ty) := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ none; cases none
  · intro pair mem
    change pair ∈ transportArcs noDown noUp at mem
    unfold transportArcs at mem
    rcases List.mem_append.mp mem with prev|upper
    · rcases List.mem_append.mp prev with base|lower
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at base
        rcases base with rfl|rfl|rfl|rfl
        · exact lower_then_anchor
        · exact subtype_trans anchorLo_to_anchorHi anchor_then_upper
        · exact subtype_refl _
        · exact anchorLo_to_anchorHi
      · cases noDown
        · obtain rfl := List.mem_singleton.mp lower
          exact down rfl
        · cases lower
    · cases noUp
      · obtain rfl := List.mem_singleton.mp upper
        exact up rfl
      · cases upper
  · intro e mem
    change e ∈ transportRows at mem
    simp only [transportRows,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ none; cases none
  · intro o mem
    change o ∈ transportOrigins at mem
    simp only [transportOrigins,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl <;> rfl

def transportTyped (noDown noUp : Bool := false) : ProjectedOutput (transportRead noDown noUp) :=
  (readProjectedOutput422 (transportRead noDown noUp)).get (by
    cases noDown <;> cases noUp <;> decide +kernel)

theorem original_typed_value_is_independent_of_the_candidate_target_type423
    (ty : Ty) (noDown noUp : Bool)
    (fit : I72.Fits (transportProblem noDown noUp).state (changedModel ty)) :
    (transportTyped noDown noUp).actualRightValue (changedModel ty) =
      some ([61,423],1,0,12,actualField) := by
  let rd := transportRead noDown noUp
  obtain ⟨evidence⟩ := RecordEndpoints422.same_model_endpoints_support_both_projected_channels422
    rd (changedModel ty) fit.1.1
  have actual := RecordEndpoints422.original_B6_binder_yields_required_projection_and_exact_addresses422
    (transportTyped noDown noUp) (changedModel ty) evidence
  have atCenter : rd.arg.center = 1 := by cases noDown <;> cases noUp <;> decide +kernel
  have atLabel : rd.low.label = 20 := by cases noDown <;> cases noUp <;> decide +kernel
  have atDecl : rd.ordinal = 1 := by cases noDown <;> cases noUp <;> decide +kernel
  have projected := evidence.atRequired
  rw [atCenter,atLabel] at projected
  have field : evidence.required = actualField :=
    Option.some.inj (projected.symm.trans (direct 20 false actualField loTail))
  rw [actual,atDecl,field]
  rfl

/-- Both inequalities really matter. Dropping one allows a strictly
different fixed-target type even though the *same source and B6 value*
remain available and the literal output row is present. These are
counterexamples to adding that reader branch without the guard,
not language rejection diagnostics. -/
theorem each_directed_bridge_is_semantically_needed423 :
    (I72.Fits (transportProblem true false).state (changedModel hiField) ∧
      (transportTyped true false).actualRightValue (changedModel hiField) =
        some ([61,423],1,0,12,actualField) ∧
      ¬ Equivalent ((changedModel hiField).assignment 12).1 actualField) ∧
    (I72.Fits (transportProblem false true).state (changedModel loField) ∧
      (transportTyped false true).actualRightValue (changedModel loField) =
        some ([61,423],1,0,12,actualField) ∧
      ¬ Equivalent ((changedModel loField).assignment 12).1 actualField) := by
  have high := transported_model_fit423 hiField true false (fun bad => by cases bad)
    (fun _ => unionLeft _ _)
  have low := transported_model_fit423 loField false true (fun _ => unionLeft _ _)
    (fun bad => by cases bad)
  exact ⟨⟨high,original_typed_value_is_independent_of_the_candidate_target_type423 _ _ _ high,
    fun h => high_not_below_mid h.1⟩,
    ⟨low,original_typed_value_is_independent_of_the_candidate_target_type423 _ _ _ low,
      fun h => mid_not_below_low h.2⟩⟩

theorem actual_transported_aliases_keep_projected_output423 :
    I72.Fits transportProblem.state (changedModel actualField) ∧
    ∃ value : Ty,
      transportTyped.actualRightValue (changedModel actualField) = some ([61,423],1,0,12,value) ∧
      Equivalent ((changedModel actualField).assignment 12).1 value := by
  have fit := transported_model_fit423 actualField false false (fun _ => subtype_refl _)
    (fun _ => subtype_refl _)
  obtain ⟨value,got,eq⟩ := original_projected_B6_fixed_target_survives_distinct_logical_names423
    transportTyped wiredTransport (changedModel actualField) fit
  have ordinal : transportRead.ordinal = 1 := by decide +kernel
  rw [ordinal] at got
  exact ⟨fit,value,got,eq⟩

def pathArcs : List (Nat × Nat) := [(0,1),(1,2),(8,14),(1,15),(11,16),(10,17)]
def pathAtoms : List (PresenceNormalForm.Atom Nat) :=
  [ .tyLe (.var 14) (.var 1), .tyLe (.var 15) (.var 9),
    .tyLe (.var 16) (.var 7), .tyLe (.var 17) (.var 11) ]

def pathProblem : Problem :=
  let core0 := (transportProblem).state.core
  let body := {core0 with current := {core0.current with ordinary :=
    ⟨⟨pathAtoms,pathArcs⟩,transportRows⟩}}
  let atlas : B6OccurrenceAtlas401 body := ⟨fun q decl i equation =>
    if q.occurrence == [61,423] && decl == 1 && i.val == 0 then
      if h : equation = .explicit authoredBody then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 body false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit authoredBody)))))
      else none
    else none⟩
  ⟨⟨body,atlas⟩,concrete.root⟩

def rootPathWire : RecordEndpoints422.Wire :=
  ⟨⟨0,0⟩,⟨1,1⟩,1,⟨[0,0,0,1,1,1,1,1,0,0,1,1,1,0,0,0,1,1],[0,1]⟩⟩
def pathWire : PathWire :=
  ⟨retainedWire,[.interval 2,.ordinary 0],[.interval 3,.ordinary 1],
    [.interval 4,.ordinary 2],[.interval 5,.ordinary 3]⟩
def pathRead : Read pathProblem :=
  (readEndpoints422 pathProblem rootPathWire).get (by decide +kernel)

theorem original_rows_are_followed_as_directed_typed_paths423 :
    (readRetentionPaths423 pathRead pathWire).isSome = true ∧
    (readTransportedRetention423 pathRead retainedWire).isSome = false ∧
    (readRetentionPaths423 pathRead {pathWire with resultToLower := [.interval 4,.ordinary 3]}).isSome = false ∧
    (readRetentionPaths423 pathRead {pathWire with actualToUpper := [.ordinary 1,.interval 3]}).isSome = false ∧
    (readRetentionPaths423 pathRead {pathWire with lowerToActual := [.interval 2]}).isSome = false := by
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · constructor
      · decide +kernel
      · constructor <;> decide +kernel

def pathValue : ProjectedOutput pathRead := (readProjectedOutput422 pathRead).get (by decide +kernel)
def pathRetained : TransportedRetained pathRead := (readRetentionPaths423 pathRead pathWire).get (by decide +kernel)

def pathModel : I72.Model :=
  { changedModel actualField with assignment := fun n =>
      if n = 14 then (anchorLo,Common.rowEmpty)
      else if n = 15 then (anchorHi,Common.rowEmpty)
      else if n = 16 ∨ n = 17 then (actualField,Common.rowEmpty)
      else (changedModel actualField).assignment n }

theorem path_only_constraints_really_fit_the_original_model423 :
    I72.Fits pathProblem.state pathModel := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro e mem
    change e ∈ pathAtoms at mem
    simp only [pathAtoms,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl <;> exact subtype_refl _
  · intro pair mem
    change pair ∈ pathArcs at mem
    simp only [pathArcs,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact lower_then_anchor
    · exact subtype_trans anchorLo_to_anchorHi anchor_then_upper
    · exact subtype_refl _
    · exact anchorLo_to_anchorHi
    · exact subtype_refl _
    · exact subtype_refl _
  · intro e mem
    change e ∈ transportRows at mem
    simp only [transportRows,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ none; cases none
  · intro o mem
    change o ∈ transportOrigins at mem
    simp only [transportOrigins,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl <;> rfl

theorem concrete_located_chains_keep_the_actual_projected_write423 :
    ∃ value : Ty,
      pathValue.actualRightValue pathModel = some ([61,423],1,0,12,value) ∧
      Equivalent (pathModel.assignment 12).1 value := by
  obtain ⟨v,read,same⟩ := original_projected_B6_fixed_target_survives_distinct_logical_names423
    pathValue pathRetained pathModel path_only_constraints_really_fit_the_original_model423
  have ordinal : pathRead.ordinal = 1 := by decide +kernel
  rw [ordinal] at read
  exact ⟨v,read,same⟩

/-- Original authored endpoints and the original B6 plan, plus
separate ordinary *inequalities* pinning only the required result.
There is no ordinary equation at 1 or new center origin. -/
def splitRows : List Equation :=
  [openRow 0 20 3 5,openRow 2 20 4 6,⟨12,.variable 11⟩]
def splitAtoms : List (PresenceNormalForm.Atom Nat) :=
  [requiredLower 20 11 1,requiredUpper 20 11 1]
def splitProblem : Problem :=
  let base := concrete.state.core
  let s := {base with current := {base.current with ordinary :=
    ⟨⟨splitAtoms,[(0,1),(1,2)]⟩,splitRows⟩}, origins := allOrigins.take 2}
  let atlas : B6OccurrenceAtlas401 s := ⟨fun q decl i body =>
    if q.occurrence == [61,423] && decl == 1 && i.val == 0 then
      if h : body = .explicit authoredBody then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 s false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit authoredBody)))))
      else none
    else none⟩
  ⟨⟨s,atlas⟩,concrete.root⟩

def splitWire : ChannelWire := ⟨2,0,1⟩
def splitRead : Read splitProblem :=
  (readEndpoints422 splitProblem transportWire).get (by decide +kernel)
def splitTyped : ProjectedOutput splitRead :=
  (readProjectedOutput422 splitRead).get (by decide +kernel)
def splitKept : RequiredOnlyRetained splitRead :=
  (readRequiredChannelRetention423 splitRead splitWire).get (by decide +kernel)

theorem channel_reader_checks_literal_split_constraints_and_target423 :
    (readRequiredChannelRetention423 splitRead splitWire).isSome = true ∧
    (readRequiredChannelRetention423 splitRead {splitWire with lowerOrdinal := 1}).isSome = false ∧
    (readRequiredChannelRetention423 splitRead {splitWire with upperOrdinal := 0}).isSome = false ∧
    (readRequiredChannelRetention423 splitRead {splitWire with targetOrdinal := 1}).isSome = false := by
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · constructor <;> decide +kernel

def splitModel : I72.Model :=
  ⟨fun n =>
    ((if n = 0 then GeneralDeclarativeRecordSplit330.lo 20
      else if n = 1 then GeneralDeclarativeRecordSplit330.hidden 20
      else if n = 2 then GeneralDeclarativeRecordSplit330.hi 20
      else if n = 3 then .bottom
      else if n = 4 ∨ n = 11 ∨ n = 12 then .top
      else .exactEmpty),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (openTerm 20 3 5)
      else if n = 2 then some (openTerm 20 4 6) else none⟩

theorem original_split_model_fits_with_exact_required_target_constraints423 :
    I72.Fits splitProblem.state splitModel := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro atom mem
    change atom ∈ splitAtoms at mem
    simp only [splitAtoms,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact subtype_refl _
    · exact (GeneralDeclarativeRecordSplit330.interval 20).2
  · intro pair mem
    change pair ∈ [(0,1),(1,2)] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact (GeneralDeclarativeRecordSplit330.interval 20).1
    · exact (GeneralDeclarativeRecordSplit330.interval 20).2
  · intro e mem
    change e ∈ splitRows at mem
    simp only [splitRows,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ none; cases none
  · intro o mem
    change o ∈ [⟨0,[44],openTerm 20 3 5⟩,⟨2,[55],openTerm 20 4 6⟩] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl <;> rfl

theorem required_B6_target_is_retained_in_an_actual_unequal_channel_fit423 :
    ∃ e : RecordEndpoints422.ProjectedRecordChannels splitRead splitModel,
      splitTyped.actualRightValue splitModel = some ([61,423],1,0,12,e.required) ∧
      Equivalent (splitModel.assignment 12).1 e.required ∧
      ¬ Equivalent e.required e.optional := by
  have fit := original_split_model_fits_with_exact_required_target_constraints423
  obtain ⟨e⟩ := RecordEndpoints422.same_model_endpoints_support_both_projected_channels422
    splitRead splitModel fit.1.1
  have ast := RecordEndpoints422.original_B6_binder_yields_required_projection_and_exact_addresses422
    splitTyped splitModel e
  have stored := retained_target_can_equal_required_projection_without_collapsing_optional423
    splitKept splitModel fit.1.1 e
  have ordinal : splitRead.ordinal = 1 := by decide +kernel
  rw [ordinal] at ast
  refine ⟨e,ast,stored,?_⟩
  intro equal
  obtain ⟨f,t,literalEq⟩ :=
    (RecordEndpoints422.projected_certificate_reassembles_exact_record_iff_its_channels_agree422
      splitRead splitModel fit.1.1 e).mpr equal
  have center : splitRead.arg.center = 1 := by decide +kernel
  have label : splitRead.low.label = 20 := by decide +kernel
  rw [center,label] at literalEq
  exact GeneralDeclarativeRecordSplit330.no_literal 20 _ _ literalEq

def sharedInput : PrepareWire := ⟨rootWire,.shared retainedWire⟩
def transportInput : PrepareWire := ⟨transportWire,.directed retainedWire⟩
def pathInput : PrepareWire := ⟨rootPathWire,.located pathWire⟩
def splitInput : PrepareWire := ⟨transportWire,.requiredChannel splitWire⟩
def absentB6 : Problem := ⟨⟨concrete.state.core,⟨fun _ _ _ _ => none⟩⟩,concrete.root⟩

theorem actual_prepare_pipeline_on_four_fixed_target_shapes423 :
    (readRetainedPickWrite423 concrete sharedInput).isSome = true ∧
    (readRetainedPickWrite423 transportProblem transportInput).isSome = true ∧
    (readRetainedPickWrite423 pathProblem pathInput).isSome = true ∧
    (readRetainedPickWrite423 splitProblem splitInput).isSome = true ∧
    (readRetainedPickWrite423 absentB6 sharedInput).isSome = false ∧
    (readRetainedPickWrite423 pathProblem ⟨rootPathWire,.directed retainedWire⟩).isSome = false := by
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · constructor
      · decide +kernel
      · constructor
        · decide +kernel
        · constructor <;> decide +kernel

def preparedSplit : PreparedWrite splitProblem :=
  (readRetainedPickWrite423 splitProblem splitInput).get (by decide +kernel)

theorem actual_prepare_entry_preserves_literal_target_coordinate_and_semantic_value423 :
    preparedSplit.retained.rowAt = (2,11) ∧
    ∃ evidence : RecordEndpoints422.ProjectedRecordChannels preparedSplit.original splitModel,
      preparedSplit.typed.actualRightValue splitModel =
        some ([61,423],1,0,12,evidence.required) ∧
      Equivalent (splitModel.assignment 12).1 evidence.required ∧
      ¬ Equivalent evidence.required evidence.optional := by
  constructor
  · decide +kernel
  · have m := original_split_model_fits_with_exact_required_target_constraints423
    obtain ⟨each,value,eq⟩ :=
      prepared_write_preserves_full_projected_capture_and_actual_value423 preparedSplit splitModel m
    have ordinal : preparedSplit.original.ordinal = 1 := by decide +kernel
    rw [ordinal] at value
    refine ⟨each,value,eq,?_⟩
    intro same
    obtain ⟨field,tail,whole⟩ :=
      (RecordEndpoints422.projected_certificate_reassembles_exact_record_iff_its_channels_agree422
        preparedSplit.original splitModel m.1.1 each).mpr same
    have center : preparedSplit.original.arg.center = 1 := by decide +kernel
    have label : preparedSplit.original.low.label = 20 := by decide +kernel
    rw [center,label] at whole
    exact GeneralDeclarativeRecordSplit330.no_literal 20 _ _ whole

/-- Two physically different retained rows of the same demanded
target, and two different verification routes, on one actual State. -/
def secondRow : Equation := ⟨12,.variable 7⟩
def twoRows : Problem :=
  let base := transportProblem.state.core
  let s := {base with current := {base.current with ordinary :=
    {base.current.ordinary with equations := transportRows ++ [secondRow]}}}
  let atlas : B6OccurrenceAtlas401 s := ⟨fun q decl i body =>
    if q.occurrence == [61,423] && decl == 1 && i.val == 0 then
      if h : body = .explicit authoredBody then
        some (h.symm ▸ (MixedRhs401.binder 8 () : B6MixedRhs401 s false
          (GeneralDeclarationPatterns.normalize (GeneralDeclarativeOutputs320.bodyPattern (.explicit authoredBody)))))
      else none
    else none⟩
  ⟨⟨s,atlas⟩,concrete.root⟩

def alternativeInput : PrepareWire :=
  ⟨transportWire,.located ⟨{retainedWire with targetRow := 5},[.interval 2],[.interval 3],[],
    [.interval 5,.interval 4]⟩⟩

def firstReceipt : PreparedWrite twoRows :=
  (readRetainedPickWrite423 twoRows transportInput).get (by decide +kernel)
def otherReceipt : PreparedWrite twoRows :=
  (readRetainedPickWrite423 twoRows alternativeInput).get (by decide +kernel)

theorem actual_distinct_rows_and_paths_do_not_change_semantic_write423 :
    firstReceipt.retained.rowAt = (4,11) ∧ otherReceipt.retained.rowAt = (5,7) ∧
    (∀ m : I72.Model, I72.Fits twoRows.state m →
      firstReceipt.typed.actualRightValue m = otherReceipt.typed.actualRightValue m) := by
  exact ⟨by decide +kernel,by decide +kernel,
    fun m fit => different_prepared_evidence_keeps_the_same_actual_write423 firstReceipt otherReceipt m fit⟩

theorem simultaneous_original_receipts_have_a_fitting_model423 :
    I72.Fits twoRows.state (changedModel actualField) := by
  have original := transported_model_fit423 actualField false false (fun _ => subtype_refl _)
    (fun _ => subtype_refl _)
  refine ⟨⟨⟨original.1.1.1,?_⟩,original.1.2⟩,original.2⟩
  intro row atRow
  change row ∈ transportRows ++ [secondRow] at atRow
  rcases List.mem_append.mp atRow with prior|extra
  · exact original.1.1.2 _ prior
  · obtain rfl := List.mem_singleton.mp extra
    exact ⟨subtype_refl _,subtype_refl _⟩

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

#print axioms distinct_names_are_accepted_and_directions_are_checked423
#print axioms actual_target_rhs_does_not_substitute_either_anchor_name423
#print axioms transported_model_fit423
#print axioms original_typed_value_is_independent_of_the_candidate_target_type423
#print axioms each_directed_bridge_is_semantically_needed423
#print axioms actual_transported_aliases_keep_projected_output423

#print axioms original_rows_are_followed_as_directed_typed_paths423
#print axioms path_only_constraints_really_fit_the_original_model423
#print axioms concrete_located_chains_keep_the_actual_projected_write423

#print axioms channel_reader_checks_literal_split_constraints_and_target423
#print axioms original_split_model_fits_with_exact_required_target_constraints423
#print axioms required_B6_target_is_retained_in_an_actual_unequal_channel_fit423

#print axioms actual_prepare_pipeline_on_four_fixed_target_shapes423
#print axioms actual_prepare_entry_preserves_literal_target_coordinate_and_semantic_value423

#print axioms actual_distinct_rows_and_paths_do_not_change_semantic_write423
#print axioms simultaneous_original_receipts_have_a_fitting_model423
