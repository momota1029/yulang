import Yulang.GeneralDeclarativeI65B6SelectedChild399

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (All₂)
open GeneralDeclarations (Declaration Equation)
open GeneralDeclarationPatterns (normalize normalizeArgs variablesArgs Pattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry Joined point)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies)

/-- The current positive unary covariant join head binds both written
payload names to the genuinely observed merged payload center. Values
outside those lexical input names cannot be read by the head. -/
def joinedPreoutputInput399 {c d row} (joined : Joined c d row)
    (outside : Nat → Capture) (name : Nat) : Capture :=
  if name = joined.firstBinder ∨ name = joined.lastBinder then point joined.actualValue else outside name

theorem joined_input_names_exact399 {c d row} (joined : Joined c d row) :
    row.inputNames = [joined.firstBinder,joined.lastBinder] := by
  simp [Declaration.inputNames,joined.head,normalizeArgs,joined.normalized,variablesArgs,Pattern.variables]

theorem joined_original_payload_capture399 {c d row} (joined : Joined c d row)
    (outside : Nat → Capture) {n : Nat} (input : n ∈ row.inputNames) :
    joinedPreoutputInput399 joined outside n = point joined.actualValue := by
  rw [joined_input_names_exact399 joined] at input
  have lexical : n = joined.firstBinder ∨ n = joined.lastBinder := by simpa using input
  simp [joinedPreoutputInput399,lexical]

/-- This pre-output readback uses the actual stored positive source
head, not a current model or a reported successful write. -/
def preoutputInputOfHead399 {s q row} (head : SourceHead s q row)
    (outside : Nat → Capture) : Nat → Capture :=
  match head with
  | .ordered input _ => input
  | .joined joined => joinedPreoutputInput399 joined outside

def preoutputFrameOfOrigin399 {s q row}
    {t : CandidateTape s q (visible s q)} (origin : SelectedHeadOrigin395 (row := row) t)
    (place : Placement) (outside : Nat → Capture) : AuthoredBodyFrame393 s q :=
  frameAtSource395 origin.pick.inScope origin.rawOrdinal origin.authored place
    (preoutputInputOfHead399 origin.pick.head outside)

theorem exact_origin_preoutput_fields399 {s q row}
    {t : CandidateTape s q (visible s q)} (origin : SelectedHeadOrigin395 (row := row) t)
    (place : Placement) (outside : Nat → Capture) :
    let frame := preoutputFrameOfOrigin399 origin place outside
    frame.decl = row ∧ frame.ordinal = origin.rawOrdinal ∧
      StoredAt395 t origin.pick origin.visibleOrdinal ∧
      (authoredRegistry s.current).declarations[frame.ordinal]? = some frame.decl :=
  ⟨rfl,rfl,origin.stored,origin.authored⟩

theorem ordered_origin_reads_exact_lexical_slot399 {s q row}
    {t : CandidateTape s q (visible s q)} (origin : SelectedHeadOrigin395 (row := row) t)
    {input : Nat → Capture} {observed : All₂ (DeepHead s input) q.demand.arguments row.head}
    (ordered : origin.pick.head = .ordered input observed)
    (place : Placement) (outside : Nat → Capture)
    (separate : row.OutputOnly) (body : Equation) {n : Nat} (used : n ∈ row.inputNames) :
    (preoutputFrameOfOrigin399 origin place outside).slots (.explicit body) n = some (input n) := by
  have exactSlot := explicit_authored_head_slot395 (preoutputFrameOfOrigin399 origin place outside)
    separate (body := body) n used
  change _ = some ((preoutputInputOfHead399 origin.pick.head outside) n) at exactSlot
  simpa only [ordered,preoutputInputOfHead399] using exactSlot

theorem joined_origin_reads_actual_merged_payload399 {s q row}
    {t : CandidateTape s q (visible s q)} (origin : SelectedHeadOrigin395 (row := row) t)
    {joined : Joined s.current q.demand row} (retains : origin.pick.head = .joined joined)
    (place : Placement) (outside : Nat → Capture)
    (separate : row.OutputOnly) (body : Equation) {n : Nat} (used : n ∈ row.inputNames) :
    (preoutputFrameOfOrigin399 origin place outside).slots (.explicit body) n =
      some (point joined.actualValue) := by
  have exactSlot := explicit_authored_head_slot395 (preoutputFrameOfOrigin399 origin place outside)
    separate (body := body) n used
  change _ = some ((preoutputInputOfHead399 origin.pick.head outside) n) at exactSlot
  rw [retains,preoutputInputOfHead399,joined_original_payload_capture399 joined outside used] at exactSlot
  exact exactSlot

private theorem join_inputs_independent399 {s q row} (head : SourceHead s q row)
    (a b : Nat → Capture) (n : Nat) (used : n ∈ row.inputNames) :
    preoutputInputOfHead399 head a n = preoutputInputOfHead399 head b n := by
  cases head with
  | ordered input _ => rfl
  | joined joined =>
    exact (joined_original_payload_capture399 joined a used).trans
      (joined_original_payload_capture399 joined b used).symm

/-- The unobservable total-function padding is not used even by the
where-output binders. The table has only actual lexical names and
existing source-determined where target names. -/
theorem origin_frame_capture_table_independent_outside399 {s q row}
    {t : CandidateTape s q (visible s q)} (origin : SelectedHeadOrigin395 (row := row) t)
    (place : Placement) (a b : Nat → Capture) :
    (preoutputFrameOfOrigin399 origin place a).captures =
      (preoutputFrameOfOrigin399 origin place b).captures := by
  change (row.inputNames ++ row.outputNames).map (fun n => (n,
    (GeneralDeclarativeFrameReadback325.sourceNames row place
      (preoutputInputOfHead399 origin.pick.head a)).input n)) =
    (row.inputNames ++ row.outputNames).map (fun n => (n,
    (GeneralDeclarativeFrameReadback325.sourceNames row place
      (preoutputInputOfHead399 origin.pick.head b)).input n))
  apply List.map_congr_left
  intro n used
  rcases List.mem_append.mp used with input|output
  · by_cases named : n ∈ row.outputNames
    · simp [GeneralDeclarativeFrameReadback325.sourceNames,GeneralDeclarativeProducedNames325.table,named]
    · simp [GeneralDeclarativeFrameReadback325.sourceNames,GeneralDeclarativeProducedNames325.table,named,
        join_inputs_independent399 origin.pick.head a b n input]
  · simp [GeneralDeclarativeFrameReadback325.sourceNames,GeneralDeclarativeProducedNames325.table,output]

theorem origin_frame_slots_independent_outside399 {s q row}
    {t : CandidateTape s q (visible s q)} (origin : SelectedHeadOrigin395 (row := row) t)
    (place : Placement) (a b : Nat → Capture) (body : Body) :
    (preoutputFrameOfOrigin399 origin place a).slots body =
      (preoutputFrameOfOrigin399 origin place b).slots body := by
  funext n
  cases body with
  | explicit eq =>
    simp only [AuthoredBodyFrame393.slots,origin_frame_capture_table_independent_outside399 origin place a b]
  | default role name term => rfl

/-- From a genuine positive complete candidate tape get the original
selected declaration and its B4 frame before any output is written.
This is not a converse from the erased diagnostic summary. -/
theorem positive_tape_produces_original_frame399 {s q row}
    {t : CandidateTape s q (visible s q)} (only : TapedMatch s q t row)
    (place : Placement) (outside : Nat → Capture) :
    ∃ origin : SelectedHeadOrigin395 (row := row) t,
      let frame := preoutputFrameOfOrigin399 origin place outside
      frame.decl = row ∧ frame.ordinal = origin.rawOrdinal ∧
        StoredAt395 t origin.pick origin.visibleOrdinal ∧
        (authoredRegistry s.current).declarations[frame.ordinal]? = some row := by
  obtain ⟨origin⟩ := selected_head_original_origin395 only
  exact ⟨origin,exact_origin_preoutput_fields399 origin place outside⟩


open GeneralDeclarativeSourceEmission322 (Names useArg useOutput inputs demand)

private theorem inputs_read_lexical_only399 (first last : Names)
    (compound : Nat → Capture) (i : Nat) (ps : List Pattern)
    (actual : ∀ p ∈ ps, ∀ n, normalize p = .var n → first.input n = last.input n) :
    inputs first compound i ps = inputs last compound i ps := by
  induction ps generalizing i with
  | nil => rfl
  | cons p rest ih =>
    have front : useArg first (compound i) p = useArg last (compound i) p := by
      cases normalized : normalize p with
      | var n =>
        have read := actual p List.mem_cons_self n normalized
        simp only [useArg,normalized,read]
      | app a args => simp only [useArg,normalized]
      | record label field tail => simp only [useArg,normalized]
      | variant tag payload => simp only [useArg,normalized]
      | join a b => simp only [useArg,normalized]
    rw [inputs,inputs,front,ih (i+1)]
    intro p' member n name
    exact actual p' (List.mem_cons_of_mem _ member) n name

private theorem original_output_reads_only_placement399 (row : Declaration) (first last : Names)
    (sameOutputs : first.output = last.output) (otherwise : Nat → Nat) (e : Equation) :
    useOutput row first otherwise e = useOutput row last otherwise e := by
  unfold useOutput GeneralDeclarationDemands.outputTarget
  cases equation : normalize e.rhs <;> simp only [Names.old,sameOutputs]

/-- Original ordered where requests do not observe the padding either.
Every bare lexical child argument lies in the authored head input
scope; compound arguments and output targets use the same placement. -/
theorem origin_frame_where_independent_outside399 {s q row}
    {t : CandidateTape s q (visible s q)} (origin : SelectedHeadOrigin395 (row := row) t)
    (place : Placement) (a b : Nat → Capture) (scope : row.Scoped) :
    (preoutputFrameOfOrigin399 origin place a).clauses =
      (preoutputFrameOfOrigin399 origin place b).clauses := by
  let first := (preoutputFrameOfOrigin399 origin place a).names
  let last := (preoutputFrameOfOrigin399 origin place b).names
  have sameOutputs : first.output = last.output := rfl
  change row.requirements.map (fun cl => LiteralWhereEntry.mk cl (demand row cl first (place.compound cl) (place.targets cl))) =
    row.requirements.map (fun cl => LiteralWhereEntry.mk cl (demand row cl last (place.compound cl) (place.targets cl)))
  apply List.map_congr_left
  intro cl belongs
  have sameInputs : inputs first (place.compound cl) 0 cl.arguments =
      inputs last (place.compound cl) 0 cl.arguments := by
    apply inputs_read_lexical_only399
    intro p present n asVar
    have lexical := scope.1 cl belongs n
      (GeneralDeclarativeProducedNames325.enters_normal present asVar)
    change (GeneralDeclarativeFrameReadback325.sourceNames row place
      (preoutputInputOfHead399 origin.pick.head a)).input n =
      (GeneralDeclarativeFrameReadback325.sourceNames row place
       (preoutputInputOfHead399 origin.pick.head b)).input n
    simp only [GeneralDeclarativeFrameReadback325.sourceNames,GeneralDeclarativeProducedNames325.table,
      join_inputs_independent399 origin.pick.head a b n lexical]
  have sameTargets : cl.outputs.map (useOutput row first (place.targets cl)) =
    cl.outputs.map (useOutput row last (place.targets cl)) := by
    apply List.map_congr_left
    intro e _
    exact original_output_reads_only_placement399 row first last sameOutputs (place.targets cl) e
  simp only [demand,sameInputs,sameTargets]


/-- Start from the genuinely stored pre-output selected source head,
recover its original declaration and supplier, and use B6's specific
annotation without a prior literal receipt or per-model witness. A
full classifier must still produce this positive complete tape. -/
theorem positive_tape_B6_source_output399 {s q row}
    {t : CandidateTape s q (visible s q)} (only : TapedMatch s q t row)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (place : Placement) (outside : Nat → Capture) (atlas : B6SymbolicAtlas398 s)
    (i : Fin q.demand.outputs.length)
    (declared : ∃ v, ((authoredRegistry s.current).roles q.demand.role).assoc
      q.demand.outputs[i].name = some v)
    (b6 : ∀ (origin : SelectedHeadOrigin395 (row := row) t) (source : Body),
      Supplies (authoredRegistry s.current).roles row q.demand.outputs[i].name source →
      ∃ plan : B6ValuePlan398 s false (normalize (bodyPattern source)),
        atlas.read origin.rawOrdinal source = some plan ∧
        B6UsesFit398 s ((preoutputFrameOfOrigin399 origin place outside).slots source) plan.needs) :
    ∃ (origin : SelectedHeadOrigin395 (row := row) t)
      (out : LogicalRoleOutput398 (preoutputFrameOfOrigin399 origin place outside) i),
      (∃ unique : (row.associated.map Equation.name).Nodup,
        logicalOutputAt398 (preoutputFrameOfOrigin399 origin place outside) atlas i unique = some out) ∧
      StoredAt395 t origin.pick origin.visibleOrdinal ∧
      (authoredRegistry s.current).declarations[origin.rawOrdinal]? = some row ∧
      out.equation.occurrence = q.occurrence ∧
      out.equation.ordinal = i.val ∧ out.equation.requested = q.demand.outputs[i] ∧
      CompoundSourceRhs394 s ((preoutputFrameOfOrigin399 origin place outside).slots out.body) false
        (normalize (bodyPattern out.body)) out.equation.rhs := by
  obtain ⟨origin⟩ := selected_head_original_origin395 only
  let f := preoutputFrameOfOrigin399 origin place outside
  let registry := authoredRegistry s.current
  have rowChecked := checked.2 row (List.mem_of_getElem? origin.authored)
  have roleEq := (visible_exact s q row).mp origin.pick.inScope |>.2
  obtain ⟨source,supplied⟩ := GeneralDictionaryAssociatedProvenance.declared_covered
    registry.roles row rowChecked.signature q.demand.outputs[i].name (roleEq ▸ declared)
  obtain ⟨plan,typed,fit⟩ := b6 origin source supplied
  have unique := rowChecked.identified.2.2.1
  obtain ⟨out,ready,same,target,meaning⟩ :=
    supplied_symbolic_body_produces_exact_logical_output398 f atlas i unique supplied typed fit
  exact ⟨origin,out,⟨unique,ready⟩,origin.stored,origin.authored,rfl,rfl,rfl,by simpa only [same]⟩

end Yulang.GeneralDeclarativeI65
