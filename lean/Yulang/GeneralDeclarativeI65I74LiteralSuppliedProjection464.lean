import Yulang.GeneralDeclarativeI65I74ExactSourceProposal464
import Yulang.GeneralDeclarativeI65I74ProjectionBatchField464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeEqualities322 (Derives)
open PreparedDeclarations463
open List410 (ExactEscapeWire)
private abbrev RawState := GeneralDeclarativeHead320.State

/-- The occurrence and cut are finite data. The equality proof for the
proposed expression is reconstructed from the two existing source rows. -/
structure LiteralProjectionWire where
  source : SourceRowSelection
  cut : ExactEscapeWire

def literalData (s : RawState) : List LiteralProjectionWire → Option (List DerivedAppendData)
  | [] => some []
  | w :: ws => do
    let row ← readSourceProposal s w.source
    let rest ← literalData s ws
    pure (⟨⟨row,w.cut⟩,literalSourceProofData w.source⟩ :: rest)

def OriginalLiteralPlans (s : RawState) : List SourceRowSelection → List Equation → Prop
  | [],[] => True
  | w::ws,e::es => ExactSourceProposal s w e ∧ OriginalLiteralPlans s ws es
  | _,_ => False

private theorem all_actual_original_sources_are_exact {s : RawState}
    {w : List LiteralProjectionWire} {d : List DerivedAppendData}
    (h : literalData s w = some d) :
    OriginalLiteralPlans s (w.map LiteralProjectionWire.source) (d.map fun x => x.checked.row) := by
  induction w generalizing d with
  | nil =>
    obtain rfl := Option.some.inj h
    exact True.intro
  | cons p ps ih =>
    cases source : readSourceProposal s p.source with
    | none => simp [literalData,source,Option.bind] at h
    | some e =>
      cases rest : literalData s ps with
      | none => simp [literalData,source,rest,Option.bind] at h
      | some proof =>
        have actual : ⟨⟨e,p.cut⟩,literalSourceProofData p.source⟩ :: proof = d := by
          simpa [literalData,source,rest,Option.bind] using h
        subst d
        exact ⟨(checked_proposal_is_exact_original_syntax_and_ordinals ..).mp source,ih rest⟩

private theorem old_source_plan_survives_exact_ordinal_prefix
    {s t : RawState} {p : SourceRowSelection} {e : Equation}
    (fixed : ∀ (i : Nat) (row : Equation), s.equations[i]? = some row → t.equations[i]? = some row)
    (proof : ExactSourceProposal s p e) : ExactSourceProposal t p e := by
  obtain ⟨a,b,atA,atB,lit,result⟩ := proof
  exact ⟨a,b,fixed _ _ atA,fixed _ _ atB,lit,result⟩

private theorem old_source_plans_survive_exact_ordinal_prefix
    {s t : RawState} {ps : List SourceRowSelection} {rows : List Equation}
    (fixed : ∀ (i : Nat) (row : Equation), s.equations[i]? = some row → t.equations[i]? = some row)
    (proof : OriginalLiteralPlans s ps rows) : OriginalLiteralPlans t ps rows := by
  induction ps generalizing rows with
  | nil => cases rows <;> exact proof
  | cons p tail ih =>
    cases rows with
    | nil => exact proof
    | cons row rest =>
      exact ⟨old_source_plan_survives_exact_ordinal_prefix fixed proof.1,ih proof.2⟩

/-- Read proposed row plans from the first snapshot. Cut validation and
ordinary equality replay use the proper independently checked prefix. -/
def checkLiteralSuppliedPhase (pre post : RawState) (w : List LiteralProjectionWire) : Bool :=
  ((literalData pre w).bind (readDerivedAppends pre)).any (exactOrdinaryState post)

theorem accepted_literal_phase_has_exact_ordinary_batch_and_original_plans
    {pre post : RawState} {w : List LiteralProjectionWire}
    (h : checkLiteralSuppliedPhase pre post w = true) :
    ActualSuppliedBatch pre post ∧
    OriginalLiteralPlans pre (w.map LiteralProjectionWire.source) (suppliedRows pre post) := by
  cases source : literalData pre w with
  | none => simp [checkLiteralSuppliedPhase,source,Option.bind] at h
  | some plan =>
    cases afterRead : readDerivedAppends pre plan with
    | none => simp [checkLiteralSuppliedPhase,source,afterRead,Option.bind] at h
    | some after =>
      have eq := (exact_ordinary_snapshot_iff post after).mp
        (by simpa [checkLiteralSuppliedPhase,source,afterRead,Option.bind] using h)
      subst after
      obtain ⟨valid,derive⟩ := read_derived_batch_validates_exact_supplied_source_proofs_and_cut afterRead
      have rows := (literal_row_order_and_ordinary_constraints_are_exact valid).2
      have suffix : suppliedRows pre post = plan.map (fun x => x.checked.row) := by
        simp [suppliedRows,rows]
      exact ⟨by unfold ActualSuppliedBatch; rw [suffix]; exact ⟨valid,derive⟩,
        suffix.symm ▸ all_actual_original_sources_are_exact source⟩

private theorem literal_plans_make_each_code_given_those_cuts
    {s : RawState} {ws : List LiteralProjectionWire} {rows : List Equation}
    (available : OriginalLiteralPlans s (ws.map LiteralProjectionWire.source) rows) :
    ∃ d, literalData s ws = some d := by
  induction ws generalizing rows with
  | nil => exact ⟨[],rfl⟩
  | cons w rest ih =>
    cases rows with
    | nil => cases available
    | cons e es =>
      obtain ⟨out,tail⟩ := ih available.2
      have first := (checked_proposal_is_exact_original_syntax_and_ordinals ..).mpr available.1
      exact ⟨⟨⟨e,w.cut⟩,literalSourceProofData w.source⟩::out,
        by simp [literalData,first,tail,Option.bind]⟩

private theorem existing_literal_codes_stay_the_same_on_exact_ordinal_prefix
    {s t : RawState} {ws : List LiteralProjectionWire} {ds : List DerivedAppendData}
    (fixed : ∀ (i : Nat) (row : Equation), s.equations[i]? = some row → t.equations[i]? = some row)
    (h : literalData s ws = some ds) : literalData t ws = some ds := by
  induction ws generalizing ds with
  | nil => exact h
  | cons w rest ih =>
    cases first : readSourceProposal s w.source with
    | none => simp [literalData,first,Option.bind] at h
    | some e =>
      cases tail : literalData s rest with
      | none => simp [literalData,first,tail,Option.bind] at h
      | some out =>
        have foreign := (checked_proposal_is_exact_original_syntax_and_ordinals ..).mpr
          (old_source_plan_survives_exact_ordinal_prefix fixed
            ((checked_proposal_is_exact_original_syntax_and_ordinals ..).mp first))
        have moved := ih tail
        simpa [literalData,foreign,moved,Option.bind,first,tail] using h

private theorem independent_ordered_literal_plans_supply_specific_equality_codes
    {pre post : RawState} {rows : List Equation} (safe : OrderedSafeAppends pre rows post)
    (plans : List SourceRowSelection) (source : OriginalLiteralPlans pre plans rows) :
    ∃ w d, w.map LiteralProjectionWire.source = plans ∧
      d.map (fun x => x.checked.row) = rows ∧ literalData pre w = some d ∧
      readDerivedAppends pre d = some post := by
  induction safe generalizing plans with
  | done =>
    cases plans with
    | nil => exact ⟨[],[],rfl,rfl,rfl,rfl⟩
    | cons _ _ => cases source
  | @thenRow form s e es target shape zero noReturn safe ih =>
    cases plans with
    | nil => cases source
    | cons p ps =>
      obtain ⟨chosen,rest⟩ := source
      have fixed : ∀ (i : Nat) (row : Equation), s.equations[i]? = some row → (extendedRows s e).equations[i]? = some row := by
        intro i r h
        have index := (List.getElem?_eq_some_iff.mp h).choose
        simpa [extendedRows,List.getElem?_append_left index] using h
      have relocated := old_source_plans_survive_exact_ordinal_prefix fixed rest
      obtain ⟨ws,ds,keys,rows,dst,checked⟩ := ih ps relocated
      obtain ⟨cut,pass⟩ := (original_projection_cut_has_finite_wire_exactly_when_safe shape).mpr
        ⟨zero,noReturn⟩
      have eq := (checked_proposal_is_exact_original_syntax_and_ordinals ..).mpr chosen
      have first := source_proposal_emits_its_exact_finite_ordinary_proof eq
      have bindOriginal : literalData s ws = some ds := by
        have given : OriginalLiteralPlans s (ws.map LiteralProjectionWire.source) es := by simpa [keys] using rest
        obtain ⟨old,got⟩ := literal_plans_make_each_code_given_those_cuts given
        have sameRead := existing_literal_codes_stay_the_same_on_exact_ordinal_prefix fixed got
        have equal := Option.some.inj (sameRead.symm.trans dst)
        exact equal ▸ got
      refine ⟨⟨p,cut⟩::ws,⟨⟨e,cut⟩,literalSourceProofData p⟩::ds,by simp [keys],by simp [rows],?_,?_⟩
      · simp [literalData,eq,bindOriginal,Option.bind]
      · simp [readDerivedAppends,first,pass,checked]

theorem exact_original_row_plans_have_finite_supplied_phase_certificate
    (pre post : RawState) (plans : List SourceRowSelection) :
    (∃ w, w.map LiteralProjectionWire.source = plans ∧ checkLiteralSuppliedPhase pre post w = true) ↔
    OrderedSafeAppends pre (suppliedRows pre post) post ∧ OriginalLiteralPlans pre plans (suppliedRows pre post) := by
  constructor
  · rintro ⟨w,rfl,pass⟩
    have result := accepted_literal_phase_has_exact_ordinary_batch_and_original_plans pass
    exact ⟨result.1.1,result.2⟩
  · rintro ⟨structural,authored⟩
    obtain ⟨w,d,chosen,_,pair,ran⟩ :=
      independent_ordered_literal_plans_supply_specific_equality_codes structural plans authored
    exact ⟨w,chosen,by simp [checkLiteralSuppliedPhase,pair,ran,Option.bind,
        (exact_ordinary_snapshot_iff ..).mpr rfl]⟩

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
