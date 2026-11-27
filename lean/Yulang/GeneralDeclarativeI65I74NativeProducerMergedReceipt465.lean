import Yulang.GeneralDeclarativeI65I74NativeProducerSameHop465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open PreparedDeclarations463
open PhysicalVisit463.IssuedProjection464
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessNativeOrder362 (node)
open GeneralDeclarativeWitnessNativeInstall360 (interpreted)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)

/-- Only the I-89 single actual visible candidate, with an existing
per-declaration checked table. This does not run candidate matching. -/
def readSingleCandidatePhaseField {p : Problem} {phase : CheckedPhase p.state.core}
    (tab : CheckedTable p.state.core.current) (w : PhaseField p phase) : Option HeadFieldReceipt :=
  if (visible p.state.core p.root).length = 1 then readFieldWithPhaseOwner tab w else none

def ExactSingleCandidatePhaseField {p : Problem} (phase : CheckedPhase p.state.core)
    (tab : CheckedTable p.state.core.current) (fact : PhaseAtHop) (r : HeadFieldReceipt) : Prop :=
  (visible p.state.core p.root).length = 1 ∧ ExactHeadField (p := p) tab r ∧
    LiteralPhaseOwnerAtHop phase r fact

theorem exact_single_candidate_phase_field_has_finite_wire
    {p : Problem} (phase : CheckedPhase p.state.core) (tab : CheckedTable p.state.core.current)
    (atHop : PhaseAtHop) (r : HeadFieldReceipt) :
    ExactSingleCandidatePhaseField phase tab atHop r ↔
      ∃ w : PhaseField p phase, w.actual = atHop ∧ readSingleCandidatePhaseField tab w = some r := by
  constructor
  · rintro ⟨unique,field,attached⟩
    obtain ⟨w,found⟩ := (prechecked_head_field_iff_finite_exact_wire ..).mp field
    let packet : PhaseField p phase := ⟨w,atHop⟩
    have pass : readFieldWithPhaseOwner tab packet = some r :=
      phase_owner_reader_keeps_the_exact_existing_field_report.mpr ⟨found,attached⟩
    exact ⟨packet,rfl,by simp [readSingleCandidatePhaseField,unique,pass]⟩
  · rintro ⟨w,rfl,found⟩
    by_cases one : (visible p.state.core p.root).length = 1
    · have exact : readFieldWithPhaseOwner tab w = some r :=
        by simpa [readSingleCandidatePhaseField,one] using found
      obtain ⟨field,phase⟩ := phase_owner_reader_keeps_the_exact_existing_field_report.mp exact
      exact ⟨one,(prechecked_head_field_iff_finite_exact_wire ..).mpr ⟨_,field⟩,phase⟩
    · simp [readSingleCandidatePhaseField,one] at found

theorem phase_owner_and_report_share_actual_original_row_in_every_fitting_model
    {input : Input} {phase : CheckedPhase input.problem.old.state.core}
    {w : PhaseField input.problem.old phase} {r : HeadFieldReceipt}
    (read : readSingleCandidatePhaseField input.checked w = some r)
    (m : I72.Model) (fit : FitsFull input.problem.state m) :
    r.literal ≠ [] ∧
    AliasCycle input.problem.old.state.core.current.ordinary
      (observed input.problem.old.state.core.current.ordinary) r.terminal ∧
    ∃ logical ordinal row,
      r.rows[w.actual.hop]? = some ordinal ∧
      input.problem.old.state.core.current.ordinary.equations[ordinal]? = some row ∧
      row.left = w.actual.write.address.target ∧
      input.problem.old.state.core.origins[w.actual.sourceOrdinal]? = some (originalOfWrite w.actual.write) ∧
      OriginRoute input.problem.old.state.core (originalOfWrite w.actual.write) logical ∧
      GeneralDeclarativeLowerKnown321.Alias input.problem.old.state.core.current.ordinary logical row.left ∧
      m.nativeSyntax row.left = some (node w.actual.write.code) ∧
      interpreted phase.world.board m.assignment row.left = some (w.actual.write.code.eval m.assignment) := by
  have bound := (exact_single_candidate_phase_field_has_finite_wire ..).mpr ⟨w,rfl,read⟩
  obtain ⟨_,_,_,nonempty,_,cycle⟩ :=
    exact_prechecked_head_field_keeps_original_and_evidence_in_each_fit input bound.2.1 m fit
  obtain ⟨cap,logical,ordinal,row,args,source,index,physical,target,unique,exact⟩ := bound.2.2
  obtain ⟨visit,found⟩ := (prechecked_head_field_iff_finite_exact_wire ..).mp bound.2.1
  obtain ⟨usedRow,atUsed,linked,usedOrig,member,route,slot⟩ :=
    every_successful_field_receipt_uses_the_very_same_previous_logical_site found args index source
  have rowEq : row = usedRow := Option.some.inj (physical.symm.trans atUsed)
  subst usedRow
  have sameOrig := any_origin_at_a_single_physical_slot_is_the_same_occurrence exact
    (target ▸ unique) member (slot.trans target)
  have native := actual_phase_origin_ordinal_and_native_view_hold_in_every_same_fit
    ((finite_phase_origin_check_iff_literal_placed_active_row ..).mpr exact) m fit.1
  exact ⟨nonempty,cycle,logical,ordinal,row,index,physical,target,exact.1,sameOrig ▸ route,
    linked,target.symm ▸ native.1,target.symm ▸ native.2⟩

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465
