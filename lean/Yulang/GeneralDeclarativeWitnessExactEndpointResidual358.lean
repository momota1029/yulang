import Yulang.GeneralDeclarativeWitnessClosedRecordVerified358
import Yulang.GeneralDeclarativeExactDeleteRigid337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessExactEndpointResidual358
open GeneralDeclarativeWitnessTwoSourcedEndpoints358 (Read Window independently_sourced)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessClosedRecordLocal358 (closed)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent Subtype record exactEmpty subtype_trans)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl record_congr)
open GeneralDeclarativeExactDelete337 (subtract)
open GeneralDeclarativeExactDeleteRigid337 (literal surviving exact_if_both_empty)

structure ExactEnds (source : Source) (s : State) (w : Window) : Prop where
  read : Read source s w
  written : closed w.lowRest ∈ source.authored ∧ closed w.highRest ∈ source.authored
  retained : closed w.lowRest ∈ s.equations ∧ closed w.highRest ∈ s.equations

theorem actual_residual_without_center_shape {a s w} (observed : ExactEnds a s w)
    (m : Assignment) (fit : Models s m) :
    Equivalent (subtract [w.label] (m w.argument.center).1) exactEmpty := by
  have base := independently_sourced observed.read m fit
  have first : Equivalent (m w.lowRest).1 exactEmpty := fit.2 _ observed.retained.1
  have last : Equivalent (m w.highRest).1 exactEmpty := fit.2 _ observed.retained.2
  have left := record_congr w.label (eqv_refl (m w.lowField).1) first
  have right := record_congr w.label (eqv_refl (m w.highField).1) last
  apply exact_if_both_empty [w.label] [(w.label,(m w.lowField).1)] [(w.label,(m w.highField).1)]
  · simp [surviving]
  · simp [surviving]
  · exact ⟨subtype_trans left.2 base.2.2.1,subtype_trans base.2.2.2.1 right.1⟩

open GeneralDeclarativeWitnessRecordWindowFixture358 (window current authored currentModel model_fits)

def source : Source := ⟨authored.authored ++ [closed 0]⟩
def state : State := GeneralDeclarativeEntailment320.appendFacts current [closed 0]

theorem exact_endpoint_source : ExactEnds source state window := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · exact ⟨List.mem_append_left _ (by decide +kernel),List.mem_append_left _ (by decide +kernel)⟩
  · exact ⟨List.mem_append_left _ (by decide +kernel),List.mem_append_left _ (by decide +kernel)⟩
  · decide +kernel
  · exact ⟨List.mem_append_right _ List.mem_cons_self,List.mem_append_right _ List.mem_cons_self⟩
  · exact ⟨List.mem_append_right _ List.mem_cons_self,List.mem_append_right _ List.mem_cons_self⟩

theorem no_literal_center : ∀ row ∈ state.equations,row.left ≠ window.argument.center := by
  intro row member
  have old : row ∈ current.equations ∨ row ∈ [closed 0] := List.mem_append.mp member
  rcases old with earlier|new
  · exact GeneralDeclarativeWitnessRecordWindowFixture358.center_has_no_equation row earlier
  · cases List.mem_singleton.mp new
    decide

theorem actual_exact_residual_under_strict_field_window :
    Models state (currentModel exactEmpty) ∧
    Subtype ((currentModel exactEmpty) window.lowField).1 ((currentModel exactEmpty) window.highField).1 ∧
    ¬ Subtype ((currentModel exactEmpty) window.highField).1 ((currentModel exactEmpty) window.lowField).1 ∧
    Equivalent (subtract [window.label] ((currentModel exactEmpty) window.argument.center).1) exactEmpty := by
  have fit : Models state (currentModel exactEmpty) := by
    apply (GeneralDeclarativeEntailment320.model_append _).mpr
    refine ⟨model_fits _,?_⟩
    intro row new
    cases List.mem_singleton.mp new
    exact eqv_refl _
  exact ⟨fit,(independently_sourced exact_endpoint_source.read _ fit).2.2.2.2,
    GeneralDeclarativeWitnessRecordWindowFixture358.strict_original_payload_bounds,
    actual_residual_without_center_shape exact_endpoint_source _ fit⟩

end Yulang.GeneralDeclarativeWitnessExactEndpointResidual358
