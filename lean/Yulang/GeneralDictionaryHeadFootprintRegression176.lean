import Yulang.GeneralDictionaryViewFootprint176
import Yulang.GeneralNominalExamples
import Yulang.GeneralDictionaryNominalOnlyRefresh175

/-! An inhabited head-locality regression with a scalar query, outside the
nominal-only query fragment. An uninspected deferred head changes its explicit
residual representation. This is NOT a known-progress centered refresh witness. -/
namespace Yulang.GeneralDictionaryHeadFootprintRegression176
open GeneralDictionaryViewFootprint176
open GeneralDictionaryInspectionTransport
open GeneralNominalRecursiveInspection

abbrev state : GeneralNominalState.State :=
  {GeneralNominalExamples.state true with
    nominals := fun _ => none
    catalogue := by intro _ _ impossible; cases impossible
    bodies_opaque := by intro _ _ impossible; cases impossible}
abbrev context : GeneralNominalRecursiveCandidates.Context :=
  ⟨state,GeneralNominalExamples.interpretation⟩

abbrev next : HeadObservation state where
  heads := fun slot => if slot = 0 then .deferred (.unsupported (.var 0)) else state.view.heads slot
  checked := by
    intro slot term recorded
    split at recorded
    · rename_i zero
      subst slot
      cases Option.some.inj recorded
      exact .refl _
    · exact state.view.checked slot term recorded
  nominals := fun _ => none
  catalogue := by intro _ _ impossible; cases impossible
  bodiesOpaque := by intro _ _ impossible; cases impossible

abbrev query : GeneralNominalInspection.Query := .scalar .int
abbrev bounds : GeneralNominalInspection.Bounds state := (1,1)

theorem agrees : Agrees context next query bounds := by
  simp [Agrees,query,bounds,next,state,GeneralNominalExamples.view]

theorem finished : Finished (inspect state query bounds none) := by
  simp [Finished,inspect,Report.visit,query,bounds,state,GeneralNominalExamples.view]

theorem view_changes : next.view ≠ state.view := by
  intro equal
  have heads := congrArg (fun view : GeneralNormalizedObservation.Snapshot state.base =>
    (view.heads 0).term) equal
  change some (.var 0 : Core.PresenceGeneration.TyTerm (Fin 2)) = none at heads
  cases heads

theorem model_nonempty : ∃ model, GeneralNominalState.Models state model ∧
    GeneralNominalState.Models (reobserve context next).state model := by
  refine ⟨GeneralNominalExamples.model,?_,?_⟩
  all_goals exact ⟨(GeneralNominalExamples.state_models true).1,
    (by intro _ _ impossible; cases impossible),(GeneralNominalExamples.state_models true).2.2⟩

def refinement : GeneralNominalRefinements.Refines state (reobserve context next).state := by
  refine { GeneralNominalRefinements.refl state with
    nominals := ?_, known := ?_ }
  · intro _ _ impossible; cases impossible
  · intro source known
    obtain ⟨slot,eq,visible | ⟨descriptor,impossible⟩⟩ := known
    · refine ⟨slot,eq,Or.inl ?_⟩
      by_cases zero : slot = 0
      · subst slot
        exact False.elim (visible rfl)
      · simpa [reobserve,HeadObservation.observation,HeadObservation.view,next,zero,
          GeneralNormalizedObservation.Snapshot.graph] using visible
    · cases impossible

theorem report_preserved : inspect (reobserve context next).state query bounds none =
    transferReport context next (inspect state query bounds none) :=
  inspect_finished context next refinement query bounds none agrees finished

theorem scalar_not_nominal_only :
    ¬ GeneralDictionaryNominalOnlyRefresh175.NominalOnly query := by
  intro fragment
  cases fragment

end Yulang.GeneralDictionaryHeadFootprintRegression176
