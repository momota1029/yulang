import Yulang.GeneralDictionaryNominalOnlyRefresh175
import Yulang.GeneralNominalExamples

/-! A concrete view-changing nominal-only inspection. Source 1 changes from
unresolved observation to scalar int; a nominal list query still captures its
argument at (1,1), rather than inspecting the argument's scalar head. -/
namespace Yulang.GeneralDictionaryNominalViewRegression175
open GeneralDictionaryInspectionTransport
open GeneralNominalRecursiveInspection
open GeneralDictionaryNominalOnlyRefresh175
private def forgottenView : GeneralNormalizedObservation.Snapshot (GeneralNominalExamples.state true).base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro first; exact Fin.elim0 first
  canonical := by intro kind; exact Fin.elim0 kind
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

abbrev forgotten : GeneralNominalState.State :=
  { GeneralNominalExamples.state true with
    view := forgottenView
    bodies_opaque := by intro _ _ _; rfl }

abbrev before : GeneralNominalRecursiveCandidates.Context :=
  ⟨forgotten, GeneralNominalExamples.interpretation⟩

def next : Observation before.state where
  view := (GeneralNominalExamples.state true).view
  nominals := (GeneralNominalExamples.state true).nominals
  catalogue := (GeneralNominalExamples.state true).catalogue
  bodiesOpaque := (GeneralNominalExamples.state true).bodies_opaque

abbrev after := reobserve before next

theorem view_changes : next.view ≠ before.state.view := by
  intro equal
  have heads := congrArg (fun view => (view.heads (1 : Fin 2)).term) equal
  change some (Core.PresenceGeneration.TyTerm.base .int : Core.PresenceGeneration.TyTerm (Fin 2)) = none at heads
  cases heads

def refinement : GeneralNominalRefinements.Refines before.state after.state where
  base := (GeneralNominalRefinements.refl (GeneralNominalExamples.state true)).base
  heads := (GeneralNominalRefinements.refl (GeneralNominalExamples.state true)).heads
  nominals := (GeneralNominalRefinements.refl (GeneralNominalExamples.state true)).nominals
  ordinary := fun _ member => member
  known := by
    rintro source ⟨slot, identity, graph | nominal⟩
    · exact False.elim (graph rfl)
    · exact ⟨slot, identity, Or.inr nominal⟩
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl

abbrev query : GeneralNominalInspection.Query := .nominal 0 [.variables [0]]

theorem query_allowed : NominalOnly query := by
  apply NominalOnly.nominal
  intro child member
  have same : child = .variables [0] := List.mem_singleton.mp member
  subst child
  exact .variables [0]

theorem finished_before : Finished (inspect before.state query (0,0) none) := by
  unfold Finished
  decide +kernel

theorem report_preserved : inspect after.state query (0,0) none =
    transferReport before next (inspect before.state query (0,0) none) :=
  inspect_finished before next refinement query (0,0) none query_allowed finished_before

theorem finished_after : Finished (inspect after.state query (0,0) none) := by
  rw [report_preserved, transferred_finished]
  exact finished_before

theorem capture_before : bindings before.state (inspect before.state query (0,0) none) = [(0,(1,1))] := by
  decide +kernel

theorem capture_after : bindings after.state (inspect after.state query (0,0) none) = [(0,(1,1))] := by
  rw [report_preserved,transferred_bindings]
  exact capture_before

theorem known_progress : ¬ GeneralNominalState.Known before.state 1 ∧
    GeneralNominalState.Known after.state 1 :=
  by
    constructor
    · rintro ⟨slot, identity, graph | ⟨descriptor, found⟩⟩
      · exact graph rfl
      · have same : slot = 1 := Fin.ext identity
        subst slot
        change none = some descriptor at found
        cases found
    · exact ⟨1, rfl, Or.inl (by decide +kernel)⟩

theorem models_nonempty : GeneralNominalState.Models before.state GeneralNominalExamples.model ∧
    GeneralNominalState.Models after.state GeneralNominalExamples.model :=
  ⟨GeneralNominalExamples.state_models true, GeneralNominalExamples.state_models true⟩

end Yulang.GeneralDictionaryNominalViewRegression175
