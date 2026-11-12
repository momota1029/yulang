import Yulang.GeneralDictionaryRecursiveObstructionEvidence
import Yulang.GeneralDictionaryRecursivePreparation

/-!
# Explicit output recording removes the original-state countermodel

This is a concrete equation-recording regression, not an implementation of Step
or a new candidate-selection policy. It records the two inequalities of the
source's already declared associated equation and keeps the original view.
-/
namespace Yulang.GeneralDictionaryRecursiveRecordingExamples
open GeneralDictionaryRecursiveObstruction
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom All)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier

abbrev outputAtoms : List (Atom Nat) :=
  [.tyLe (.var 1) (.base .int), .tyLe (.base .int) (.var 1)]

abbrev recorded := GeneralNominalState.extend context.state [] outputAtoms

theorem output_atoms_exact (model : Assignment) :
    All CommonNominalFullCarrier.model model outputAtoms ↔ Equivalent (model 1).1 (.base .int) := by
  simp [All, Atom.Holds, TyTerm.eval, CommonNominalFullCarrier.model, Equivalent]

/-- Exact full-model refinement, not merely one retained branch witness. -/
theorem recorded_models_exact (model : Assignment) :
    GeneralNominalState.Models recorded model ↔
      GeneralNominalState.Models context.state model ∧ Equivalent (model 1).1 (.base .int) := by
  rw [GeneralNominalState.extend_models, output_atoms_exact]

theorem good_recorded_model : GeneralNominalState.Models recorded GeneralNominalExamples.model :=
  (recorded_models_exact _).mpr ⟨GeneralNominalExamples.state_models false,
    ⟨subtype_refl _,subtype_refl _⟩⟩

theorem bad_not_recorded : ¬ GeneralNominalState.Models recorded badModel :=
  fun models => bad_output_equation ((recorded_models_exact _).mp models).2

/-- Recording is a strict, nonempty refinement in the concrete fixture. -/
theorem recorded_strict_nonempty :
    (∃ model, GeneralNominalState.Models recorded model) ∧
    (∀ model, GeneralNominalState.Models recorded model → GeneralNominalState.Models context.state model) ∧
    (∃ model, GeneralNominalState.Models context.state model ∧ ¬ GeneralNominalState.Models recorded model) :=
  ⟨⟨_,good_recorded_model⟩,fun model models => ((recorded_models_exact model).mp models).1,
    ⟨badModel,bad_original_model,bad_not_recorded⟩⟩

abbrev sourceTree : GeneralSourceDictionaries.Dictionary GeneralDeclarationExamples.roles :=
  .node root 40 []

theorem candidate_tree : GeneralSourceDictionaries.Evidence
    (GeneralNominalRecursiveCandidates.Survivor registry context) sourceTree :=
  .node survivor (by intro child member; cases member)

/-- The compound-head counterexample still reconstructs its exact source tree.
The previous variable-only materializer does not mediate this representation. -/
theorem reconstruct_exact :
    GeneralDictionaryRecursiveReadback.reconstruct registry registry_checked context (.node 40 []) root =
      some sourceTree :=
  GeneralDictionaryRecursiveReadback.reconstruct_candidate registry registry_checked context sourceTree candidate_tree

/-- The old variable-only head compiler explicitly defers this real nominal head. -/
theorem compound_head_deferred (capture : GeneralDeclarationDemands.Capture) :
    GeneralDictionaryVariableHeads.compileAt context.state.base declaration capture 0 = none := rfl

/-- In this concrete nominal fixture, recording precisely the declared output
is both sufficient and necessary for source Evidence of the selected leaf. -/
theorem recorded_models_iff_evidence (model : Assignment) :
    GeneralNominalState.Models recorded model ↔
      GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node 40 []) :=
  (recorded_models_exact model).trans (evidence_iff_output model).symm

/-- One fixed raw dictionary has source meaning in every recorded full model.
This validates the equation-recording repair, not a complete saturation driver. -/
theorem recorded_uniform_evidence :
    ∀ model, GeneralNominalState.Models recorded model →
      GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node 40 []) :=
  fun model models => (recorded_models_iff_evidence model).mp models

end Yulang.GeneralDictionaryRecursiveRecordingExamples
