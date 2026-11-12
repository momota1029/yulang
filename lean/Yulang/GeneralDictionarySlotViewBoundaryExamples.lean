import Yulang.GeneralDictionaryNominalSlotTransport
import Yulang.GeneralNominalExamples
import Yulang.CommonRoleStructuralRenaming

/-!
# Model-preserving slot transport does not preserve normalized readiness

Only the normalized observation is forgotten. Base storage, nominal descriptors
and identity metadata are unchanged, and the same concrete model satisfies both
states. Nevertheless a known scalar source becomes pending. Thus the transport
certificate cannot justify cross-context candidate or driver equivalence.
-/
namespace Yulang.GeneralDictionarySlotViewBoundaryExamples
open GeneralNominalExamples (state listDescriptor model state_models)
open GeneralDictionaryNominalSlotTransport (Transport)

private def forgottenView : GeneralNormalizedObservation.Snapshot (state true).base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro first; exact Fin.elim0 first
  canonical := by intro kind; exact Fin.elim0 kind
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

abbrev forgotten : GeneralNominalState.State :=
  { state true with
    view := forgottenView
    bodies_opaque := by intro _ _ _; rfl }

private theorem nominal_value (slot : Fin (state true).base.slots)
    (value : GeneralNominalState.Descriptor (state true).base.slots)
    (found : (state true).nominals slot = some value) : value = listDescriptor := by
  change (if slot = 0 then some listDescriptor else none) = some value at found
  split at found
  · cases found; rfl
  · cases found

/-- The existing certificate imposes no normalized-view equality. -/
def transport : Transport (state true) forgotten where
  embed := id
  source := by intro _; rfl
  rowSource := by intro _; rfl
  atoms := rfl
  heads := by
    intro slot term
    constructor
    · intro found
      exact ⟨slot, term, found, rfl, (CommonRoleStructuralRenaming.ty_rename_id term).symm⟩
    · rintro ⟨old, original, found, rfl, rfl⟩
      simpa only [CommonRoleStructuralRenaming.ty_rename_id] using found
  intervals := rfl
  nominals := by
    intro slot value
    constructor
    · intro found
      have same := nominal_value slot value found
      subst value
      exact ⟨slot, listDescriptor, found, rfl, rfl⟩
    · rintro ⟨old, original, found, rfl, rfl⟩
      have same := nominal_value _ original found
      subst original
      exact found
  constructors := rfl
  seed := rfl
  allocated := rfl
  reserved := rfl
  ordinary := rfl

theorem models_exact (assignment : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models forgotten assignment ↔ GeneralNominalState.Models (state true) assignment :=
  GeneralDictionaryNominalSlotTransport.models transport assignment

theorem known_before : GeneralNominalState.Known (state true) 1 :=
  ⟨1, rfl, Or.inl (by decide +kernel)⟩

theorem not_known_after : ¬ GeneralNominalState.Known forgotten 1 := by
  rintro ⟨slot, source, known⟩
  have same : slot = 1 := Fin.ext source
  subst slot
  rcases known with graph | ⟨value, found⟩
  · exact graph rfl
  · change none = some value at found
    cases found

abbrev demand : GeneralSourceState.Demand GeneralDeclarationExamples.roles :=
  ⟨0, fun _ => (1, 1), [], by intro _ impossible; cases impossible⟩

theorem not_pending_before : ¬ GeneralNominalState.RootPending (state true) demand := by
  rintro ⟨index, absent⟩
  exact absent known_before

theorem pending_after : GeneralNominalState.RootPending forgotten demand := ⟨⟨0, by decide⟩, not_known_after⟩

/-- Actual model existence rules out vacuous equivalence; readiness still changes. -/
theorem nonvacuous_view_boundary :
    GeneralNominalState.Models (state true) model ∧ GeneralNominalState.Models forgotten model ∧
    GeneralNominalState.Known (state true) 1 ∧ ¬ GeneralNominalState.Known forgotten 1 ∧
    ¬ GeneralNominalState.RootPending (state true) demand ∧ GeneralNominalState.RootPending forgotten demand :=
  ⟨state_models true, (models_exact model).mpr (state_models true), known_before,
    not_known_after, not_pending_before, pending_after⟩

end Yulang.GeneralDictionarySlotViewBoundaryExamples
