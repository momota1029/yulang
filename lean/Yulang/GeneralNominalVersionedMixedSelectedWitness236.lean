import Yulang.GeneralNominalVersionedMixedSelectedFrame235
import Yulang.GeneralNominalVersionedMixedCurrentCandidate235
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedMixedSelectedWitness236
open GeneralNominalVersionedJournal232 GeneralNominalVersionedDiagnostic232
variable {roles : Roles.RoleDecls} {registry : GeneralDeclarations.Registry} {state : State roles}

theorem sharing
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children))
    (inhabited : ∃ model, Models state model) :
    Feasible (GeneralNominalCenteredHeadAllocEncoding.registry registry) state demand key := by
  classical
  obtain ⟨plan,frame,_⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
  have selectedLocal := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected
  have unique := GeneralNominalVersionedMixedCurrentEvidence235.selected_unique selectedLocal
  have safe := GeneralNominalVersionedMixedCurrentCandidate235.selected_safe selectedLocal
  apply Classical.byContradiction; intro none
  have conflict : SharingConflict (GeneralNominalCenteredHeadAllocEncoding.registry registry) state demand :=
    ⟨key,children,unique,safe,inhabited,⟨plan,frame⟩,none⟩
  exact B4TargetV8.conflict_not_selected conflict selectedLocal

theorem effects
    (selected : Local registry state demand (.selected key children))
    (head : ∃ model, Models state model ∧ ChosenHead registry state demand key model) :
    ∃ model, Models state model ∧ ChosenEffects registry state demand key model := by
  classical
  cases selected with
  | ordinary _ prior =>
    cases prior with
    | ordinary _ chosen =>
      cases chosen with
      | selected _ _ clear =>
        apply Classical.byContradiction; intro none
        exact clear ⟨head,none⟩
end Yulang.GeneralNominalVersionedMixedSelectedWitness236
