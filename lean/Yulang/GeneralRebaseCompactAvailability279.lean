import Yulang.GeneralRebaseCompactObservationGuard279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseCompactAvailability279
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseCompactEdgeInstall279
open GeneralRebaseCompactObservationGuard279 (refreshForward revisionForward certificate improves)
open GeneralRebaseCompactInstallGuard279 (reframe enabled_iff)
open GeneralRebaseCompactTrust279 (replace_twice replace_self)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralNominalVersionedMixedKernel234 (Administrative At Step Stable)

variable {roles : Roles.RoleDecls} {state after : State roles} {new : List (Edge roles)}
variable {registry : Registry} {root focus : Occurrence roles}

def SameEdges (state : State roles) (new : List (Edge roles)) : Prop :=
  ∀ edge, edge ∈ new ↔ edge ∈ state.core.erased.current.edges

theorem admin_forward (h : Administrative state focus after) :
    ∃ target, Administrative (replaceEdges state new) focus target := by
  cases h with
  | enqueue linked absent => exact ⟨_,.enqueue _ linked absent⟩
  | refresh context cert source member none some =>
    exact ⟨_,.refresh _ context (refreshForward cert) source member none some⟩
  | equate first last a b eq novel =>
    exact ⟨_,.equate _ first last a b (fun m h => eq m ((models_exact state new m).mp h)) novel⟩
  | reobserve rev cert inc =>
    exact ⟨_,.reobserve _ (revisionForward rev) (certificate cert) (improves inc)⟩

theorem at_forward (same : SameEdges state new) (h : At registry state focus after) :
    ∃ target, At registry (replaceEdges state new) focus target := by
  cases h with
  | administrative action =>
    obtain ⟨target,admin⟩ := admin_forward (new := new) action
    exact ⟨target,.administrative admin⟩
  | refresh _ context cert source member none some =>
    exact ⟨_,.refresh _ context (refreshForward cert) source member none some⟩
  | install effect enabled absent =>
    exact ⟨_,.install (reframe effect enabled.snapshot_eq new) ((enabled_iff enabled.snapshot_eq).mpr enabled)
      ((not_congr (committed_exact state new same effect.plan)).mpr absent)⟩
  | merge first last a b eq novel =>
    exact ⟨_,.merge first last a b (by rwa [GeneralRebaseCompactDiagnostics279.same_models])
      ((not_congr (aliases_exact state new _ _)).mpr novel)⟩

theorem opposite (same : SameEdges state new) :
    SameEdges (replaceEdges state new) state.core.erased.current.edges :=
  fun edge => (same edge).symm

theorem at_exists_iff (same : SameEdges state new) :
    (∃ target, At registry (replaceEdges state new) focus target) ↔
      ∃ target, At registry state focus target := by
  constructor
  · rintro ⟨after,h⟩
    have backward := at_forward (opposite same) h
    rwa [replace_twice,replace_self] at backward
  · rintro ⟨after,h⟩
    exact at_forward same h

theorem step_exists_iff (same : SameEdges state new) :
    (∃ target, Step registry root (replaceEdges state new) target) ↔
      ∃ target, Step registry root state target := by
  constructor
  · rintro ⟨target,focus,generated,action⟩
    obtain ⟨other,h⟩ := (at_exists_iff same).mp ⟨target,action⟩
    exact ⟨other,focus,(generated_exact state new same root focus).mp generated,h⟩
  · rintro ⟨target,focus,generated,action⟩
    obtain ⟨other,h⟩ := (at_exists_iff same).mpr ⟨target,action⟩
    exact ⟨other,focus,(generated_exact state new same root focus).mpr generated,h⟩

theorem stable_iff_not_step (state : State roles) :
    Stable registry state root ↔ ¬ ∃ target, Step registry root state target := by
  constructor
  · rintro done ⟨target,focus,generated,action⟩
    exact done focus generated target action
  · intro none focus generated target action
    exact none ⟨target,focus,generated,action⟩

theorem stable_iff (same : SameEdges state new) :
    Stable registry (replaceEdges state new) root ↔ Stable registry state root :=
  (stable_iff_not_step _).trans ((not_congr (step_exists_iff same)).trans (stable_iff_not_step _).symm)

theorem reduced_stable (start : State roles) (effect : GeneralNominalVersionedJournal232.Effect roles) :
    Stable registry (reduced start effect) root ↔
      Stable registry (GeneralNominalVersionedInstall232.install start effect) root :=
  stable_iff (reduced_membership start effect)

end Yulang.GeneralRebaseCompactAvailability279
