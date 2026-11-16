import Yulang.GeneralDictionaryAdministrativeSemanticSupport222

namespace Yulang.GeneralDictionarySemanticDelta223
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefault214ActualBodyFrame (classSources class_iff)
open GeneralDictionaryDefault214ActualJournal (effectSources effect_iff)
open GeneralDictionaryDefaultPacketSupport213 (packetSources packet_iff)
variable {roles : Roles.RoleDecls} {state : State roles} {pool : List Nat}

/-- An independently justified semantic dependency pool, not a freshness claim. -/
def Depends (state : State roles) (pool : List Nat) : Prop :=
  ∀ a b : Assignment, (∀ n ∈ pool, a n = b n) → (Models state a ↔ Models state b)

noncomputable def liveSources (effects : List (Effect roles))
    (core : GeneralNominalCenteredSteps.State roles) : List Nat :=
  effects.flatMap fun effect => classSources core effect.plan.packet.site.occurrence effect.plan

theorem live_iff (effects : List (Effect roles))
    (core : GeneralNominalCenteredSteps.State roles)
    (same : ∀ n ∈ liveSources effects core, a n = b n) :
    (∀ effect ∈ effects, effect.Live core a) ↔ (∀ effect ∈ effects, effect.Live core b) := by
  apply forall_congr'; intro effect
  apply forall_congr'; intro member
  apply class_iff
  intro n present
  exact same n (List.mem_flatMap.mpr ⟨effect,member,present⟩)

noncomputable def installDelta (state : State roles) (effect : Effect roles) : List Nat :=
  packetSources effect.plan ++ effectSources (install state effect) effect ++
    liveSources state.effects (installCore state.core effect.plan)

/-- Exact installation still includes new and old live effects and total packets.
The delta is finite but is not asserted disjoint from current capture slots. -/
theorem install_depends (depends : Depends state pool)
    (snapshot : effect.snapshot = state.core) :
    Depends (install state effect) (pool ++ installDelta state effect) := by
  intro a b same
  rw [install_models snapshot,install_models snapshot]
  unfold InstallationModels
  apply and_congr (depends a b (fun n member => same n (List.mem_append_left _ member)))
  apply and_congr (packet_iff effect.plan (fun n member => same n (by simp [installDelta,member])))
  have current := effect_iff (install state effect) effect (fun n member => same n (by simp [installDelta,member]))
  have prior := live_iff state.effects (installCore state.core effect.plan)
    (fun n member => same n (by simp [installDelta,member]))
  simpa only [install,and_assoc] using and_congr current prior

noncomputable def mergeDelta (state : State roles) (first last : Site roles) : List Nat :=
  (GeneralNominalDemandMerging.outputAtoms first.observed last.observed).flatMap GeneralNominalState.atomSources ++
    liveSources state.effects (merge state first last).core

theorem merge_depends (depends : Depends state pool) :
    Depends (merge state first last) (pool ++ mergeDelta state first last) := by
  intro a b same
  rw [merge_models,merge_models]
  apply and_congr (depends a b (fun n member => same n (List.mem_append_left _ member)))
  apply and_congr
  · unfold PresenceNormalForm.All
    apply forall_congr'; intro atom
    apply forall_congr'; intro member
    apply GeneralNominalCenteredModelExtension.atom_same
    intro n present
    exact same n (List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨atom,member,present⟩)))
  · exact live_iff _ _ (fun n member => same n (List.mem_append_right _ (List.mem_append_right _ member)))

/-- Every step from a reachable state has an explicit finite support extension.
Administrative/refresh steps use the empty delta; install and merge use the
lists above. This does not prove disjointness or semantic Overlap. -/
theorem step_depends
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (step : Step registry root state after) (depends : Depends state pool) :
    ∃ delta : List Nat, Depends after (pool ++ delta) := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative action =>
      refine ⟨[],?_⟩
      simpa only [List.append_nil,Depends] using
        GeneralDictionaryAdministrativeSemanticSupport222.reachable_administrative_depends
          path generated action depends
  | refresh focus context certificate source member unknown known =>
      refine ⟨[],?_⟩
      simp only [List.append_nil]
      intro a b same
      exact GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate |>.trans
        ((depends a b same).trans (GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate).symm)
  | install effect enabled novel => exact ⟨installDelta state effect,install_depends depends enabled.snapshot_eq⟩
  | merge first last one two same novel => exact ⟨mergeDelta state first last,merge_depends depends⟩

end Yulang.GeneralDictionarySemanticDelta223
