import Yulang.GeneralDictionaryNameDelta227
import Yulang.GeneralDictionaryReachableRest227

/-! Existing effects read only their new requests and cross-name targets.
The current journal, rather than an added support assumption, supplies all old
class equations. The newly installed effect still retains its full live class. -/
namespace Yulang.GeneralDictionaryHistoricalLive227
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionarySemanticDelta223 (Depends liveSources)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
open GeneralDictionaryNameDelta227 (deltaSources)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

noncomputable def historySources (state : State roles)
    (after : GeneralNominalCenteredSteps.State roles) : List Nat :=
  state.effects.flatMap fun prior =>
    deltaSources state.core after prior.plan.packet.site.occurrence prior.plan

theorem history_iff (state : State roles) (after : GeneralNominalCenteredSteps.State roles)
    (subset : ∀ prior ∈ state.effects,
      GeneralNominalCenteredHeadOutputs.requests state.core prior.plan.packet.site.occurrence ⊆
      GeneralNominalCenteredHeadOutputs.requests after prior.plan.packet.site.occurrence)
    (one : Models state a) (two : Models state b)
    (same : ∀ n ∈ historySources state after, a n = b n) :
    (∀ prior ∈ state.effects, prior.Live after a) ↔
      (∀ prior ∈ state.effects, prior.Live after b) := by
  apply forall_congr'; intro prior
  apply forall_congr'; intro member
  exact GeneralDictionaryNameDelta227.class_iff (subset prior member)
    (one.2.2.2.2.2 prior member).2 (two.2.2.2.2.2 prior member).2
    (fun n present => same n (List.mem_flatMap.mpr ⟨prior,member,present⟩))

noncomputable def installDelta (state : State roles) (effect : Effect roles) : List Nat :=
  GeneralDictionaryReachableRest227.packetSources effect.plan ++
    classSources (installCore state.core effect.plan) effect.plan.packet.site.occurrence effect.plan ++
    historySources state (installCore state.core effect.plan)

theorem install_depends
    (enabled : Installable registry state effect) (depends : Depends state pool) :
    Depends (install state effect) (pool ++ installDelta state effect) := by
  intro a b same
  rw [GeneralDictionaryLiveDelta227.installation_iff enabled.snapshot_eq,
    GeneralDictionaryLiveDelta227.installation_iff enabled.snapshot_eq]
  simp only [List.mem_cons,forall_eq_or_imp]
  have old := depends a b (fun n member => same n (List.mem_append_left _ member))
  have packet (one : Models state a) (two : Models state b) :=
    GeneralDictionaryReachableRest227.packet_iff effect.plan
      (GeneralDictionaryDefaultDepth208.frame enabled) one two
      (fun n member => same n (by simp [installDelta,member]))
  have current := GeneralDictionaryDefault214ActualBodyFrame.class_iff
    (installCore state.core effect.plan) effect.plan.packet.site.occurrence effect.plan
    (fun n member => same n (by simp [installDelta,member]))
  have prior (one : Models state a) (two : Models state b) :=
    history_iff state (installCore state.core effect.plan)
      (fun _ _ => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (fun _ h => List.mem_append_left _ h) (fun _ h => h)) one two
      (fun n member => same n (by simp [installDelta,member]))
  constructor
  · rintro ⟨valid,held,live,history⟩
    exact ⟨old.mp valid,(packet valid (old.mp valid)).mp held,
      current.mp live,(prior valid (old.mp valid)).mp history⟩
  · rintro ⟨valid,held,live,history⟩
    exact ⟨old.mpr valid,(packet (old.mpr valid) valid).mpr held,
      current.mpr live,(prior (old.mpr valid) valid).mpr history⟩

noncomputable def mergeDelta (state : State roles) (first last : Site roles) : List Nat :=
  (GeneralNominalDemandMerging.outputAtoms first.observed last.observed).flatMap GeneralNominalState.atomSources ++
    historySources state (merge state first last).core

theorem merge_depends (depends : Depends state pool) :
    Depends (merge state first last) (pool ++ mergeDelta state first last) := by
  intro a b same
  rw [merge_models,merge_models]
  have old := depends a b (fun n member => same n (List.mem_append_left _ member))
  have atoms : PresenceNormalForm.All CommonNominalFullCarrier.model a
      (GeneralNominalDemandMerging.outputAtoms first.observed last.observed) ↔
      PresenceNormalForm.All CommonNominalFullCarrier.model b
      (GeneralNominalDemandMerging.outputAtoms first.observed last.observed) := by
    unfold PresenceNormalForm.All
    apply forall_congr'; intro atom
    apply forall_congr'; intro member
    apply GeneralNominalCenteredModelExtension.atom_same
    intro n present
    exact same n (List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨atom,member,present⟩)))
  have history (one : Models state a) (two : Models state b) := history_iff state (merge state first last).core
    (fun _ _ => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
      (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h)) one two
    (fun n member => same n (List.mem_append_right _ (List.mem_append_right _ member)))
  constructor
  · rintro ⟨valid,held,live⟩
    exact ⟨old.mp valid,atoms.mp held,(history valid (old.mp valid)).mp live⟩
  · rintro ⟨valid,held,live⟩
    exact ⟨old.mpr valid,atoms.mpr held,(history (old.mpr valid) valid).mpr live⟩

theorem history_subset (state : State roles) (after : GeneralNominalCenteredSteps.State roles) :
    historySources state after ⊆ liveSources state.effects after := by
  intro name member
  obtain ⟨prior,present,within⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨prior,present,GeneralDictionaryClassDelta227.delta_subset _ _ _ _ (GeneralDictionaryNameDelta227.delta_subset within)⟩

theorem history_empty (state : State roles) (after : GeneralNominalCenteredSteps.State roles)
    (same : ∀ prior ∈ state.effects, ∀ output,
      output ∈ GeneralNominalCenteredHeadOutputs.requests after prior.plan.packet.site.occurrence →
      output ∈ GeneralNominalCenteredHeadOutputs.requests state.core prior.plan.packet.site.occurrence) :
    historySources state after = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨prior,present,within⟩ := List.mem_flatMap.mp member
  have included := GeneralDictionaryNameDelta227.delta_subset within
  rw [GeneralDictionaryClassDelta227.no_new (same prior present)] at included
  cases included
end Yulang.GeneralDictionaryHistoricalLive227
