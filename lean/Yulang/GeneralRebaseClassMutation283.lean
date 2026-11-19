import Yulang.GeneralRebaseClassFrontier283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseClassMutation283
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty)
open GeneralNominalVersionedAdministrative232 (merge merge_models)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open Core.PresenceGeneration (CompTerm)
open GeneralRebaseClassFrontier283 (compile exact no_growth)
open GeneralRebaseClassDelta283 (Growth class_factor)
open GeneralRebaseIncrementalGate283 (new_requests)
open GeneralNominalVersionedInstall232 (installCore)
open GeneralNominalCenteredHeadStepEffects (requests_subset_of_sites_aliases)

noncomputable def frontier (before after : GeneralNominalCenteredSteps.State roles)
    (prior : Effect roles) (mapping : Nat → CompTerm Nat) :=
  compile prior.plan mapping (requests before prior.plan.packet.site.occurrence)
    (requests after prior.plan.packet.site.occurrence)

theorem install_exact (state : State roles) (candidate prior : Effect roles)
    (mapping : Nat → CompTerm Nat) (base : Assignment) :
    (frontier state.core (installCore state.core candidate.plan) prior mapping).Holds base ↔
      new_requests state candidate prior (read mapping base) :=
  exact prior.plan mapping _ _ base

theorem terminal_no_delta (state : State roles) (candidate prior : Effect roles) (base : Assignment)
    (closed : GeneralNominalVersionedFrame231.children candidate.plan.packet = []) :
    new_requests state candidate prior base := by
  exact no_growth _ _ _ _ (fun _ listed => (GeneralNominalVersionedTerminal232.requests_iff closed).mp listed)

theorem merge_new (state : State roles) (first last : Site roles) (prior : Effect roles) (a : Assignment) :
    prior.Live (merge state first last).core a ↔ prior.Live state.core a ∧
      (frontier state.core (merge state first last).core prior CompTerm.var).Holds a := by
  have grow := requests_subset_of_sites_aliases
    (before := state.core) (after := (merge state first last).core) (fun _ h => h)
    (fun _ h => List.mem_cons_of_mem _ h) (root := prior.plan.packet.site.occurrence)
  refine (class_factor state.core (merge state first last).core prior.plan.packet.site.occurrence
    prior.plan a (fun o h => grow h)).trans (and_congr Iff.rfl ?_)
  exact (exact prior.plan CompTerm.var _ _ a).symm

theorem exact_merge (state : State roles) (empty : LegacyEmpty state) (first last : Site roles) (a : Assignment) :
    Models (merge state first last) a ↔ Models state a ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model a
        (GeneralNominalDemandMerging.outputAtoms first.observed last.observed) ∧
      ∀ prior ∈ state.effects, (frontier state.core (merge state first last).core prior CompTerm.var).Holds a := by
  rw [merge_models]
  constructor
  · rintro ⟨models,atoms,legacy,live⟩
    exact ⟨models,atoms,fun p listed => ((merge_new state first last p a).mp (live p listed)).2⟩
  · rintro ⟨models,atoms,growth⟩
    refine ⟨models,atoms,?_,?_⟩
    · intro p listed
      rw [empty.2] at listed
      cases listed
    · intro p listed
      exact (merge_new state first last p a).mpr ⟨(models.2.2 p listed).2,growth p listed⟩

end Yulang.GeneralRebaseClassMutation283
