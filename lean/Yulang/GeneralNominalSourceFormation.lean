import Yulang.GeneralNominalCycleCompatibility

/-! Initial finite source data and its closure under the unchanged Step.
Formation contains no rank, readback, finite work basis or accessibility field.
The nominal state already checks normalized observations and finite slot IDs.
An inference-to-initial-data producer is not asserted here. -/
namespace Yulang.GeneralNominalSourceFormation

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCycleSteps

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

structure InitialSource (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop where
  roles_agree : registry.roles = roles
  metadata : GeneralNominalRecursiveCandidates.Metadata registry context
  linked : GeneralNominalState.Linked context.state root.demand
  intervals : ∀ model, GeneralNominalState.Models context.state model →
    ∀ index, CommonNominalFullCarrier.Subtype (model (root.demand.arguments index).1).1
      (model (root.demand.arguments index).2).1
  below_seed : ∀ source ∈ GeneralNominalState.sources context.state, source ≤ context.state.seed
  unallocated : context.state.allocated = []

inductive SourceFormed (registry : Registry) (root : Occurrence roles) : State roles → Prop
  | initial (context) : InitialSource registry context root → SourceFormed registry root (initial context root)
  | update : SourceFormed registry root before → Step registry root before after → SourceFormed registry root after

theorem formed_iff_reachable (state : State roles) :
    SourceFormed registry root state ↔ ∃ context, InitialSource registry context root ∧
      B4Target.Steps (Step registry root) (initial context root) state := by
  constructor
  · intro formed
    induction formed with
    | initial context valid => exact ⟨context,valid,.refl⟩
    | update _ step ih =>
        obtain ⟨context,valid,path⟩ := ih
        exact ⟨context,valid,.tail path step⟩
  · rintro ⟨context,valid,path⟩
    induction path with
    | refl => exact .initial context valid
    | tail _ step ih => exact .update ih step

theorem step_preserves {before after : State roles}
    (formed : SourceFormed registry root before) (step : Step registry root before after) :
    SourceFormed registry root after := .update formed step

theorem initial_journal (context : GeneralNominalCandidates.Context) (root : Occurrence roles) :
    (initial context root).packets = [] ∧ (initial context root).edges = [] ∧
      (initial context root).aliases = [] := ⟨rfl,rfl,rfl⟩

theorem seed_update {before after : State roles} {focus : Occurrence roles}
    (step : At registry before focus after) : after.context.state.seed = before.context.state.seed := by
  cases step with
  | enqueue => rfl
  | install packet emitted enabled _ =>
      change packet.context.state.seed = before.context.state.seed
      rw [enabled.2.1]
  | merge => rfl
  | refresh _ _ certificate _ _ _ _ => exact certificate.refines.seed

theorem seed_trace {before after : State roles}
    (path : B4Target.Steps (Step registry root) before after) :
    after.context.state.seed = before.context.state.seed := by
  induction path with
  | refl => rfl
  | tail _ step ih => exact (seed_update step.choose_spec.2).trans ih

theorem metadata_update {before after : State roles} {focus : Occurrence roles}
    (metadata : GeneralNominalRecursiveCandidates.Metadata registry before.context)
    (step : At registry before focus after) : GeneralNominalRecursiveCandidates.Metadata registry after.context := by
  cases step with
  | enqueue => exact metadata
  | install packet emitted enabled _ =>
      change GeneralNominalRecursiveCandidates.Metadata registry packet.context
      rw [enabled.2.1]
      exact metadata
  | merge => exact metadata
  | refresh _ _ certificate _ _ _ _ =>
      refine ⟨metadata.1.trans certificate.refines.constructors.symm,?_⟩
      dsimp only [regenerate]
      rw [certificate.interpretation]
      exact metadata.2

theorem formed_metadata (state : State roles) (formed : SourceFormed registry root state) :
    registry.roles = roles ∧ GeneralNominalRecursiveCandidates.Metadata registry state.context := by
  induction formed with
  | initial context valid => exact ⟨valid.roles_agree,valid.metadata⟩
  | update _ step ih => exact ⟨ih.1,metadata_update ih.2 step.choose_spec.2⟩

theorem initial_fresh (context : GeneralNominalCandidates.Context)
    (formed : InitialSource registry context root) (invocation : Nat) :
    GeneralNominalAllocation.Fresh context.state registry invocation := by
  intro origin _ collision
  exact False.elim (GeneralNominalAllocation.source_initial_fresh context.state registry invocation origin _
    (formed.below_seed _ collision) rfl)

theorem formed_provenance (state : State roles) (formed : SourceFormed registry root state) :
    ∃ context, InitialSource registry context root ∧ state.context.state.seed = context.state.seed ∧
      (∀ model, Models state model → GeneralNominalState.Models context.state model) ∧
      GeneralNominalSaturationInvariants.Canonical state ∧ GeneralNominalSaturationInvariants.EdgesRecorded state := by
  obtain ⟨context,valid,path⟩ := (formed_iff_reachable state).mp formed
  have journal := GeneralNominalSaturationInvariants.reachable_journal
    (GeneralNominalCycleCompatibility.steps_legacy path)
  exact ⟨context,valid,seed_trace path,fun model models =>
    (initial_models context root model).mp (steps_models path model models),journal.1,journal.2.1⟩

theorem generated_registered (state : State roles) (formed : SourceFormed registry root state)
    (focus : Occurrence roles) (generated : Generated state root focus) :
    ∃ site ∈ state.sites, site.occurrence = focus := by
  obtain ⟨context,_,path⟩ := (formed_iff_reachable state).mp formed
  exact GeneralNominalCycleCompatibility.generated_recorded path generated

theorem enqueue_unavailable (state : State roles) (formed : SourceFormed registry root state)
    (focus : Occurrence roles) (generated : Generated state root focus) :
    ¬ (∀ site ∈ state.sites, site.occurrence ≠ focus) := by
  obtain ⟨site,member,equal⟩ := generated_registered state formed focus generated
  exact fun absent => absent site member equal

/-- Reservations are real new source identities. A bound by just the initial
source list is not preserved by installation, even though the seed is fixed. -/
theorem installation_reserves (packet : Packet roles)
    (origin : GeneralNominalAllocation.Origin)
    (member : origin ∈ GeneralNominalAllocation.keys packet.registry packet.site.occurrence.identity) :
    GeneralNominalAllocation.source packet.context.state packet.registry packet.site.occurrence.identity origin ∈
      GeneralNominalState.sources packet.privateContext.state ∧
    packet.context.state.seed <
      GeneralNominalAllocation.source packet.context.state packet.registry packet.site.occurrence.identity origin := by
  constructor
  · apply List.mem_append_left
    apply List.mem_append_right
    change _ ∈ packet.context.state.reserved ++
      GeneralNominalAllocation.reserved packet.context.state packet.registry packet.site.occurrence.identity ++ []
    apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_map.mpr ⟨origin,member,rfl⟩)
  · exact GeneralNominalIdentities.source_above_seed _ origin

end Yulang.GeneralNominalSourceFormation
