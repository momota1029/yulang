import Yulang.GeneralNominalCenteredHeadStepSimulation

set_option backward.isDefEq.respectTransparency false

/-! Shared reachable inputs for distinct registries contain no installations.
Their passive prefix and empty effect ledger are registry independent. -/
namespace Yulang.GeneralNominalCenteredHeadStepRegistry
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepBoundary (boundary)
open GeneralNominalCenteredHeadStepSimulation (packet_at)
variable {roles : Roles.RoleDecls}
variable {before after state : State roles} {root focus : Occurrence roles}

def RegistryJournal (registry : Registry) (state : State roles) : Prop :=
  ∀ packet ∈ state.core.erased.current.packets, packet.registry = registry

theorem registry_at (recorded : RegistryJournal registry before) (action : At registry before focus after) :
    RegistryJournal registry after := by
  intro packet member
  cases action with
  | administrative _ _ action => cases action <;> exact recorded packet member
  | refresh | merge => exact recorded packet member
  | install plan support enabled novel =>
      rcases List.mem_cons.mp member with rfl | member
      · exact enabled.frame.registry_eq
      · exact recorded packet member

theorem registry_trace (path : B4Target.Steps (Step registry root) (initial context root) state) : RegistryJournal registry state := by
  induction path with
  | refl => intro _ member; cases member
  | tail _ step ih => exact registry_at ih step.choose_spec.2

theorem registry_reachable (reachable : B4TargetV6.Reachable (boundary roles) registry root state) : RegistryJournal registry state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact registry_trace path

theorem distinct_shared_packet_free (different : first ≠ last)
    (one : B4TargetV6.Reachable (boundary roles) first root state)
    (two : B4TargetV6.Reachable (boundary roles) last root state) : state.core.erased.current.packets = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro packet member
  exact different ((registry_reachable one packet member).symm.trans (registry_reachable two packet member))

theorem packet_free_at (action : At registry before focus after)
    (empty : after.core.erased.current.packets = []) (last : Registry) :
    At last before focus after ∧ GeneralNominalCenteredSteps.At registry before.core focus after.core ∧
      after.effects = before.effects := by
  cases action with
  | administrative focus next action =>
      exact ⟨.administrative _ _ (GeneralNominalCenteredRegistryPassive.administrative action last),.administrative _ _ action,rfl⟩
  | refresh focus context certificate source member unknown known =>
      exact ⟨.refresh focus context certificate source member unknown known,.refresh focus context certificate source member unknown known,rfl⟩
  | merge a b support one two inputs novel guard =>
      exact ⟨.merge a b support one two inputs novel guard,.merge a b support one two inputs novel guard,rfl⟩
  | install => cases empty

theorem packet_free_steps (path : B4Target.Steps (Step registry root) before after)
    (empty : after.core.erased.current.packets = []) (last : Registry) :
    B4Target.Steps (Step last root) before after ∧
      B4Target.Steps (GeneralNominalCenteredSteps.Step registry root) before.core after.core ∧ after.effects = before.effects := by
  induction path with
  | refl => exact ⟨.refl,.refl,rfl⟩
  | @tail middle finish path step ih =>
      have prior : middle.core.erased.current.packets = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro packet member
        have retained := packet_at step.choose_spec.2 member
        rw [empty] at retained
        cases retained
      obtain ⟨next,old,effects⟩ := packet_free_at step.choose_spec.2 empty last
      obtain ⟨priorPath,core,effectsBefore⟩ := ih prior
      exact ⟨.tail priorPath ⟨step.choose,step.choose_spec.1,next⟩,
        .tail core ⟨step.choose,step.choose_spec.1,old⟩,effects.trans effectsBefore⟩

theorem initial_reorders (order : Reorders first last) (given : (boundary roles).Initial first root state) :
    (boundary roles).Initial last root state := by
  obtain ⟨context,labels,source,point,ground,rfl⟩ := given
  exact ⟨context,labels,GeneralDictionaryInitialSource.source_reorders first last order context root source,point,ground,rfl⟩

theorem packet_free_reachable (order : Reorders first last)
    (reachable : B4TargetV6.Reachable (boundary roles) first root state)
    (empty : state.core.erased.current.packets = []) : B4TargetV6.Reachable (boundary roles) last root state := by
  obtain ⟨start,source,path⟩ := reachable
  exact ⟨start,initial_reorders order source,(packet_free_steps path empty last).1⟩

theorem packet_free_self (last : Registry)
    (reachable : B4TargetV6.Reachable (boundary roles) first root state)
    (empty : state.core.erased.current.packets = []) : GeneralNominalCenteredHeadStepSimulation.Related first last state state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  have old := packet_free_steps path empty last
  have recorded := GeneralNominalCenteredHeadStepSimulation.recorded_trace path
  have coreSource : B4TargetV5.Reachable (GeneralNominalCenteredAdministrativeLocal.boundary roles) first root state.core :=
    ⟨GeneralNominalCenteredSteps.initial context root,⟨context,labels,source,point,ground,rfl⟩,old.2.1⟩
  refine ⟨⟨GeneralNominalCenteredPermutationRepresentation.reachable_packet_free last coreSource empty,?_⟩,recorded,recorded⟩
  rw [old.2.2]
  exact .nil

end Yulang.GeneralNominalCenteredHeadStepRegistry
