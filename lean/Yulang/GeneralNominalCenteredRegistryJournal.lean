import Yulang.GeneralNominalCenteredAdministrativeComposition

/-! A recorded packet retains the registry of the centered execution.
Shared reachable inputs for distinct registries therefore have no packets. -/
namespace Yulang.GeneralNominalCenteredRegistryJournal
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal

variable {roles : Roles.RoleDecls}

def RegistryJournal (registry : Registry) (state : State roles) : Prop :=
  ∀ packet ∈ state.erased.current.packets, packet.registry = registry

theorem registry_at (recorded : RegistryJournal registry before)
    (action : At registry before focus after) : RegistryJournal registry after := by
  intro packet member
  cases action with
  | administrative focus after action =>
    cases action <;> exact recorded packet member
  | refresh | merge => exact recorded packet member
  | install plan support enabled novel guard =>
    rcases List.mem_cons.mp member with rfl | old
    · exact enabled.1.1
    · exact recorded packet old

theorem registry_trace
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    RegistryJournal registry state := by
  induction path with
  | refl => intro packet member; cases member
  | tail path step ih => exact registry_at ih step.choose_spec.2

theorem registry_reachable
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    RegistryJournal registry state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact registry_trace path

theorem shared_packet_registry
    (firstPath : B4TargetV5.Reachable (boundary roles) first root state)
    (lastPath : B4TargetV5.Reachable (boundary roles) last root state)
    (recorded : packet ∈ state.erased.current.packets) : first = last :=
  (registry_reachable firstPath packet recorded).symm.trans
    (registry_reachable lastPath packet recorded)

theorem distinct_shared_packet_free
    (distinct : first ≠ last)
    (firstPath : B4TargetV5.Reachable (boundary roles) first root state)
    (lastPath : B4TargetV5.Reachable (boundary roles) last root state) :
    state.erased.current.packets = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro packet recorded
  exact distinct (shared_packet_registry firstPath lastPath recorded)

theorem shared_reachable_cases
    (firstPath : B4TargetV5.Reachable (boundary roles) first root state)
    (lastPath : B4TargetV5.Reachable (boundary roles) last root state) :
    first = last ∨ state.erased.current.packets = [] := by
  classical
  by_cases same : first = last
  · exact Or.inl same
  · exact Or.inr (distinct_shared_packet_free same firstPath lastPath)

theorem packet_at (action : At registry before focus after)
    (recorded : packet ∈ before.erased.current.packets) :
    packet ∈ after.erased.current.packets := by
  cases action with
  | administrative focus after action => cases action <;> exact recorded
  | refresh | merge => exact recorded
  | install => exact List.mem_cons_of_mem _ recorded

theorem packet_steps (path : B4Target.Steps (Step registry root) before after)
    (recorded : packet ∈ before.erased.current.packets) :
    packet ∈ after.erased.current.packets := by
  induction path with
  | refl => exact recorded
  | tail path step ih => exact packet_at step.choose_spec.2 ih

end Yulang.GeneralNominalCenteredRegistryJournal
