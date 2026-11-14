import Yulang.GeneralNominalCenteredRegistryJournal
import Yulang.GeneralCanonicalRegistry

/-! A packet-free prefix contains no installation. All of its actual actions
transport to another registry without changing any state. -/
namespace Yulang.GeneralNominalCenteredRegistryPassive
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal

variable {roles : Roles.RoleDecls}

theorem administrative (action : GeneralNominalSharedSteps.Administrative first state focus after)
    (last : Registry) : GeneralNominalSharedSteps.Administrative last state focus after := by
  cases action with
  | enqueue linked absent => exact .enqueue _ linked absent
  | refresh context certificate source member unknown known =>
    exact .refresh _ context certificate source member unknown known
  | equate one two a b equal novel => exact .equate _ one two a b equal novel
  | reobserve revision certificate improved => exact .reobserve _ revision certificate improved

theorem packet_free_at (action : At first before focus after)
    (empty : after.erased.current.packets = []) (last : Registry) : At last before focus after := by
  cases action with
  | administrative focus after action => exact .administrative _ _ (administrative action last)
  | refresh focus context certificate source member unknown known =>
    exact .refresh focus context certificate source member unknown known
  | merge first last support one two same novel guard => exact .merge _ _ _ one two same novel guard
  | install => cases empty

theorem packet_free_step (step : Step first root before after)
    (empty : after.erased.current.packets = []) (last : Registry) : Step last root before after :=
  ⟨step.choose,step.choose_spec.1,packet_free_at step.choose_spec.2 empty last⟩

theorem packet_free_steps (path : B4Target.Steps (Step first root) before after)
    (empty : after.erased.current.packets = []) (last : Registry) :
    B4Target.Steps (Step last root) before after := by
  induction path with
  | refl => exact .refl
  | @tail middle finish path step ih =>
    have prior : middle.erased.current.packets = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro packet member
      have recorded := GeneralNominalCenteredRegistryJournal.packet_at step.choose_spec.2 member
      rw [empty] at recorded
      cases recorded
    exact .tail (ih prior) (packet_free_step step empty last)

theorem packet_free_reachable
    (order : GeneralRegistryReordering.Reorders first last)
    (reachable : B4TargetV5.Reachable (boundary roles) first root state)
    (empty : state.erased.current.packets = []) :
    B4TargetV5.Reachable (boundary roles) last root state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact ⟨initial context root,
    ⟨context,labels,GeneralDictionaryInitialSource.source_reorders first last order context root source,
      point,ground,rfl⟩,packet_free_steps path empty last⟩

theorem canonical_reachable
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (empty : state.erased.current.packets = []) :
    B4TargetV5.Reachable (boundary roles) (GeneralCanonicalRegistry.canonical registry) root state :=
  packet_free_reachable (GeneralCanonicalRegistry.reorders_canonical registry) reachable empty

end Yulang.GeneralNominalCenteredRegistryPassive
