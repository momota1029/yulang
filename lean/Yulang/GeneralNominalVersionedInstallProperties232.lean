import Yulang.GeneralNominalVersionedInstall232
set_option backward.isDefEq.respectTransparency false

/-! Structural properties of the explicit versioned install transformer.
No automatic satisfiability, termination, or general kernel completion follows
from these storage and reachability facts. -/
namespace Yulang.GeneralNominalVersionedInstallProperties232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedInstall232
open GeneralNominalSaturationState (Generated Alias)

variable {roles : Roles.RoleDecls} {core : GeneralNominalCenteredSteps.State roles}
  {plan : Plan roles}

theorem raw_sites_included : core.erased.current.sites ⊆ (installCore core plan).erased.current.sites :=
  fun _ h => List.mem_append_left _ h

theorem centers_included : core.sites ⊆ (installCore core plan).sites :=
  fun _ h => List.mem_append_left _ h

theorem edges_included : core.erased.current.edges ⊆ (installCore core plan).erased.current.edges :=
  fun _ h => List.mem_append_left _ h

theorem aliases_equal : (installCore core plan).erased.current.aliases = core.erased.current.aliases := rfl

theorem alias_forward (given : Alias core.erased.current first last) :
    Alias (installCore core plan).erased.current first last := by
  induction given with
  | refl => exact .refl _
  | edge member => exact .edge member
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem alias_iff : Alias (installCore core plan).erased.current first last ↔
    Alias core.erased.current first last := by
  constructor
  · intro given
    induction given with
    | refl => exact .refl _
    | edge member => exact .edge member
    | symm _ ih => exact .symm ih
    | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  · exact alias_forward

theorem generated_preserved (given : Generated core.erased.current root focus) :
    Generated (installCore core plan).erased.current root focus := by
  induction given with
  | root => exact .root
  | child _ edge ih => exact .child ih (edges_included edge)
  | alias _ first last equal ih =>
    exact .alias ih (raw_sites_included first) (raw_sites_included last) (alias_forward equal)

theorem children_generated (given : Generated core.erased.current root plan.packet.site.occurrence)
    (member : child ∈ GeneralNominalVersionedFrame231.children plan.packet) :
    Generated (installCore core plan).erased.current root child :=
  GeneralNominalVersionedChildren232.generated_child _
    (fun _ h => List.mem_append_right _ h) (generated_preserved given) member

theorem source_base_preserved (context : plan.packet.context = core.erased.current.context) :
    (installCore core plan).erased.current.context.state.base = core.erased.current.context.state.base := by
  rw [← context]
  rfl

theorem seed_preserved (context : plan.packet.context = core.erased.current.context) :
    (installCore core plan).erased.current.context.state.seed = core.erased.current.context.state.seed := by
  rw [← context]
  rfl

theorem known_iff (context : plan.packet.context = core.erased.current.context) :
    GeneralNominalState.Known (installCore core plan).erased.current.context.state name ↔
      GeneralNominalState.Known core.erased.current.context.state name := by
  rw [← context]
  exact GeneralNominalVersionedInstallation231.replay_known plan name

theorem keys_owned (member : key ∈ GeneralNominalVersionedInstallation231.allocated plan.packet) :
    key ∈ (installCore core plan).erased.current.context.state.allocated :=
  GeneralNominalVersionedInstallation231.replay_keys_owned plan member

theorem old_keys_owned (context : plan.packet.context = core.erased.current.context)
    (member : key ∈ core.erased.current.context.state.allocated) :
    key ∈ (installCore core plan).erased.current.context.state.allocated := by
  have old : key ∈ plan.packet.context.state.allocated := context.symm ▸ member
  exact List.mem_append_left _ old

theorem packets_included : core.erased.current.packets ⊆ (installCore core plan).erased.current.packets :=
  fun _ h => List.mem_cons_of_mem _ h

theorem packet_recorded : plan.packet ∈ (installCore core plan).erased.current.packets := List.mem_cons_self ..

theorem plans_included : state.plans ⊆ (install state effect).plans :=
  fun _ h => List.mem_cons_of_mem _ h

theorem effects_included : state.effects ⊆ (install state effect).effects :=
  fun _ h => List.mem_cons_of_mem _ h

end Yulang.GeneralNominalVersionedInstallProperties232
