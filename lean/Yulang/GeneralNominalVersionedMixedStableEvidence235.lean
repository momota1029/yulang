import Yulang.GeneralNominalVersionedMixedCurrentEvidence235
import Yulang.GeneralNominalVersionedMixedStableLaws235
set_option backward.isDefEq.respectTransparency false
/-! Nonterminal evidence from actual current installability and full Stable.
The committed packet/effects are conclusions, not model-indexed assumptions. -/
namespace Yulang.GeneralNominalVersionedMixedStableEvidence235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedEvidence231 GeneralNominalVersionedMixedCurrentEvidence235
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

theorem certificate
    (stable : Stable registry state root)
    (generated : Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (enabled : Installable registry state effect) (valid : Models state model) :
    Certificate registry state.core model effect.plan.packet.site.occurrence effect.plan.packet.declaration.id
      (GeneralNominalVersionedFrame231.children effect.plan.packet) effect.plan := by
  have result := current_certificate enabled.snapshot_eq
    (GeneralNominalVersionedMixedStableLaws235.install_committed stable generated enabled) valid
  rw [enabled.registry_eq] at result
  exact result

theorem selected_node
    (stable : Stable registry state demand)
    (enabled : Installable registry state effect)
    (occurrence : effect.plan.packet.site.occurrence = demand)
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state demand (.selected key children))
    (valid : Models state model)
    (childEvidence : CommonRoleOutermostResolver.All₂ (Evidence registry state.core model) children dictionaries) :
    Evidence registry state.core model demand (.node key dictionaries) :=
  selected_evidence enabled.registry_eq enabled.snapshot_eq occurrence selected
    (GeneralNominalVersionedMixedStableLaws235.install_committed stable (occurrence.symm ▸ Generated.root) enabled)
    valid childEvidence

theorem selected_generated_children
    (stable : Stable registry state demand)
    (enabled : Installable registry state effect)
    (occurrence : effect.plan.packet.site.occurrence = demand)
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state demand (.selected key children))
    (reached : demand = root ∨ Generated state.core.erased.current root demand)
    (member : child ∈ children) : Generated state.core.erased.current root child := by
  have edge := selected_child_edge enabled.registry_eq enabled.snapshot_eq occurrence selected
    (GeneralNominalVersionedMixedStableLaws235.install_committed stable (occurrence.symm ▸ Generated.root) enabled) member
  have parent : Generated state.core.erased.current root demand := reached.elim (fun same => same ▸ Generated.root) id
  exact .child parent edge

end Yulang.GeneralNominalVersionedMixedStableEvidence235
