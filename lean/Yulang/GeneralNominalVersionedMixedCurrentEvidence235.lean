import Yulang.GeneralNominalVersionedMixedSourceBoundary234
set_option backward.isDefEq.respectTransparency false
/-! Current effect semantics and ordered-child identification. This local layer
keeps semantic commitment explicit; the stable layer derives it operationally. -/
namespace Yulang.GeneralNominalVersionedMixedCurrentEvidence235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedEvidence231
open GeneralNominalVersionedMixedKernel234
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

theorem selected_unique
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state root (.selected key children)) :
    GeneralNominalVersionedCandidates231.Unique registry state.core.erased.current.context root key children := by
  have chosen := (B4TargetV7.selected_iff.mp (B4TargetV8.selected_iff.mp
    (GeneralNominalVersionedMixedBoundary234.local_iff.mp selected)).1).1
  cases chosen with
  | selected _ unique _ => exact unique

theorem selected_identifies
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (occurrence : effect.plan.packet.site.occurrence = root)
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state root (.selected key children)) :
    effect.plan.packet.declaration.id = key ∧ GeneralNominalVersionedFrame231.children effect.plan.packet = children := by
  have current := effect.unique
  rw [registryEq,snapshot,occurrence] at current
  exact (selected_unique selected).2 _ _ current.1

theorem current_certificate (snapshot : effect.snapshot = state.core)
    (committed : Committed state effect.plan) (valid : Models state model) :
    Certificate effect.registry state.core model effect.plan.packet.site.occurrence effect.plan.packet.declaration.id
      (GeneralNominalVersionedFrame231.children effect.plan.packet) effect.plan :=
  certificate_of_semantics (snapshot ▸ effect.frame) rfl (committed.1 model valid).1
    (snapshot ▸ effect.ready) (committed.1 model valid).2

theorem selected_certificate
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (occurrence : effect.plan.packet.site.occurrence = root)
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state root (.selected key children))
    (committed : Committed state effect.plan) (valid : Models state model) :
    Certificate registry state.core model root key children effect.plan := by
  have certificate := current_certificate snapshot committed valid
  have same := selected_identifies registryEq snapshot occurrence selected
  rw [registryEq,occurrence,same.1,same.2] at certificate
  exact certificate

theorem selected_evidence
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (occurrence : effect.plan.packet.site.occurrence = root)
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state root (.selected key children))
    (committed : Committed state effect.plan) (valid : Models state model)
    (childEvidence : CommonRoleOutermostResolver.All₂ (Evidence registry state.core model) children dictionaries) :
    Evidence registry state.core model root (.node key dictionaries) :=
  evidence_node ⟨effect.plan,selected_certificate registryEq snapshot occurrence selected committed valid⟩ childEvidence

theorem selected_child_edge
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (occurrence : effect.plan.packet.site.occurrence = root)
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state root (.selected key children))
    (committed : Committed state effect.plan) (member : child ∈ children) :
    (root,child) ∈ state.core.erased.current.edges := by
  have same := selected_identifies registryEq snapshot occurrence selected
  rw [← same.2] at member
  simpa only [occurrence] using committed.2 child member

end Yulang.GeneralNominalVersionedMixedCurrentEvidence235
