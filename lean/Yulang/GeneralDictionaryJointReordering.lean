import Yulang.GeneralNominalCandidateReordering

/-! Registry reordering preserves the actual joint alias applicability residual
at one fixed state. The same model satisfies every alias; no existential model
is chosen separately for each site. Executor final-state agreement is not proved. -/
namespace Yulang.GeneralDictionaryJointReordering
open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalJointCandidates
variable {roles : Roles.RoleDecls} {first last : Registry}

theorem branch_forward (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (key : Nat)
    (model : GeneralNominalCommonBridge.Assignment)
    (branch : BranchAt first state root key model) : BranchAt last state root key model := by
  obtain ⟨a,visible,ac,identity,role,prepared,bounds,located,holds⟩ := branch
  obtain ⟨b,present,pair⟩ := reorders_visible order a visible
  let bc := GeneralNominalCandidateReordering.checked_declaration order pair ac
  exact ⟨b,present,bc,pair.id.symm.trans identity,pair.role.symm.trans role,
    (GeneralNominalRegistryOrder.prepared order roleEq pair state.context root ac bc).mp prepared,
    bounds,located,(GeneralNominalRegistryOrder.branch_models order roleEq pair state.context root ac bc bounds model).mp holds⟩

theorem branch (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (key : Nat)
    (model : GeneralNominalCommonBridge.Assignment) :
    BranchAt first state root key model ↔ BranchAt last state root key model :=
  ⟨branch_forward order roleEq state root key model,
    branch_forward (GeneralRegistryChildOrder.reorders_symm order)
      (order.2.1.symm.trans roleEq) state root key model⟩

theorem joint_forward (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (key : Nat)
    (joint : Joint first state root key) : Joint last state root key := by
  obtain ⟨consistent,model,valid,atRoot,aliases⟩ := joint
  exact ⟨consistent,model,valid,(branch order roleEq state root key model).mp atRoot,
    fun site related => (branch order roleEq state site.occurrence key model).mp (aliases site related)⟩

theorem joint (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (key : Nat) :
    Joint first state root key ↔ Joint last state root key :=
  ⟨joint_forward order roleEq state root key,
    joint_forward (GeneralRegistryChildOrder.reorders_symm order)
      (order.2.1.symm.trans roleEq) state root key⟩

theorem survivor (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles)) :
    GeneralNominalJointCandidates.Survivor first state root key children ↔
    GeneralNominalJointCandidates.Survivor last state root key children :=
  and_congr (GeneralNominalCandidateReordering.survivor order roleEq state.context root key children)
    (joint order roleEq state root key)

end Yulang.GeneralDictionaryJointReordering
