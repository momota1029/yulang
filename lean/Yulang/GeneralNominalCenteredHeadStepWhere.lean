import Yulang.GeneralNominalCenteredHeadStepBoundary
import Yulang.GeneralNominalCenteredAdministrativeWhere

/-! Registered parents and the existing child allocation bound all local
child chains. This proof is independent of operational accessibility. -/
namespace Yulang.GeneralNominalCenteredHeadStepWhere
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepBoundary
open CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls}

def rank (state : State roles) (root : Occurrence roles) : Nat :=
  GeneralNominalCenteredAdministrativeWhere.ceiling state.core + 1 - root.identity

theorem selected_bounded (selected : Local registry state root (.selected key children)) :
    root.identity ≤ GeneralNominalCenteredAdministrativeWhere.ceiling state.core := by
  obtain ⟨site,member,same⟩ := (selected_ready selected).1
  exact GeneralNominalCenteredWhere.member_max _ _
    (List.mem_map.mpr ⟨site,member,congrArg Occurrence.identity same⟩)

theorem selected_child_above (selected : Local registry state root (.selected key children))
    (child : Occurrence roles) (member : child ∈ children) : root.identity < child.identity := by
  cases selected with
  | selected safe unique clear =>
      obtain ⟨_,declaration,_,checked,_,_,bounds,_,_,childrenEq⟩ := unique.1
      let packet : GeneralNominalSaturationState.Packet roles :=
        ⟨registry,state.core.erased.current.context,
          GeneralNominalDemandMerging.pointSite (GeneralNominalCenteredHeadCandidates.inputs root),declaration,checked,bounds⟩
      have same : children = packet.children := childrenEq
      exact GeneralNominalCenteredWhere.packet_child_above packet child (same ▸ member)

theorem child_rank (edge : Child (Local registry state) child root) : rank state child < rank state root := by
  obtain ⟨key,children,selected,member⟩ := edge
  have bounded := selected_bounded selected
  have above := selected_child_above selected child member
  unfold rank
  omega

theorem whereAccessible (registry : Registry) (state : State roles) (root : Occurrence roles) :
    Acc (Child (Local registry state)) root := by
  have all : ∀ n, ∀ root, rank state root = n → Acc (Child (Local registry state)) root := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro root equal
        refine Acc.intro root ?_
        intro child edge
        exact ih _ (equal ▸ child_rank edge) child rfl
  exact all _ root rfl

end Yulang.GeneralNominalCenteredHeadStepWhere
