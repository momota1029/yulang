import Yulang.GeneralNominalCenteredAdministrativeLocal

/-! Every selected parent is registered, and every candidate child has a larger
identity. A finite snapshot therefore bounds all local child chains, including
snapshots before saturation. -/
namespace Yulang.GeneralNominalCenteredAdministrativeWhere
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal CommonRoleOutermostResolver

variable {roles : Roles.RoleDecls}

def ceiling (state : State roles) : Nat :=
  (state.sites.map fun site => site.occurrence.identity).foldr max 0

def rank (state : State roles) (root : Occurrence roles) : Nat := ceiling state + 1 - root.identity

theorem selected_bounded (selected : Local registry state root (.selected key children)) :
    root.identity ≤ ceiling state := by
  obtain ⟨site,member,same⟩ := (selected_ready selected).1
  exact GeneralNominalCenteredWhere.member_max _ _
    (List.mem_map.mpr ⟨site,member,congrArg Occurrence.identity same⟩)

theorem selected_child_above (selected : Local registry state root (.selected key children))
    (child : Occurrence roles) (member : child ∈ children) : root.identity < child.identity := by
  have old := selected_old selected
  cases old with
  | selected safe unique =>
    obtain ⟨_,declaration,_,checked,_,_,bounds,_,_,childrenEq⟩ := unique.1
    let packet : GeneralNominalSaturationState.Packet roles :=
      ⟨registry,state.erased.current.context,GeneralNominalDemandMerging.pointSite root,declaration,checked,bounds⟩
    have same : children = packet.children := childrenEq
    exact GeneralNominalCenteredWhere.packet_child_above packet child (same ▸ member)

theorem child_rank (edge : Child (Local registry state) child root) : rank state child < rank state root := by
  obtain ⟨key,children,selected,member⟩ := edge
  have bounded := selected_bounded selected
  have above := selected_child_above selected child member
  unfold rank
  omega

theorem local_where_accessible (registry : Registry) (state : State roles) (root : Occurrence roles) :
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

theorem boundary_where_accessible (registry : Registry) (state : State roles) (root : Occurrence roles) :
    Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) root := by
  have all := local_where_accessible registry state root
  induction all with
  | intro parent below ih =>
    refine Acc.intro parent ?_
    rintro child ⟨key,children,selected,member⟩
    exact ih child ⟨key,children,(local_correspondence registry state parent _).mp selected,member⟩

theorem whereAccessible (registry : Registry) (_checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (_reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) root :=
  boundary_where_accessible registry state root

end Yulang.GeneralNominalCenteredAdministrativeWhere
