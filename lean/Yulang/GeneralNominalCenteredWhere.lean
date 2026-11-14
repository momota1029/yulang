import Yulang.GeneralNominalCenteredSelection

/-! At a stable reachable snapshot, finite registration and increasing emitted
identities give where accessibility once selected plans are available. The
availability premise remains a source-compilation obligation. -/
namespace Yulang.GeneralNominalCenteredWhere
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredBoundary (Local Installable boundary)
open GeneralNominalCenteredTrace GeneralNominalCenteredSelection
open GeneralNominalSaturationState (Packet Generated)
open CommonRoleOutermostResolver (Child)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def Available (registry : Registry) (state : State roles) (focus : Occurrence roles) : Prop :=
  ∀ key children, Local registry state focus (.selected key children) →
    ∃ plan : Plan roles, plan.packet.site.occurrence = focus ∧ Installable registry state plan

theorem packet_child_above (packet : Packet roles) (child : Occurrence roles) (member : child ∈ packet.children) :
    packet.site.occurrence.identity < child.identity := by
  obtain ⟨clause,_,signature,rfl⟩ := GeneralNominalPatersonLineage.emitted_clause packet child member
  exact GeneralNominalIdentities.source_above_invocation packet.context.state.seed
    (GeneralNominalAllocation.origin packet.site.occurrence.identity packet.declaration.id 6 clause.id 0)

theorem member_max (values : List Nat) (value : Nat) (member : value ∈ values) : value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

def ceiling (state : State roles) : Nat := (state.erased.current.sites.map fun site => site.occurrence.identity).foldr max 0

def rank (state : State roles) (focus : Occurrence roles) : Nat := ceiling state + 1 - focus.identity

theorem generated_bounded
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : Generated state.erased.current root focus) : focus.identity ≤ ceiling state := by
  obtain ⟨site,member,same⟩ := generated_registered path generated
  exact member_max _ _ (List.mem_map.mpr ⟨site,member,congrArg Occurrence.identity same⟩)

theorem generated_children
    (stable : Stable registry state root)
    (available : ∀ focus, Generated state.erased.current root focus → Available registry state focus)
    (generated : Generated state.erased.current root focus)
    (selected : Local registry state focus (.selected key children)) :
    ∀ child ∈ children, Generated state.erased.current root child := by
  obtain ⟨plan,same,enabled⟩ := available focus generated key children selected
  exact guarded_selected_children
    (fun demand reached => stable demand (GeneralNominalSaturationState.generated_trans generated reached))
    selected plan same enabled generated

theorem local_where_accessible
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (stable : Stable registry state root)
    (available : ∀ focus, Generated state.erased.current root focus → Available registry state focus)
    (generated : Generated state.erased.current root focus) : Acc (Child (Local registry state)) focus := by
  have all : ∀ n, ∀ focus, rank state focus = n → Generated state.erased.current root focus →
      Acc (Child (Local registry state)) focus := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro focus equal generated
      refine Acc.intro focus ?_
      rintro child ⟨key,children,selected,member⟩
      obtain ⟨plan,same,enabled⟩ := available focus generated key children selected
      have chosen := GeneralNominalCenteredBoundary.installable_selected enabled
      rw [same] at chosen
      have identity := GeneralNominalCenteredBoundary.local_functional chosen selected
      have kids : plan.packet.children = children := by cases identity; rfl
      have above := packet_child_above plan.packet child (kids ▸ member)
      rw [same] at above
      have bounded := generated_bounded path generated
      have smaller : rank state child < rank state focus := by unfold rank; omega
      exact ih _ (equal ▸ smaller) child rfl (generated_children stable available generated selected child member)
  exact all _ focus rfl generated

theorem whereAccessible
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (stable : Stable registry state root)
    (available : ∀ focus, Generated state.erased.current root focus → Available registry state focus) :
    Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) root := by
  have all := local_where_accessible path stable available (focus := root) Generated.root
  clear path stable available
  induction all with
  | intro parent below ih =>
    refine Acc.intro parent ?_
    rintro child ⟨key,children,selected,member⟩
    exact ih child ⟨key,children,
      (GeneralNominalCenteredBoundary.local_correspondence registry state parent _).mp selected,member⟩

end Yulang.GeneralNominalCenteredWhere
