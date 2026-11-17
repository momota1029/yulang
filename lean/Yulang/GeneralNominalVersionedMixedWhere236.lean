import Yulang.GeneralNominalVersionedMixedSelectedFrame235
import Yulang.GeneralNominalCenteredWhere
set_option backward.isDefEq.respectTransparency false
/-! Actual selected-child accessibility. Finite registered parents and strictly
increasing versioned child identities suffice; no model availability premise. -/
namespace Yulang.GeneralNominalVersionedMixedWhere236
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedSourceBoundary234 (Local boundary)
open CommonRoleOutermostResolver (Child)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}

theorem child_above (packet : GeneralNominalSaturationState.Packet roles)
 (member : child ∈ GeneralNominalVersionedFrame231.children packet) :
 packet.site.occurrence.identity < child.identity := by
 have found : child.identity ∈ packet.children.map Occurrence.identity := by
   rw [← GeneralNominalVersionedFrame231.children_identity_eq]
   exact List.mem_map.mpr ⟨child,member,rfl⟩
 obtain ⟨old,member,same⟩ := List.mem_map.mp found
 rw [← same]
 exact GeneralNominalCenteredWhere.packet_child_above packet old member

def ceiling (state : State roles) : Nat :=
 (state.core.sites.map fun site => site.occurrence.identity).foldr max 0

def rank (state : State roles) (focus : Occurrence roles) : Nat := ceiling state + 1 - focus.identity

theorem selected_bounded (selected : Local registry state demand (.selected key children)) :
 demand.identity ≤ ceiling state := by
 obtain ⟨site,member,same⟩ := (GeneralNominalVersionedMixedSelectedFrame235.administrative_ready
   (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected)).1
 exact GeneralNominalCenteredWhere.member_max _ _ (List.mem_map.mpr ⟨site,member,congrArg Occurrence.identity same⟩)

theorem child_rank (path : B4TargetV8.Reachable (boundary roles) registry root state)
 (edge : Child (Local registry state) child parent) : rank state child < rank state parent := by
 obtain ⟨key,children,selected,member⟩ := edge
 obtain ⟨plan,frame,kids⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
 have above := child_above plan.packet (kids ▸ member)
 rw [frame.occurrence_eq] at above
 have bounded := selected_bounded selected
 unfold rank
 omega

theorem accessible (path : B4TargetV8.Reachable (boundary roles) registry root state)
 (demand : Occurrence roles) : Acc (Child (Local registry state)) demand := by
 have all : ∀ n, ∀ demand, rank state demand = n → Acc (Child (Local registry state)) demand := by
   intro n
   induction n using Nat.strongRecOn with
   | ind n ih =>
     intro demand same
     exact Acc.intro demand (fun child edge => ih _ (same ▸ child_rank path edge) child rfl)
 exact all _ demand rfl

/-- The literal whereAccessible field, with its hypotheses retained. -/
theorem whereAccessible : ∀ registry, (boundary roles).Checked registry → ∀ state root,
 B4TargetV8.Reachable (boundary roles) registry root state →
 Acc (Child (Local registry state)) root := by
 intro registry _ state root path
 exact accessible path root

end Yulang.GeneralNominalVersionedMixedWhere236
