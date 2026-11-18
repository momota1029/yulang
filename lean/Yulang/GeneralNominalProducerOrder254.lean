import Yulang.GeneralNominalSourceReadback254
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalProducerOrder254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalInvocationAncestry (successors frontier AtDepth)
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {state : State roles}

/-- Static candidate-frame child-call edges at one source snapshot. This
is not the scheduler Step, alias relation or arbitrary equation dependency. -/
def Edge (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
 (child parent : Nat) : Prop :=
 ∃ (plan : Plan roles) (focus : Occurrence roles) (key : Nat),
 GeneralNominalVersionedEvidence231.Frame registry state focus key plan ∧
 parent = focus.identity ∧ ∃ occurrence ∈ GeneralNominalVersionedFrame231.children plan.packet,
 child = occurrence.identity

theorem child_successor (packet : GeneralNominalSaturationState.Packet roles)
 (visible : packet.declaration ∈ packet.registry.declarations)
 (member : occurrence ∈ GeneralNominalVersionedFrame231.children packet) :
 occurrence.identity ∈ successors packet.registry packet.context.state.seed packet.site.occurrence.identity := by
 obtain ⟨emission,present,rfl⟩ := List.mem_map.mp member
 have old := (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity
   packet.declaration packet.checked _ _).mem_iff.mpr present
 obtain ⟨clause,_,same⟩ := List.mem_map.mp old
 cases same
 exact List.mem_flatMap.mpr ⟨packet.declaration,visible,List.mem_map.mpr ⟨clause.val,clause.property,rfl⟩⟩

theorem successor_above (member : child ∈ successors registry seed parent) : parent < child := by
 obtain ⟨declaration,_,clauseMember⟩ := List.mem_flatMap.mp member
 obtain ⟨clause,_,rfl⟩ := List.mem_map.mp clauseMember
 exact GeneralNominalIdentities.source_above_invocation seed (GeneralNominalAllocation.origin parent declaration.id 6 clause.id 0)

theorem edge_above (edge : Edge registry core child parent) : parent < child := by
 obtain ⟨plan,focus,key,frame,rfl,occurrence,member,rfl⟩ := edge
 have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := frame.registry_eq ▸ frame.visible
 have above := successor_above (child_successor plan.packet visible member)
 simpa only [frame.occurrence_eq] using above

theorem no_self_edge : ¬ Edge registry core name name := fun edge => Nat.lt_irrefl _ (edge_above edge)

def ceiling (names : List Nat) : Nat := names.foldr max 0

theorem below_ceiling (member : name ∈ names) : name ≤ ceiling names := by
 induction names with
 | nil => cases member
 | cons first rest ih =>
   rcases List.mem_cons.mp member with rfl | member
   · exact Nat.le_max_left _ _
   · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem source_edge_bounded
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (valid : Models state model)
 (edge : Edge registry state.core child parent) :
 child ≤ ceiling (frontier registry context.state.seed root.identity (mass rootLabels + 1)) := by
 obtain ⟨plan,focus,key,frame,_,occurrence,member,rfl⟩ := edge
 obtain ⟨level,labels,ancestry,_,bound⟩ :=
   GeneralNominalVersionedMixedAncestry237.sites_bounded source point ground coverage path model valid plan.input frame.center_recorded
 have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := frame.registry_eq ▸ frame.visible
 have successor := child_successor plan.packet visible member
 have seed : state.core.erased.current.context.state.seed = context.state.seed :=
   (GeneralNominalVersionedMixedAncestry237.configuration_trace path).1
 rw [plan.input_exact] at ancestry
 rw [frame.registry_eq,frame.context_eq,seed] at successor
 have childAncestry := AtDepth.child ancestry successor
 exact below_ceiling (GeneralNominalInvocationAncestry.bounded_enumerated childAncestry (by omega))

theorem bounded_accessible
 (bound : ∀ child parent, Edge registry core child parent → child ≤ limit)
 (parent : Nat) : Acc (Edge registry core) parent := by
 generalize measure : limit + 1 - parent = n
 induction n using Nat.strongRecOn generalizing parent with
 | ind n ih =>
   apply Acc.intro
   intro child edge
   have above := edge_above edge
   have below := bound child parent edge
   apply ih (limit + 1 - child) (by omega) child rfl

/-- A source-derived well-founded order for the static child-producer graph.
It excludes recursive producer calls but does not exclude repeated scheduler
refreshes, alias cycles or installation of an unchanged fact. -/
theorem source_wellFounded
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (valid : Models state model) : WellFounded (Edge registry state.core) :=
 ⟨bounded_accessible (fun _ _ edge => source_edge_bounded source point ground coverage path valid edge)⟩

end Yulang.GeneralNominalProducerOrder254
