import Yulang.GeneralNominalOutputMenu254
namespace Yulang.GeneralNominalProducerRank254
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalInvocationAncestry (frontier)
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {state : State roles}

/-- Number of remaining candidate identities, retaining duplicates in the
enumeration. This is a bound by list length, not by allocator numeric size. -/
def rank : List Nat → Nat → Nat
 | [],_ => 0
 | first :: rest,parent => (if parent ≤ first then 1 else 0) + rank rest parent

theorem monotone (names : List Nat) (le : parent ≤ child) : rank names child ≤ rank names parent := by
 induction names with
 | nil => exact Nat.le_refl _
 | cons first rest ih =>
   simp only [rank]
   split <;> split <;> omega

theorem strict (names : List Nat) (member : parent ∈ names) (lt : parent < child) :
 rank names child < rank names parent := by
 induction names with
 | nil => cases member
 | cons first rest ih =>
   rcases List.mem_cons.mp member with rfl | member
   · have tail := monotone rest (Nat.le_of_lt lt)
     simp only [rank,Nat.le_refl,ite_true]
     have notBelow : ¬ child ≤ parent := by omega
     simp only [notBelow,ite_false]; omega
   · have smaller := ih member
     simp only [rank]
     split <;> split <;> omega

theorem length_bound (names : List Nat) (parent : Nat) : rank names parent ≤ names.length := by
 induction names with
 | nil => exact Nat.le_refl _
 | cons first rest ih =>
   simp only [rank,List.length_cons]
   split <;> omega

theorem positive (member : parent ∈ names) : 0 < rank names parent := by
 have below := strict names member (Nat.lt_succ_self parent)
 omega

def pool (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) (rootLabels : List GeneralDeclarationPatterns.Pattern) : List Nat :=
 frontier registry context.state.seed root.identity (mass rootLabels)

theorem frame_member
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (valid : Models state model)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan) :
 focus.identity ∈ pool registry context root rootLabels := by
 have member := GeneralNominalOwnerCandidates252.modeled_sites_enumerated source point ground coverage path valid plan.input frame.center_recorded
 simpa only [pool,plan.input_exact,frame.occurrence_eq] using member

theorem edge_rank
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (valid : Models state model)
 (edge : GeneralNominalProducerOrder254.Edge registry state.core child parent) :
 rank (pool registry context root rootLabels) child < rank (pool registry context root rootLabels) parent := by
 have above := GeneralNominalProducerOrder254.edge_above edge
 obtain ⟨plan,focus,key,frame,rfl,_⟩ := edge
 exact strict _ (frame_member source point ground coverage path valid frame) above

theorem pool_length :
 (pool registry context root rootLabels).length =
 (1 + GeneralNominalOwnerCandidates252.branching registry) ^ mass rootLabels :=
 GeneralNominalOwnerCandidates252.frontier_count registry context.state.seed root.identity (mass rootLabels)
end Yulang.GeneralNominalProducerRank254
