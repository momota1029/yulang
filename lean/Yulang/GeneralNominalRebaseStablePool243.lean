import Yulang.GeneralNominalRebaseOwnerIndex242
import Yulang.GeneralNominalAllocationSupport
namespace Yulang.GeneralNominalRebaseStablePool243
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseInstall242
open GeneralNominalInvocationAncestry (frontier allocationPool)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : Journal.State roles}

def pool (registry : Registry) (context : GeneralNominalCandidates.Context) (root limit : Nat) : List Nat :=
 GeneralNominalState.sources context.state ++ allocationPool registry context.state.seed
   (frontier registry context.state.seed root limit)

theorem initial_supported : GeneralNominalState.sources context.state ⊆ pool registry context rootIdentity limit :=
 fun _ member => List.mem_append_left _ member

theorem reserved_supported
 (same : snapshot.seed = context.state.seed)
 (parent : invocation ∈ frontier registry context.state.seed rootIdentity limit) :
 GeneralNominalAllocation.reserved snapshot registry invocation ⊆ pool registry context rootIdentity limit := by
 intro identity member
 unfold GeneralNominalAllocation.reserved at member
 obtain ⟨key,keyMember,rfl⟩ := List.mem_map.mp member
 apply List.mem_append_right
 change GeneralNominalIdentities.source snapshot.seed key ∈ _
 rw [same]
 exact GeneralNominalInvocationAncestry.allocation_member invocation parent key keyMember

theorem generated_identity
 (metadata : registry.constructors = context.state.constructors)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (covered : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (GeneralNominalPointKernel240.Step registry root)
   (GeneralNominalVersionedJournal232.initial context root) state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus) :
 focus.identity ∈ frontier registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels) := by
 have old := GeneralNominalPointErasure240.steps_old path
 have invariant := GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) old
 obtain ⟨raw,present,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered invariant.1 generated
 obtain ⟨center,member,equal⟩ := invariant.2.2 raw present
 have included := GeneralNominalRebaseBirthWitness242.trace_enumerated metadata point ground covered old center member
 have identity := congrArg Occurrence.identity (equal.trans same)
 simpa only [identity] using included

theorem generated_reserved
 (metadata : registry.constructors = context.state.constructors)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (covered : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (GeneralNominalPointKernel240.Step registry root)
   (GeneralNominalVersionedJournal232.initial context root) state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus) :
 GeneralNominalAllocation.reserved state.core.erased.current.context.state registry focus.identity ⊆
 pool registry context root.identity (GeneralNominalPatersonLineage.mass labels) :=
 reserved_supported (GeneralNominalVersionedMixedGrowth234.steps (GeneralNominalPointErasure240.steps_old path)).seed
   (generated_identity metadata point ground covered path generated)

end Yulang.GeneralNominalRebaseStablePool243
