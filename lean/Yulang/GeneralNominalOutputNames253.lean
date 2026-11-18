import Yulang.GeneralNominalSourceOwnerCandidates252
namespace Yulang.GeneralNominalOutputNames253
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234 GeneralNominalVersionedInstall232
open GeneralNominalOwnerCandidates252

/-- Opaque public output references, not their ground expansions. -/
def outputs (registry : Registry) (seed : Nat) (keys : List (Nat × Nat)) : List Nat :=
 keys.flatMap fun key => registry.declarations.flatMap fun declaration =>
   if declaration.id = key.2 then declaration.outputNames.map fun name =>
     GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin key.1 declaration.id 2 name 0)
   else []

theorem output_mem (registry : Registry) (seed parent : Nat) (keys : List (Nat × Nat))
 (declaration : Declaration) (owner : (parent,declaration.id) ∈ keys)
 (visible : declaration ∈ registry.declarations) (name : Nat) (named : name ∈ declaration.outputNames) :
 GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration.id 2 name 0) ∈ outputs registry seed keys := by
 apply List.mem_flatMap.mpr
 refine ⟨(parent,declaration.id),owner,?_⟩
 apply List.mem_flatMap.mpr
 refine ⟨declaration,visible,?_⟩
 simp only [↓reduceIte]
 exact List.mem_map.mpr ⟨name,named,rfl⟩

/-- Actual reachable installations use the finite names supplied by their
source-derived owner list. No ground-depth hypothesis is introduced. -/
theorem installed_output_enumerated
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (enabled : Installable registry state effect) (novel : ¬ Committed state effect.plan)
 (name : Nat) (named : name ∈ effect.plan.packet.declaration.outputNames) :
 (GeneralNominalVersionedFrame231.capture effect.plan.packet).outputs name ∈
 outputs registry context.state.seed (owners registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass rootLabels)) := by
 have owner := installed_owner_enumerated source point ground coverage path generated enabled novel
 have current := GeneralNominalVersionedMixedAncestry237.frame enabled
 have seed : effect.plan.packet.context.state.seed = context.state.seed := by
   rw [current.context_eq]
   exact (GeneralNominalVersionedMixedAncestry237.configuration_trace path).1
 change GeneralNominalIdentities.source effect.plan.packet.context.state.seed
   (GeneralNominalAllocation.origin effect.plan.packet.site.occurrence.identity effect.plan.packet.declaration.id 2 name 0) ∈ _
 rw [seed]
 exact output_mem registry _ _ _ _ owner current.visible name named

/-- One finite list covers all named public outputs of every future actual
mixed-source installation. It does not claim private-slot substitution closure. -/
theorem mixed_finite_outputs (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ names : List Nat, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state →
 ∀ effect,
 GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
 Installable (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) state effect →
 ¬ Committed state effect.plan → ∀ name ∈ effect.plan.packet.declaration.outputNames,
 (GeneralNominalVersionedFrame231.capture effect.plan.packet).outputs name ∈ names := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 refine ⟨outputs (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry)
   context.state.seed (owners (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry)
     context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels)),?_⟩
 intro state path effect generated enabled novel name named
 exact installed_output_enumerated formed point ground coverage path generated enabled novel name named

theorem point_finite_outputs (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalPointSourceBoundary240.boundary roles).Initial sourceRegistry root start) :
 ∃ names : List Nat, ∀ state,
 B4Target.Steps ((GeneralNominalPointSourceBoundary240.boundary roles).Step sourceRegistry root) start state →
 ∀ effect,
 GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
 Installable (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) state effect →
 ¬ Committed state effect.plan → ∀ name ∈ effect.plan.packet.declaration.outputNames,
 (GeneralNominalVersionedFrame231.capture effect.plan.packet).outputs name ∈ names := by
 obtain ⟨names,finite⟩ := mixed_finite_outputs sourceRegistry root start source
 refine ⟨names,?_⟩
 intro state path effect generated enabled novel name named
 exact finite state (GeneralNominalPointErasure240.steps_old path) effect generated enabled novel name named
end Yulang.GeneralNominalOutputNames253
