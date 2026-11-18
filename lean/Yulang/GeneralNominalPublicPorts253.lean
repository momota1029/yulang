import Yulang.GeneralNominalOutputNames253
namespace Yulang.GeneralNominalPublicPorts253
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234 GeneralNominalVersionedInstall232
open GeneralNominalOwnerCandidates252

/-- A candidate wider basis: named outputs and emitted public clause ports.
Private aggregate slots (purposes 0 and 1) are not added. This definition does
not change the operational journal or assert its substitution closure. -/
def ports (seed parent : Nat) (declaration : Declaration) : List Nat :=
 (declaration.outputNames.map fun name => GeneralNominalIdentities.source seed
   (GeneralNominalAllocation.origin parent declaration.id 2 name 0)) ++
 declaration.requirements.flatMap fun clause =>
   ((List.range clause.arguments.length).flatMap fun index =>
     [GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration.id 3 clause.id index),
      GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration.id 4 clause.id index)]) ++
   clause.outputs.map fun equation => GeneralNominalIdentities.source seed
     (GeneralNominalAllocation.origin parent declaration.id 5 equation.id 0)

def names (registry : Registry) (seed : Nat) (keys : List (Nat × Nat)) : List Nat :=
 keys.flatMap fun key => registry.declarations.flatMap fun declaration =>
   if declaration.id = key.2 then ports seed key.1 declaration else []

theorem port_mem (registry : Registry) (seed parent : Nat) (keys : List (Nat × Nat))
 (declaration : Declaration) (owner : (parent,declaration.id) ∈ keys)
 (visible : declaration ∈ registry.declarations) (name : Nat) (member : name ∈ ports seed parent declaration) :
 name ∈ names registry seed keys := by
 apply List.mem_flatMap.mpr
 refine ⟨(parent,declaration.id),owner,?_⟩
 apply List.mem_flatMap.mpr
 exact ⟨declaration,visible,by simpa only [↓reduceIte] using member⟩

theorem output_mem (seed parent : Nat) (declaration : Declaration) (name : Nat)
 (member : name ∈ declaration.outputNames) :
 GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration.id 2 name 0) ∈ ports seed parent declaration :=
 List.mem_append_left _ (List.mem_map.mpr ⟨name,member,rfl⟩)

theorem argument_mem (seed parent : Nat) (declaration : Declaration) (clause : Clause)
 (member : clause ∈ declaration.requirements) (index : Nat) (bound : index < clause.arguments.length) :
 GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration.id 3 clause.id index) ∈ ports seed parent declaration ∧
 GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration.id 4 clause.id index) ∈ ports seed parent declaration := by
 constructor
 all_goals
   apply List.mem_append_right
   apply List.mem_flatMap.mpr
   refine ⟨clause,member,List.mem_append_left _ ?_⟩
   apply List.mem_flatMap.mpr
   exact ⟨index,List.mem_range.mpr bound,by simp⟩

theorem clause_output_mem (seed parent : Nat) (declaration : Declaration) (clause : Clause)
 (member : clause ∈ declaration.requirements) (equation : Equation) (found : equation ∈ clause.outputs) :
 GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration.id 5 equation.id 0) ∈ ports seed parent declaration := by
 apply List.mem_append_right
 apply List.mem_flatMap.mpr
 exact ⟨clause,member,List.mem_append_right _ (List.mem_map.mpr ⟨equation,found,rfl⟩)⟩


theorem port_purpose (seed parent : Nat) (declaration : Declaration) (name : Nat)
 (member : name ∈ ports seed parent declaration) :
 ∃ purpose owner position, 2 ≤ purpose ∧ purpose ≤ 5 ∧
 name = GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration.id purpose owner position) := by
 simp only [ports,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with ⟨binder,_,rfl⟩ | ⟨clause,_,(⟨index,_,rfl | rfl⟩ | ⟨equation,_,rfl⟩)⟩
 · exact ⟨2,binder,0,by decide,by decide,rfl⟩
 · exact ⟨3,clause.id,index,by decide,by decide,rfl⟩
 · exact ⟨4,clause.id,index,by decide,by decide,rfl⟩
 · exact ⟨5,equation.id,0,by decide,by decide,rfl⟩

/-- Enlarging this candidate basis with public ports does not add a versioned
private aggregate, regardless of that aggregate's binding history. -/
theorem aggregate_not_port (seed parent : Nat) (declaration : Declaration)
 (root key purpose binder : Nat) (bindings : GeneralNominalAllocation.Bindings) (privatePurpose : purpose ≤ 1) :
 GeneralNominalAggregateVersion231.slot seed root key purpose binder bindings ∉ ports seed parent declaration := by
 intro member
 obtain ⟨p,owner,position,lower,_,equal⟩ := port_purpose seed parent declaration _ member
 have same := (GeneralNominalIdentities.source_identity seed _ _).mp equal
 have purposes := congrArg (fun origin : GeneralNominalIdentities.Origin => origin.2.2.1) same
 change purpose = p at purposes
 omega

theorem aggregate_not_names (registry : Registry) (seed : Nat) (keys : List (Nat × Nat))
 (root key purpose binder : Nat) (bindings : GeneralNominalAllocation.Bindings) (privatePurpose : purpose ≤ 1) :
 GeneralNominalAggregateVersion231.slot seed root key purpose binder bindings ∉ names registry seed keys := by
 intro member
 obtain ⟨owner,_,found⟩ := List.mem_flatMap.mp member
 obtain ⟨declaration,_,found⟩ := List.mem_flatMap.mp found
 split at found
 · exact aggregate_not_port seed owner.1 declaration root key purpose binder bindings privatePurpose found
 · cases found

theorem installed_port_enumerated
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (enabled : Installable registry state effect) (novel : ¬ Committed state effect.plan)
 (name : Nat) (member : name ∈ ports effect.plan.packet.context.state.seed
   effect.plan.packet.site.occurrence.identity effect.plan.packet.declaration) :
 name ∈ names registry context.state.seed (owners registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass rootLabels)) := by
 have current := GeneralNominalVersionedMixedAncestry237.frame enabled
 have seed : effect.plan.packet.context.state.seed = context.state.seed := by
   rw [current.context_eq]
   exact (GeneralNominalVersionedMixedAncestry237.configuration_trace path).1
 rw [seed] at member
 exact port_mem registry _ _ _ _ (installed_owner_enumerated source point ground coverage path generated enabled novel) current.visible name member

theorem mixed_finite_ports (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ pool : List Nat, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state →
 ∀ effect,
 GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
 Installable (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) state effect →
 ¬ Committed state effect.plan → ∀ name ∈ ports effect.plan.packet.context.state.seed
   effect.plan.packet.site.occurrence.identity effect.plan.packet.declaration, name ∈ pool := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 refine ⟨names (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry)
   context.state.seed (owners (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry)
     context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels)),?_⟩
 intro state path effect generated enabled novel name member
 exact installed_port_enumerated formed point ground coverage path generated enabled novel name member
end Yulang.GeneralNominalPublicPorts253
