import Yulang.GeneralNominalRebaseChildrenUniverse243
namespace Yulang.GeneralNominalRebaseMergeSupport243
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalAllocationSupport GeneralNominalAllocation
open GeneralNominalRebaseChildProducer243 GeneralNominalRebaseChildrenUniverse243
open GeneralNominalRebaseStablePool243 (pool)

theorem candidate_outputs {roles : Roles.RoleDecls} {demand : GeneralSourceState.Demand roles}
 (visible : declaration ∈ registry.declarations) (required : clause ∈ declaration.requirements)
 (valid : clause.Signature roles) (present : demand ∈ candidates state registry invocation declaration clause valid values)
 (member : output ∈ demand.outputs) :
 output.target ∈ reserved state registry invocation := by
 obtain ⟨inputs,_,rfl⟩ := List.mem_map.mp present
 obtain ⟨equation,found,rfl⟩ := List.mem_map.mp member
 unfold GeneralDeclarationDemands.outputTarget
 split
 · split
   · rename_i name _ named
     exact reservation state _ (output_key visible named)
   · exact reservation state _ (clause_output_key visible required found)
 · exact reservation state _ (clause_output_key visible required found)

theorem child_outputs
 (checked : Checked registry)
 (present : child ∈ childrenPool registry checked initial root budget)
 (member : output ∈ child.demand.outputs) :
 output.target ∈ pool registry initial root budget := by
 obtain ⟨invocation,parent,rest⟩ := List.mem_flatMap.mp present
 obtain ⟨declaration,_,rest⟩ := List.mem_flatMap.mp rest
 obtain ⟨clause,_,rest⟩ := List.mem_flatMap.mp rest
 obtain ⟨demand,known,rfl⟩ := List.mem_map.mp rest
 exact GeneralNominalRebaseStablePool243.reserved_supported rfl parent
   (candidate_outputs declaration.property clause.property _ known member)

theorem output_atoms
 (first last : GeneralNominalDemandMerging.Site roles)
 (left : ∀ output ∈ first.occurrence.demand.outputs, output.target ∈ values)
 (right : ∀ output ∈ last.occurrence.demand.outputs, output.target ∈ values)
 (atom : PresenceNormalForm.Atom Nat)
 (present : atom ∈ GeneralNominalDemandMerging.outputAtoms first last) :
 GeneralNominalState.atomSources atom ⊆ values := by
 obtain ⟨one,found,rest⟩ := List.mem_flatMap.mp present
 obtain ⟨two,other,rest⟩ := List.mem_flatMap.mp rest
 split at rest
 · exact equation_sources _ _ (left one found)
     (fun _ h => by cases List.mem_singleton.mp h; exact right two other) atom rest
 · cases rest

theorem merge_children
 (checked : Checked registry)
 (path : B4Target.Steps (GeneralNominalRebaseSourceSteps243.Step registry initial root budget) initial.state state)
 (first last : GeneralNominalDemandMerging.Site registry.roles)
 (left : first.occurrence ∈ childrenPool registry checked initial root budget)
 (right : last.occurrence ∈ childrenPool registry checked initial root budget) :
 GeneralNominalState.sources (GeneralNominalState.extend state []
   (GeneralNominalDemandMerging.outputAtoms first last)) ⊆ pool registry initial root budget :=
 extend_sources state [] _ (GeneralNominalRebaseSourceSteps243.trace_supported path)
   (by intro _ h; cases h)
   (output_atoms first last (fun _ h => child_outputs checked left h)
     (fun _ h => child_outputs checked right h))
def sitesPool (registry : Registry) (checked : Checked registry)
 (initial : GeneralNominalCandidates.Context) (root : Occurrence registry.roles) (budget : Nat) :
 List (Occurrence registry.roles) := root :: childrenPool registry checked initial root.identity budget

theorem site_outputs
 (checked : Checked registry) (linked : GeneralNominalState.Linked initial.state root.demand)
 (present : site ∈ sitesPool registry checked initial root budget)
 (member : output ∈ site.demand.outputs) :
 output.target ∈ pool registry initial root.identity budget := by
 rcases List.mem_cons.mp present with rfl | child
 · exact GeneralNominalRebaseStablePool243.initial_supported (linked.2 output member)
 · exact child_outputs checked child member

theorem merge_sites
 (checked : Checked registry) (linked : GeneralNominalState.Linked initial.state root.demand)
 (path : B4Target.Steps (GeneralNominalRebaseSourceSteps243.Step registry initial root.identity budget) initial.state state)
 (first last : GeneralNominalDemandMerging.Site registry.roles)
 (left : first.occurrence ∈ sitesPool registry checked initial root budget)
 (right : last.occurrence ∈ sitesPool registry checked initial root budget) :
 GeneralNominalState.sources (GeneralNominalState.extend state []
   (GeneralNominalDemandMerging.outputAtoms first last)) ⊆ pool registry initial root.identity budget :=
 extend_sources state [] _ (GeneralNominalRebaseSourceSteps243.trace_supported path)
   (by intro _ h; cases h)
   (output_atoms first last (fun _ h => site_outputs checked linked left h)
     (fun _ h => site_outputs checked linked right h))
end Yulang.GeneralNominalRebaseMergeSupport243
