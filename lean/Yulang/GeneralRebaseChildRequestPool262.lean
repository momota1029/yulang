import Yulang.GeneralNominalPublicPorts253
import Yulang.GeneralNominalOutputMenu254
import Yulang.GeneralRebaseSourceSnapshot261
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseChildRequestPool262
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralSourceState (Output)
open GeneralNominalVersionedFrame231 (clauseChild)

/-- Actual child output targets use public purpose2 or purpose5 slots. This
statement is about identities, not ground readback or packet correctness. -/
theorem equation_target (packet : GeneralNominalSaturationState.Packet roles)
 (clause : Clause) (present : clause ∈ packet.declaration.requirements)
 (equation : Equation) (member : equation ∈ clause.outputs) :
 GeneralDeclarationDemands.outputTarget packet.declaration
   (GeneralNominalVersionedFrame231.capture packet)
   ((GeneralNominalVersionedFrame231.frame packet).allocation packet.declaration.id clause).outputs equation ∈
 GeneralNominalPublicPorts253.ports packet.context.state.seed packet.site.occurrence.identity packet.declaration := by
 unfold GeneralDeclarationDemands.outputTarget
 cases normalized : GeneralDeclarationPatterns.normalize equation.rhs with
 | var name =>
   by_cases named : name ∈ packet.declaration.outputNames
   · simp only [named,ite_true]
     exact GeneralNominalPublicPorts253.output_mem _ _ _ name named
   · simp only [named,ite_false]
     exact GeneralNominalPublicPorts253.clause_output_mem _ _ _ clause present equation member
 | _ => exact GeneralNominalPublicPorts253.clause_output_mem _ _ _ clause present equation member

theorem clause_target (packet : GeneralNominalSaturationState.Packet roles)
 (clause : Clause) (present : clause ∈ packet.declaration.requirements)
 (signature : clause.Signature roles) (output : Output)
 (requested : output ∈ (clauseChild packet clause signature).demand.outputs) :
 output.target ∈ GeneralNominalPublicPorts253.ports packet.context.state.seed
   packet.site.occurrence.identity packet.declaration := by
 obtain ⟨equation,member,rfl⟩ := List.mem_map.mp requested
 exact equation_target packet clause present equation member

theorem emitted_target (plan : Plan roles) (site : Site roles)
 (member : site ∈ GeneralNominalVersionedChildren232.emitted plan)
 (output : Output) (requested : output ∈ site.occurrence.demand.outputs) :
 output.target ∈ GeneralNominalPublicPorts253.ports plan.packet.context.state.seed
   plan.packet.site.occurrence.identity plan.packet.declaration := by
 obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
 exact clause_target plan.packet clause.val
   ((GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property) _ output requested

theorem raw_target (plan : Plan roles) (site : GeneralNominalDemandMerging.Site roles)
 (member : site ∈ GeneralNominalVersionedChildren232.rawSites plan)
 (output : Output) (requested : output ∈ site.occurrence.demand.outputs) :
 output.target ∈ GeneralNominalPublicPorts253.ports plan.packet.context.state.seed
   plan.packet.site.occurrence.identity plan.packet.declaration := by
 obtain ⟨center,included,rfl⟩ := List.mem_map.mp member
 exact emitted_target plan center included output requested

theorem raw_name (registry : Registry) (root : Occurrence roles) (plan : Plan roles)
 (visible : plan.packet.declaration ∈ registry.declarations)
 (site : GeneralNominalDemandMerging.Site roles)
 (member : site ∈ GeneralNominalVersionedChildren232.rawSites plan)
 (output : Output) (requested : output ∈ site.occurrence.demand.outputs) :
 output.name ∈ GeneralNominalOutputMenu254.names registry root := by
 obtain ⟨center,included,rfl⟩ := List.mem_map.mp member
 obtain ⟨clause,_,rfl⟩ := List.mem_map.mp included
 exact GeneralNominalOutputMenu254.child_name plan.packet visible
   ((GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property) _ output requested

/-- Cartesian overapproximation of request identities. Not every pair need
occur; names and targets must both be justified by the caller. -/
def product (names targets : List Nat) : List Output :=
 names.flatMap fun name => targets.map fun target => ⟨name,target⟩

theorem mem_product (names targets : List Nat) (output : Output) :
 output ∈ product names targets ↔ output.name ∈ names ∧ output.target ∈ targets := by
 constructor
 · intro member
   obtain ⟨name,named,found⟩ := List.mem_flatMap.mp member
   obtain ⟨target,targeted,same⟩ := List.mem_map.mp found
   cases same
   exact ⟨named,targeted⟩
 · rintro ⟨named,targeted⟩
   exact List.mem_flatMap.mpr ⟨output.name,named,List.mem_map.mpr ⟨output.target,targeted,by cases output; rfl⟩⟩

def Covered (source : GeneralNominalCenteredSteps.State roles) (pool : List Output) : Prop :=
 ∀ site ∈ source.erased.current.sites, ∀ output ∈ site.occurrence.demand.outputs, output ∈ pool

theorem requests_covered (source : GeneralNominalCenteredSteps.State roles) (pool : List Output)
 (covered : Covered source pool) (root : Occurrence roles) (output : Output)
 (requested : output ∈ GeneralNominalCenteredHeadOutputs.requests source root) : output ∈ pool := by
 obtain ⟨site,member,_,found⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp requested
 exact covered site member output found

theorem snapshot_product (source : GeneralNominalCenteredSteps.State roles) (names targets : List Nat)
 (named : ∀ site ∈ source.erased.current.sites, ∀ output ∈ site.occurrence.demand.outputs, output.name ∈ names)
 (targeted : ∀ site ∈ source.erased.current.sites, ∀ output ∈ site.occurrence.demand.outputs, output.target ∈ targets) :
 Covered source (product names targets) := by
 intro site member output requested
 exact (mem_product names targets output).mpr ⟨named site member output requested,targeted site member output requested⟩

end Yulang.GeneralRebaseChildRequestPool262
