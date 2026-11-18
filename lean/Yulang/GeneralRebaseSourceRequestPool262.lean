import Yulang.GeneralRebaseChildRequestPool262
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSourceRequestPool262
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralSourceState (Output)
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedInstall232
open GeneralRebaseChildRequestPool262

/-- One candidate list includes initial request targets and public ports of
future installations. It is not a list of only currently emitted requests. -/
def pool (registry : Registry) (root : Occurrence roles) (targets : List Nat) : List Output :=
 product (GeneralNominalOutputMenu254.names registry root)
   (root.demand.outputs.map Output.target ++ targets)

/-- The explicit future-port premise is discharged from actual source formation
below. No absorption into the current alias classes is required. -/
theorem trace_covered (registry : Registry) (root : Occurrence roles)
 (context : GeneralNominalCandidates.Context) (targets : List Nat)
 (finite : ∀ state, B4Target.Steps (Step registry root) (initial context root) state →
   ∀ effect,
   GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
   Installable registry state effect → ¬ Committed state effect.plan →
   ∀ name ∈ GeneralNominalPublicPorts253.ports effect.plan.packet.context.state.seed
     effect.plan.packet.site.occurrence.identity effect.plan.packet.declaration, name ∈ targets)
 (state : State roles) (path : B4Target.Steps (Step registry root) (initial context root) state) :
 Covered state.core (pool registry root targets) := by
 induction path with
 | refl =>
   intro site member output requested
   cases List.mem_singleton.mp member
   apply (mem_product _ _ output).mpr
   exact ⟨List.mem_append_left _ (List.mem_map.mpr ⟨output,requested,rfl⟩),
     List.mem_append_left _ (List.mem_map.mpr ⟨output,requested,rfl⟩)⟩
 | @tail before after path step ih =>
   obtain ⟨focus,generated,action⟩ := step
   cases action with
   | administrative action =>
     cases action with
     | enqueue linked absent =>
       obtain ⟨site,member,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
         (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).1 generated
       exact False.elim (absent site member same)
     | refresh | equate | reobserve => exact ih
   | refresh | merge => exact ih
   | install effect enabled novel =>
     intro site member output requested
     change site ∈ before.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites effect.plan at member
     rcases List.mem_append.mp member with old | added
     · exact ih site old output requested
     · apply (mem_product _ _ output).mpr
       refine ⟨raw_name registry root effect.plan
         (GeneralNominalVersionedMixedAncestry237.frame enabled).visible site added output requested,?_⟩
       exact List.mem_append_right _ (finite before path effect generated enabled novel output.target
         (raw_target effect.plan site added output requested))

/-- Actual source formation provides one fixed candidate Output list for every
snapshot of the mixed source trace. This is a coverage theorem feeding rebase,
not termination or a simulation theorem for that old source Step. -/
theorem mixed_finite_requests (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ candidates : List Output, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state →
 Covered state.core candidates := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 let registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry
 let targets := GeneralNominalPublicPorts253.names registry context.state.seed
   (GeneralNominalOwnerCandidates252.owners registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels))
 refine ⟨pool registry root targets,?_⟩
 intro state path
 apply trace_covered registry root context targets _ state path
 intro state path effect generated enabled novel name member
 exact GeneralNominalPublicPorts253.installed_port_enumerated formed point ground coverage path generated enabled novel name member

theorem all_requests (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ candidates : List Output, ∀ state,
 B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state →
 ∀ queriedRoot output, output ∈ GeneralNominalCenteredHeadOutputs.requests state.core queriedRoot → output ∈ candidates := by
 obtain ⟨candidates,covered⟩ := mixed_finite_requests sourceRegistry root start source
 exact ⟨candidates,fun state path queriedRoot output requested => requests_covered state.core candidates
   (covered state path) queriedRoot output requested⟩
end Yulang.GeneralRebaseSourceRequestPool262
