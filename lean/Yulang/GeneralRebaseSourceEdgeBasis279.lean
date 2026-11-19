import Yulang.GeneralRebaseFiniteProbeObstruction279
import Yulang.GeneralNominalSourceOwnerCandidates252

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseSourceEdgeBasis279
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Step At Installable Committed)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalInvocationAncestry (successors)
open GeneralNominalVersionedInstall232 (install)
open GeneralRebaseInstallNovelty279 (Edge)

def project (edge : Edge roles) : Nat × Nat := (edge.1.identity,edge.2.identity)

def candidateEdges (r : Registry) (seed : Nat) (owners : List (Nat × Nat)) : List (Nat × Nat) :=
  owners.flatMap fun entry => (successors r seed entry.1).map fun child => (entry.1,child)

theorem emitted_project (r : Registry) (seed : Nat) (owners : List (Nat × Nat)) (p : Plan roles)
    (owner : (p.packet.site.occurrence.identity,p.packet.declaration.id) ∈ owners)
    (visible : p.packet.declaration ∈ r.declarations)
    (same : p.packet.context.state.seed = seed) (edge : Edge roles)
    (written : edge ∈ GeneralNominalVersionedChildren232.edges p) :
    project edge ∈ candidateEdges r seed owners := by
  obtain ⟨child,chosen,rfl⟩ := GeneralNominalVersionedChildren232.edge_iff.mp written
  obtain ⟨site,atSite,isChild⟩ := GeneralNominalVersionedChildren232.emitted_child_iff.mp chosen
  obtain ⟨clause,mem,rfl⟩ := List.mem_map.mp atSite
  subst child
  apply List.mem_flatMap.mpr
  refine ⟨_,owner,List.mem_map.mpr ⟨_,?_,rfl⟩⟩
  apply List.mem_flatMap.mpr
  refine ⟨p.packet.declaration,visible,List.mem_map.mpr ⟨clause.val,
    (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property,?_⟩⟩
  change GeneralNominalIdentities.source seed
      (GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id 6 clause.val.id 0) =
    GeneralNominalIdentities.source p.packet.context.state.seed
      (GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id 6 clause.val.id 0)
  rw [same]

theorem initial_edges (source : (boundary roles).Initial r root start) :
    start.core.erased.current.edges = [] := by
  obtain ⟨_,⟨_,_,_,_,_,_,rfl⟩,rfl⟩ := source
  rfl

theorem finite_projected_edges (source : (boundary roles).Initial r root start) :
    ∃ pool : List (Nat × Nat), ∀ state,
      B4Target.Steps ((boundary roles).Step r root) start state →
      ∀ edge ∈ state.core.erased.current.edges, project edge ∈ pool := by
  obtain ⟨owners,finite⟩ := GeneralNominalSourceOwnerCandidates252.mixed_finite_owners r root start source
  refine ⟨candidateEdges (registry r) start.core.erased.current.context.state.seed owners,?_⟩
  intro final walk
  induction walk with
  | refl =>
    intro edge member
    rw [initial_edges source] at member
    exact False.elim (List.not_mem_nil member)
  | tail path step ih =>
    have seed := (GeneralNominalVersionedMixedAncestry237.configuration_trace path).1
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative admin => cases admin <;> exact ih
    | refresh => exact ih
    | merge => exact ih
    | install effect enabled novel =>
      intro edge member
      rcases List.mem_append.mp member with old | fresh
      · exact ih edge old
      · have framed := GeneralNominalVersionedMixedAncestry237.frame enabled
        have owner := finite _ path effect generated enabled novel
        have effectSeed := (congrArg (fun context => context.state.seed) framed.context_eq).trans seed
        exact emitted_project _ _ _ _ owner framed.visible effectSeed edge fresh

end Yulang.GeneralRebaseSourceEdgeBasis279
