import Yulang.GeneralRebaseOwnedSupport277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseMixedOwnedTrace277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect initial)
open GeneralNominalVersionedMixedKernel234 (Step At Administrative Installable)
open GeneralNominalVersionedInstallation231 (replayPlan reserved)
open GeneralNominalState (sources)
open GeneralRebaseOwnedSupport277 (Covered)

variable {roles : Roles.RoleDecls} {before after start : State roles} {root focus : Occurrence roles}

abbrev raw (s : State roles) := s.core.erased.current.context.state

structure Invariant (s : State roles) : Prop where
  owns : Covered (raw s)
  outputs : ∀ site ∈ s.core.sites, ∀ output ∈ site.occurrence.demand.outputs,
    output.target ∈ sources (raw s)

theorem initial_invariant (ctx : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (covered : Covered ctx.state) (link : GeneralNominalState.Linked ctx.state root.demand) :
    Invariant (initial ctx root) := by
  refine ⟨covered,?_⟩
  intro site member output present
  cases List.mem_singleton.mp member
  exact link.2 output present

theorem source_extend (s : GeneralNominalState.State) (new : List Nat)
    (atoms : List (PresenceNormalForm.Atom Nat)) :
    sources s ⊆ sources (GeneralNominalState.extend s new atoms) := by
  intro id prior
  simp only [sources,GeneralNominalState.extend,List.flatMap_append,List.mem_append] at prior ⊢
  rcases prior with ((type|row)|reserved)|atom
  · exact Or.inl (Or.inl (Or.inl type))
  · exact Or.inl (Or.inl (Or.inr row))
  · exact Or.inl (Or.inr (Or.inl reserved))
  · exact Or.inr (Or.inl atom)

theorem reserved_extend (s : GeneralNominalState.State) {new : List Nat}
    (atoms : List (PresenceNormalForm.Atom Nat)) :
    new ⊆ sources (GeneralNominalState.extend s new atoms) := by
  intro id member
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ member))

theorem emitted_output (p : Plan roles) (visible : p.packet.declaration ∈ p.packet.registry.declarations)
    (site : Site roles) (emitted : site ∈ GeneralNominalVersionedChildren232.emitted p)
    (output : GeneralSourceState.Output) (request : output ∈ site.occurrence.demand.outputs) :
    output.target ∈ reserved p.packet := by
  obtain ⟨clause,present,rfl⟩ := List.mem_map.mp emitted
  have member := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  let allocate := ((GeneralNominalVersionedFrame231.frame p.packet).allocation p.packet.declaration.id clause.val).outputs
  change output ∈ clause.val.outputs.map (fun eq =>
    ⟨eq.name,GeneralDeclarationDemands.outputTarget p.packet.declaration
     (GeneralNominalVersionedFrame231.capture p.packet) allocate eq⟩) at request
  obtain ⟨eq,listed,rfl⟩ := List.mem_map.mp request
  have clauseKey : GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id 5 eq.id 0
      ∈ GeneralNominalVersionedAllocation231.keys p.packet.registry p.packet.site.occurrence.identity p.packet.bindings :=
    List.mem_flatMap.mpr ⟨_,visible,List.mem_append_right _
      (List.mem_flatMap.mpr ⟨clause.val,member,List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_map.mpr ⟨eq,listed,rfl⟩))⟩)⟩
  change GeneralDeclarationDemands.outputTarget _ _ _ _ ∈ reserved p.packet
  unfold GeneralDeclarationDemands.outputTarget
  split
  · split
    · rename_i name normalized names
      have outputKey : GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id 2 name 0
          ∈ GeneralNominalVersionedAllocation231.keys p.packet.registry p.packet.site.occurrence.identity p.packet.bindings :=
        List.mem_flatMap.mpr ⟨_,visible,List.mem_append_left _
          (List.mem_append_right _ (List.mem_map.mpr ⟨name,names,rfl⟩))⟩
      exact List.mem_map.mpr ⟨_,outputKey,rfl⟩
    · exact List.mem_map.mpr ⟨_,clauseKey,rfl⟩
  · exact List.mem_map.mpr ⟨_,clauseKey,rfl⟩

theorem install (old : Invariant before) (e : Effect roles)
    (snapshot : e.snapshot = before.core) :
    Invariant (GeneralNominalVersionedInstall232.install before e) := by
  have ctx : e.plan.packet.context = before.core.erased.current.context :=
    e.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snapshot)
  have same : e.plan.packet.context.state = raw before := congrArg GeneralNominalCandidates.Context.state ctx
  have visible : e.plan.packet.declaration ∈ e.plan.packet.registry.declarations := e.frame.registry_eq.symm ▸ e.frame.visible
  refine ⟨GeneralRebaseOwnedSupport277.replay_owned e.plan visible (same.symm ▸ old.owns),?_⟩
  intro site member output request
  change site ∈ before.core.sites ++ GeneralNominalVersionedChildren232.emitted e.plan at member
  rcases List.mem_append.mp member with prior|emitted
  · have named := old.outputs site prior output request
    change output.target ∈ sources (GeneralDictionaryOrdinaryTransport.extendState e.plan.packet.context.state
      (reserved e.plan.packet) (GeneralNominalVersionedInstallation231.atoms e.plan.packet)
      (GeneralNominalVersionedInstallation231.allocated e.plan.packet))
    exact source_extend _ _ _ (same.symm ▸ named)
  · have named := emitted_output e.plan visible site emitted output request
    change output.target ∈ sources (GeneralDictionaryOrdinaryTransport.extendState e.plan.packet.context.state
      (reserved e.plan.packet) (GeneralNominalVersionedInstallation231.atoms e.plan.packet)
      (GeneralNominalVersionedInstallation231.allocated e.plan.packet))
    exact reserved_extend _ _ named

theorem administrative (old : Invariant before) (action : Administrative before focus after) :
    Invariant after := by
  cases action with
  | enqueue link absent => exact ⟨old.owns,old.outputs⟩
  | refresh ctx cert id tracked unknown known =>
    refine ⟨GeneralRebaseOwnedSupport277.certified_refinement cert.refines cert.support old.owns,?_⟩
    exact fun site member output request =>
      GeneralNominalRefinements.sources cert.refines _ (old.outputs site member output request)
  | equate first last one two equal novel =>
    refine ⟨fun id member => old.owns id (GeneralNominalCenteredHeadMatStepEnumeration.equate_sources one two member),?_⟩
    exact fun site member output request => source_extend _ _ _ (old.outputs site member output request)
  | reobserve revision cert improves => exact ⟨old.owns,old.outputs⟩

theorem merge (old : Invariant before) {a b : Site roles} (one : a ∈ before.core.sites)
    (two : b ∈ before.core.sites) :
    Invariant (GeneralNominalVersionedAdministrative232.merge before a b) := by
  refine ⟨?_,?_⟩
  · intro id member
    have introA : ∀ output ∈ a.observed.occurrence.demand.outputs, output.target ∈ sources (raw before) :=
      old.outputs a one
    have introB : ∀ output ∈ b.observed.occurrence.demand.outputs, output.target ∈ sources (raw before) :=
      old.outputs b two
    exact old.owns id (GeneralNominalCenteredEnumeration.merge_sources (before := before.core.erased.current)
      (fun _ h => h) introA introB member)
  · exact fun site member output request => source_extend _ _ _ (old.outputs site member output request)

theorem step (old : Invariant before) (action : Step registry root before after) : Invariant after := by
  obtain ⟨focus,reached,action⟩ := action
  cases action with
  | administrative action => exact administrative old action
  | refresh focus ctx cert id tracked unknown known =>
    exact administrative old (.refresh focus ctx cert id tracked unknown known)
  | install effect enabled novel => exact install old effect enabled.snapshot_eq
  | merge a b first last same novel => exact merge old first last

theorem trace (old : Invariant start) (path : B4Target.Steps (Step registry root) start after) :
    Invariant after := by
  induction path with
  | refl => exact old
  | tail path action ih => exact step ih action

theorem all_fresh (old : Invariant start) (path : B4Target.Steps (Step registry root) start after) :
    ∀ reg id bs, GeneralNominalVersionedAllocation231.Fresh (raw after) reg id bs :=
  GeneralRebaseOwnedSupport277.allFresh (trace old path).owns

theorem initial_boundary
    (formed : GeneralNominalVersionedMixedBoundary234.Initial registry root start) :
    Invariant start := by
  obtain ⟨old,⟨ctx,labels,source,point,ground,coverage,rfl⟩,rfl⟩ := formed
  exact initial_invariant ctx root (fun id member => Or.inl (source.below_seed id member)) source.linked

theorem boundary_reachable (path : B4TargetV8.Reachable
    (GeneralNominalVersionedMixedBoundary234.boundary roles) registry root after) :
    Invariant after := by
  obtain ⟨start,formation,steps⟩ := path
  exact trace (initial_boundary formation) steps

theorem adapter_reachable (path : B4TargetV8.Reachable
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root after) :
    Invariant after :=
  boundary_reachable (GeneralNominalVersionedMixedSourceBoundary234.reachable_compiled path)

theorem adapter_all_fresh (path : B4TargetV8.Reachable
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root after) :
    ∀ reg id bs, GeneralNominalVersionedAllocation231.Fresh (raw after) reg id bs :=
  GeneralRebaseOwnedSupport277.allFresh (adapter_reachable path).owns

end Yulang.GeneralRebaseMixedOwnedTrace277
