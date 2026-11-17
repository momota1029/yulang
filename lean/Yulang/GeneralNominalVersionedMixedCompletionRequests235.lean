import Yulang.GeneralNominalVersionedMixedTrace235
import Yulang.GeneralNominalCenteredHeadMatCompletionRequests
set_option backward.isDefEq.respectTransparency false
/-! Canonical child output identities survive versioned emission. On an actual
mixed source trace, installing children leaves every already-present class's
output requests unchanged, even when the new children have outputs. -/
namespace Yulang.GeneralNominalVersionedMixedCompletionRequests235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalCenteredHeadMatCompletionRequests (Formed Invariant Present outputs formed_above same_outputs alias_present)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {before after state : State roles}

set_option linter.unusedSimpArgs false in
theorem emitted_formed (valid : Invariant registry seed root state.core)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core
      plan.packet.site.occurrence plan.packet.declaration.id plan)
    (member : site ∈ GeneralNominalVersionedChildren232.emitted plan) :
    Formed registry seed root site.occurrence := by
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  refine Or.inr ⟨plan.packet.site.occurrence.identity,plan.packet.declaration,frame.visible,
    clause.val,visible,formed_above (valid.raw _ frame.raw_recorded),?_,?_⟩
  · change GeneralNominalIdentities.source plan.packet.context.state.seed _ = _
    rw [frame.context_eq,valid.seed_eq]
    rfl
  · change clause.val.outputs.map _ = _
    unfold outputs
    apply List.map_congr_left
    intro equation _
    congr 1
    unfold GeneralDeclarationDemands.outputTarget
    cases GeneralDeclarationPatterns.normalize equation.rhs <;>
      simp only [GeneralNominalVersionedFrame231.capture,GeneralNominalVersionedFrame231.frame,
        GeneralNominalVersionedAllocation231.capture,GeneralNominalAllocation.allocation,GeneralNominalAllocation.source,
        GeneralNominalAllocation.origin,frame.context_eq,valid.seed_eq]

theorem install (valid : Invariant registry seed root state.core)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core
      effect.plan.packet.site.occurrence effect.plan.packet.declaration.id effect.plan) :
    Invariant registry seed root (GeneralNominalVersionedInstall232.install state effect).core := by
  have present : ∀ identity, Present state.core identity →
      Present (GeneralNominalVersionedInstall232.install state effect).core identity := by
    rintro identity ⟨site,member,same⟩
    exact ⟨site,List.mem_append_left _ member,same⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro site member
    rcases List.mem_append.mp member with old | added
    · exact valid.raw site old
    · obtain ⟨center,present,rfl⟩ := List.mem_map.mp added
      exact emitted_formed valid frame present
  · intro site member
    exact (List.mem_append.mp member).elim (valid.centers site) (emitted_formed valid frame)
  · intro site member
    rcases List.mem_append.mp member with old | added
    · exact present _ (valid.registered site old)
    · exact ⟨site.observed,List.mem_append_right _ (List.mem_map.mpr ⟨site,added,rfl⟩),rfl⟩
  · intro pair member
    exact ⟨present _ (valid.aliases pair member).1,present _ (valid.aliases pair member).2⟩
  · change effect.plan.packet.context.state.seed = seed
    rw [frame.context_eq,valid.seed_eq]

theorem initial (context : GeneralNominalCandidates.Context) :
    Invariant registry context.state.seed root (GeneralNominalVersionedJournal232.initial context root).core := by
  refine ⟨?_,?_,?_,?_,rfl⟩
  · intro site member; cases List.mem_singleton.mp member; exact Or.inl rfl
  · intro site member; cases List.mem_singleton.mp member; exact Or.inl rfl
  · intro site member; cases List.mem_singleton.mp member; exact ⟨_,List.mem_singleton_self _,rfl⟩
  · intro pair member; cases member

theorem step (recorded : GeneralNominalVersionedMixedTrace235.Registered before root)
    (valid : Invariant registry seed root before.core)
    (action : Step registry root before after) : Invariant registry seed root after.core := by
  obtain ⟨focus,generated,action⟩ := action
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,present,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered recorded generated
      exact False.elim (absent site present same)
    | equate | reobserve => exact ⟨valid.raw,valid.centers,valid.registered,valid.aliases,valid.seed_eq⟩
    | refresh _ certificate _ _ _ _ =>
      exact ⟨valid.raw,valid.centers,valid.registered,valid.aliases,certificate.refines.seed.trans valid.seed_eq⟩
  | refresh _ _ certificate _ _ _ _ =>
    exact ⟨valid.raw,valid.centers,valid.registered,valid.aliases,certificate.refines.seed.trans valid.seed_eq⟩
  | merge first last one two same novel =>
    refine ⟨valid.raw,valid.centers,valid.registered,?_,valid.seed_eq⟩
    intro pair member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨valid.registered _ one,valid.registered _ two⟩
    · exact valid.aliases pair member
  | install effect enabled novel =>
    exact install valid (enabled.registry_eq ▸ enabled.snapshot_eq ▸ effect.frame)

theorem trace
    (path : B4Target.Steps (Step registry root) (GeneralNominalVersionedJournal232.initial context root) state) :
    Invariant registry context.state.seed root state.core := by
  induction path with
  | refl => exact initial context
  | tail path action ih =>
    exact step (GeneralNominalVersionedMixedTrace235.steps
      (GeneralNominalVersionedMixedTrace235.initial context) path).1 ih action

theorem reachable
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
    Invariant (GeneralNominalCenteredHeadAllocEncoding.registry registry)
      state.core.erased.source.state.seed root state.core := by
  obtain ⟨first,⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,path⟩ := path
  subst first
  subst legacy
  have result := trace path
  rw [GeneralNominalVersionedMixedGrowth234.steps_source path]
  exact result

theorem install_requests (checked : Checked registry) (valid : Invariant registry seed root state.core)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core
      plan.packet.site.occurrence plan.packet.declaration.id plan)
    (present : Present state.core focus.identity) (output) :
    output ∈ GeneralNominalCenteredHeadOutputs.requests (GeneralNominalVersionedInstall232.installCore state.core plan) focus ↔
      output ∈ GeneralNominalCenteredHeadOutputs.requests state.core focus := by
  constructor
  · intro member
    obtain ⟨site,member,alias,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
    have alias := GeneralNominalVersionedInstallProperties232.alias_iff.mp alias
    rcases List.mem_append.mp member with old | added
    · exact GeneralNominalCenteredHeadOutputs.mem_requests_iff.mpr ⟨site,old,alias,within⟩
    · obtain ⟨center,emittedMember,rfl⟩ := List.mem_map.mp added
      obtain ⟨old,recorded,same⟩ := alias_present valid alias present
      have requests := same_outputs checked (valid.raw _ recorded) (emitted_formed valid frame emittedMember) same
      exact GeneralNominalCenteredHeadOutputs.mem_requests_iff.mpr
        ⟨old,recorded,same.symm ▸ alias,requests.symm ▸ within⟩
  · exact GeneralNominalVersionedInstall232.requests_included state.core plan output

end Yulang.GeneralNominalVersionedMixedCompletionRequests235
