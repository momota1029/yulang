import Yulang.GeneralRebaseAggregateTags281
import Yulang.GeneralRebaseQuietBound277
import Yulang.GeneralRebaseOwnedSupport277

set_option maxRecDepth 28000
namespace Yulang.GeneralRebaseFixedOrigin281
open GeneralNominalIdentities (Origin source source_identity source_above_seed)
open GeneralNominalAllocation (origin)
open GeneralNominalAggregateVersion231 (key not_legacy)
open GeneralRebaseAggregateTags281 (Tag fixedOrigin fixed)
open GeneralNominalVersionedAllocation231 (declarationKeys keys)
open GeneralNominalSaturationState (Packet)

theorem not_declarationKey (oldParent oldDecl : Nat) (t : Tag) (root : Nat)
    (d : GeneralDeclarations.Declaration) (bindings : GeneralNominalAllocation.Bindings) :
    fixedOrigin oldParent oldDecl t ∉ declarationKeys root d bindings := by
  intro member
  simp only [declarationKeys,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_cons,List.mem_nil_iff,
    or_false] at member
  rcases member with (⟨name,_,same | same⟩ | ⟨name,_,same⟩) | ⟨clause,_,(same | branches) | outputs⟩
  · exact not_legacy root d.id 0 name bindings oldParent oldDecl _ t.binder same.symm
  · exact not_legacy root d.id 1 name bindings oldParent oldDecl _ t.binder same.symm
  all_goals
    first
    | obtain ⟨arg,_,same | same⟩ := branches
      all_goals
        have impossible := congrArg (fun k : Origin => k.2.2.1) same
        cases h : t.upper <;> simp [fixedOrigin,origin,h] at impossible
    | obtain ⟨eqn,_,same⟩ := outputs
      have impossible := congrArg (fun k : Origin => k.2.2.1) same
      cases h : t.upper <;> simp [fixedOrigin,origin,h] at impossible
    | have impossible := congrArg (fun k : Origin => k.2.2.1) same
      cases h : t.upper <;> simp [fixedOrigin,origin,h] at impossible

theorem not_reserved (p : Packet roles) (owner decl : Nat) (tag : Tag) :
    source p.context.state.seed (fixedOrigin owner decl tag) ∉
      GeneralNominalVersionedInstallation231.reserved p := by
  intro member
  obtain ⟨k,inKeys,same⟩ := List.mem_map.mp member
  have identity := (source_identity _ _ _).mp same
  subst k
  obtain ⟨d,_,member⟩ := List.mem_flatMap.mp inKeys
  exact not_declarationKey owner decl tag _ d _ member

open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseMixedOwnedTrace277 (raw adapter_reachable)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split)

theorem fixed_absent {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {after : State roles} (owner decl : Nat) (tag : Tag)
    (path : Reachable registry root after) :
    source (raw after).seed (fixedOrigin owner decl tag) ∉ GeneralNominalState.sources (raw after) := by
  obtain ⟨start,formation,steps⟩ := path
  induction steps with
  | refl =>
    obtain ⟨legacy,⟨ctx,labels,sourceInit,point,ground,coverage,rfl⟩,rfl⟩ := formation
    intro member
    exact Nat.not_lt_of_ge (sourceInit.below_seed _ member) (source_above_seed _ _)
  | @tail before after tail action ih =>
    have reached : Reachable registry root before := ⟨start,formation,tail⟩
    rcases split reached action with admin | ⟨effect,enabled,_,rfl⟩
    · have seed : (raw after).seed = (raw before).seed := by
        cases admin with
        | refresh context cert => exact cert.refines.seed
        | reobserve | equate | merge => rfl
      rw [seed]
      exact fun member => ih (GeneralRebaseQuietBound277.admin_same_sources
        (adapter_reachable reached) admin _ |>.mpr member)
    · have ctx : effect.plan.packet.context.state = raw before := congrArg GeneralNominalCandidates.Context.state
        (effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) enabled.snapshot_eq))
      have visible : effect.plan.packet.declaration ∈ effect.plan.packet.registry.declarations :=
        effect.frame.registry_eq.symm ▸ effect.frame.visible
      change source effect.plan.packet.context.state.seed (fixedOrigin owner decl tag) ∉
        GeneralNominalState.sources (GeneralNominalVersionedInstallation231.replayPlan effect.plan).packet.context.state
      intro member
      rcases List.mem_append.mp (GeneralRebaseOwnedSupport277.replay_support effect.plan visible member) with old | added
      · rw [ctx] at old
        exact ih old
      · exact not_reserved effect.plan.packet owner decl tag added

end Yulang.GeneralRebaseFixedOrigin281
