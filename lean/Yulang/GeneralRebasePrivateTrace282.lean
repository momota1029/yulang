import Yulang.GeneralRebasePrivateClass282

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
namespace Yulang.GeneralRebasePrivateTrace282
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split)
open GeneralNominalVersionedMixedGrowth234 (steps step steps_source)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralRebasePrivateKey282 (port Excludes different_purpose)
open GeneralRebasePrivateSchema282 (SiteSafe)
open GeneralRebasePrivateChild282 (child_site)
open GeneralRebasePrivatePacket282 (Safe)
open GeneralRebaseAggregateTags281 (Tag fixedOrigin)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {before after : State roles}

theorem root_site (ctx : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (linked : GeneralNominalState.Linked ctx.state root.demand) (low : ∀ n ∈ GeneralNominalState.sources ctx.state, n ≤ ctx.state.seed)
    (owner decl : Nat) (tag : Tag) :
    SiteSafe (rootSite ctx.state.seed root) (port ctx.state.seed owner decl tag) := by
  intro idx
  have large : ctx.state.seed < port ctx.state.seed owner decl tag := GeneralNominalIdentities.source_above_seed ctx.state.seed (fixedOrigin owner decl tag)
  have lo : port ctx.state.seed owner decl tag ≠ (root.demand.arguments idx).1 :=
    fun same => Nat.not_lt_of_ge (same.symm ▸ low _ (linked.1 idx).1) large
  have hi : port ctx.state.seed owner decl tag ≠ (root.demand.arguments idx).2 :=
    fun same => Nat.not_lt_of_ge (same.symm ▸ low _ (linked.1 idx).2) large
  refine ⟨lo,hi,?_⟩
  change _ ≠ (if (root.demand.arguments idx).1 = (root.demand.arguments idx).2 then
    (root.demand.arguments idx).1 else fresh ctx.state.seed root.identity 0 7 idx.val 0)
  split
  · exact lo
  · exact different_purpose tag (by decide : 2 ≤ 7)

theorem sites_safe (reached : Reachable registry root after) (owner decl : Nat) (tag : Tag) :
    ∀ site ∈ after.core.sites, SiteSafe site (port (raw after).seed owner decl tag) := by
  obtain ⟨start,init,path⟩ := reached
  induction path with
  | refl =>
    obtain ⟨legacy,⟨ctx,labels,formed,point,ground,covered,rfl⟩,rfl⟩ := init
    intro site used
    cases List.mem_singleton.mp used
    exact root_site ctx root formed.linked formed.below_seed owner decl tag
  | @tail prior current path action ih =>
    have old : Reachable registry root prior := ⟨start,init,path⟩
    have seed := (step action).seed
    rcases split old action with admin|⟨effect,enabled,_,rfl⟩
    · intro site used
      rw [GeneralNominalVersionedMixedAdministrative236.sites admin] at used
      exact seed.symm ▸ ih site used
    · intro site used
      change site ∈ prior.core.sites ++ GeneralNominalVersionedChildren232.emitted effect.plan at used
      have ctx : effect.plan.packet.context.state = raw prior := congrArg GeneralNominalCandidates.Context.state
        (effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) enabled.snapshot_eq))
      rcases List.mem_append.mp used with previous | next
      · exact seed.symm ▸ ih site previous
      · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp next
        have absent : Excludes effect.plan.packet owner decl tag := by
          unfold Excludes
          rw [ctx]
          exact GeneralRebaseFixedOrigin281.fixed_absent owner decl tag old
        have safe := child_site absent clause.val
          (effect.plan.packet.checked.signature.2.2.2 clause.val
            ((GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property))
        exact safe

theorem raw_outputs_safe (reached : Reachable registry root after) (owner decl : Nat) (tag : Tag)
    (site : GeneralNominalDemandMerging.Site roles) (listed : site ∈ after.core.erased.current.sites)
    (output : GeneralSourceState.Output) (used : output ∈ site.occurrence.demand.outputs) :
    port (raw after).seed owner decl tag ≠ output.target := by
  have all := (GeneralNominalVersionedMixedTrace235.reachable reached).2.2
  obtain ⟨center,present,same⟩ := all site listed
  have source := (GeneralRebaseMixedOwnedTrace277.adapter_reachable reached).outputs center present output (same.symm ▸ used)
  intro collision
  have absent : port (raw after).seed owner decl tag ∉ GeneralNominalState.sources (raw after) :=
    GeneralRebaseFixedOrigin281.fixed_absent owner decl tag reached
  exact absent (collision.symm ▸ source)

theorem frame_safe (reached : Reachable registry root after)
    {q : Plan roles} {r : Registry} {focus : Occurrence roles}
    (frame : GeneralNominalVersionedEvidence231.Frame r after.core focus key q)
    (owner decl : Nat) (tag : Tag) :
    Safe q owner decl tag := by
  have state : q.packet.context.state = raw after := congrArg GeneralNominalCandidates.Context.state frame.context_eq
  have seed := congrArg GeneralNominalState.State.seed state
  refine ⟨frame.registry_eq.symm ▸ frame.visible,?_,?_,?_⟩
  · unfold Excludes
    rw [state]
    exact GeneralRebaseFixedOrigin281.fixed_absent owner decl tag reached
  · exact seed.symm ▸ sites_safe reached owner decl tag q.input frame.center_recorded
  · intro out member
    rw [seed]
    exact raw_outputs_safe reached owner decl tag _ frame.raw_recorded out member

theorem historical (reached : Reachable registry root after) :
    (∀ p ∈ after.plans, ∃ e ∈ after.effects, e.plan = p) ∧
    ∀ e ∈ after.effects, ∃ prior, Reachable registry root prior ∧ e.snapshot = prior.core ∧ (raw prior).seed = (raw after).seed := by
  obtain ⟨start,init,path⟩ := reached
  induction path with
  | refl =>
    obtain ⟨legacy,_,rfl⟩ := init
    exact ⟨fun _ h => False.elim (List.not_mem_nil h),fun _ h => False.elim (List.not_mem_nil h)⟩
  | @tail prior current path action ih =>
    have saved : Reachable registry root prior := ⟨start,init,path⟩
    have seed := (step action).seed
    rcases split saved action with admin|⟨effect,enabled,_,rfl⟩
    · cases admin <;> exact ⟨ih.1,fun e member => by
          obtain ⟨w,reachable,eq,old⟩ := ih.2 e member
          exact ⟨w,reachable,eq,old.trans seed.symm⟩⟩
    · constructor
      · intro p listed
        rcases List.mem_cons.mp listed with rfl|prior
        · exact ⟨effect,List.mem_cons_self,rfl⟩
        · obtain ⟨e,member,same⟩ := ih.1 p prior
          exact ⟨e,List.mem_cons_of_mem _ member,same⟩
      · intro e listed
        rcases List.mem_cons.mp listed with rfl|earlier
        · exact ⟨prior,saved,enabled.snapshot_eq,seed.symm⟩
        · obtain ⟨w,reachable,eq,old⟩ := ih.2 e earlier
          exact ⟨w,reachable,eq,old.trans seed.symm⟩

end Yulang.GeneralRebasePrivateTrace282
