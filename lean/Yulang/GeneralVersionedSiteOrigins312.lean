import Yulang.GeneralNominalVersionedMixedAncestry237
import Yulang.GeneralNominalVersionedMixedSeedLedger237
import Yulang.GeneralNominalVersionedMixedChoiceHistory236
import Yulang.GeneralNominalVersionedMixedPlanLedger235
import Yulang.GeneralNominalVersionedCurrentProjection237

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionedSiteOrigins312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models initial Effect)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedChildren232 (emitted)
open GeneralNominalVersionedFrame231 (childSite)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalRecursiveInspection (Finished)
open GeneralNominalQueryProvenance183 (headInspection)

variable {roles : Roles.RoleDecls}

theorem child_above (p : Plan roles) (clause : Clause) (signature : clause.Signature roles) :
    p.packet.site.occurrence.identity < (childSite p clause signature).occurrence.identity := by
  change p.packet.site.occurrence.identity < GeneralNominalIdentities.source p.packet.context.state.seed
    (GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id 6 clause.id 0)
  exact GeneralNominalIdentities.source_above_invocation p.packet.context.state.seed
    (GeneralNominalAllocation.origin p.packet.site.occurrence.identity p.packet.declaration.id 6 clause.id 0)

theorem emitted_origin {p : Plan roles} {site : Site roles} (seen : site ∈ emitted p) :
    ∃ clause ∈ p.packet.declaration.requirements, ∃ signature : clause.Signature roles,
      site = childSite p clause signature := by
  obtain ⟨item,_,rfl⟩ := List.mem_map.mp seen
  exact ⟨item.val,(GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr item.property,_,rfl⟩

theorem emitted_above {p : Plan roles} {site : Site roles} (seen : site ∈ emitted p) :
    p.packet.site.occurrence.identity < site.occurrence.identity := by
  obtain ⟨clause,_,sig,rfl⟩ := emitted_origin seen
  exact child_above p clause sig

structure TraceData (root : Occurrence roles) (ctx : GeneralNominalCandidates.Context) (state : State roles) : Prop where
  origin : ∀ site ∈ state.core.sites, site = rootSite ctx.state.seed root ∨
    ∃ prior ∈ state.plans, site ∈ emitted prior
  root_le : ∀ site ∈ state.core.sites, root.identity ≤ site.occurrence.identity
  input : ∀ plan ∈ state.plans, plan.input ∈ state.core.sites
  configuration : ∀ plan ∈ state.plans, plan.packet.context.state.seed = ctx.state.seed ∧
    plan.packet.context.state.constructors = ctx.state.constructors ∧
    plan.packet.context.interpretation = ctx.interpretation

theorem initial_data (root : Occurrence roles) (ctx : GeneralNominalCandidates.Context) :
    TraceData root ctx (initial ctx root) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro site seen
    exact Or.inl (List.mem_singleton.mp seen)
  · intro site seen
    cases List.mem_singleton.mp seen
    exact Nat.le_refl _
  · intro p seen; cases seen
  · intro p seen; cases seen

theorem trace (path : B4Target.Steps (Step registry root) (initial ctx root) state) :
    TraceData root ctx state := by
  induction path with
  | refl => exact initial_data _ _
  | @tail before after prior action ih =>
    have prev := GeneralNominalVersionedMixedAncestry237.configuration_trace prior
    have growth := GeneralNominalVersionedMixedGrowth234.step action
    obtain ⟨focus,generated,action⟩ := action
    cases action with
    | administrative action =>
      cases action with
      | enqueue _ absent =>
        obtain ⟨site,present,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
          (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial ctx) prior).1 generated
        exact False.elim (absent site present same)
      | refresh | reobserve | equate => exact ⟨ih.origin,ih.root_le,ih.input,ih.configuration⟩
    | refresh | merge => exact ⟨ih.origin,ih.root_le,ih.input,ih.configuration⟩
    | install e enabled _ =>
      have frame := GeneralNominalVersionedMixedAncestry237.frame enabled
      refine ⟨?_,?_,?_,?_⟩
      · intro site present
        rcases List.mem_append.mp present with old|new
        · rcases ih.origin site old with rootCase|⟨plan,found,production⟩
          · exact Or.inl rootCase
          · exact Or.inr ⟨plan,List.mem_cons_of_mem _ found,production⟩
        · exact Or.inr ⟨e.plan,List.mem_cons_self,new⟩
      · intro site present
        rcases List.mem_append.mp present with old|new
        · exact ih.root_le site old
        · have parent := ih.root_le e.plan.input frame.center_recorded
          rw [e.plan.input_exact] at parent
          exact Nat.le_trans parent (Nat.le_of_lt (emitted_above new))
      · intro p found
        rcases List.mem_cons.mp found with rfl|old
        · exact growth.legacy.sites frame.center_recorded
        · exact growth.legacy.sites (ih.input p old)
      · intro p found
        rcases List.mem_cons.mp found with rfl|old
        · rw [frame.context_eq]
          exact prev
        · exact ih.configuration p old

theorem reached
    (path : B4TargetV8.Reachable (boundary roles) registry root state) :
    ∃ ctx, TraceData root ctx state := by
  obtain ⟨first,⟨legacy,⟨ctx,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,steps⟩ := path
  subst first
  subst legacy
  exact ⟨ctx,trace steps⟩

theorem stored_current_config
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (present : plan ∈ state.plans) :
    plan.packet.context.state.seed = state.core.erased.current.context.state.seed ∧
    plan.packet.context.state.constructors = state.core.erased.current.context.state.constructors ∧
    plan.packet.context.interpretation = state.core.erased.current.context.interpretation := by
  obtain ⟨first,⟨legacy,⟨ctx,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,steps⟩ := path
  subst first
  subst legacy
  have own := (trace steps).configuration plan present
  have now := GeneralNominalVersionedMixedAncestry237.configuration_trace steps
  exact ⟨own.1.trans now.1.symm,own.2.1.trans now.2.1.symm,own.2.2.trans now.2.2.symm⟩

theorem stored_effect
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (present : plan ∈ state.plans) :
    ∃ effect ∈ state.effects, effect.plan = plan := by
  rw [(GeneralNominalVersionedMixedPlanLedger235.reachable path).1] at present
  exact List.mem_map.mp present

theorem stored_finished
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (present : plan ∈ state.plans) : Finished (headInspection plan) := by
  obtain ⟨e,_,rfl⟩ := stored_effect path present
  have prior := e.frame.prepared
  rw [← e.frame.context_eq] at prior
  obtain ⟨_,_,bounds,found,_,finished,_⟩ := prior
  have equal : bounds = e.plan.packet.bounds := Option.some.inj (found.symm.trans e.frame.located)
  subst bounds
  exact GeneralNominalInspectionAlignment.finished_origins e.plan.packet.context.state _ e.plan.packet.bounds _ _ 0 0 finished

theorem stored_visible
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (present : plan ∈ state.plans) :
    plan.packet.declaration ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations := by
  obtain ⟨e,seen,rfl⟩ := stored_effect path present
  exact ((GeneralNominalVersionedMixedRegistry234.reachable path).2.2 e seen) ▸ e.frame.visible

end Yulang.GeneralVersionedSiteOrigins312
