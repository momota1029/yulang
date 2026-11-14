import Yulang.GeneralNominalCenteredAllocation
import Yulang.GeneralNominalCenteredHeadWFBoundary
import Yulang.GeneralNominalCenteredHeadStepEnumeration

/-! Actual path induction recovers a registered producer for every emitted
centered site. Purpose-eight site centers come from a bare child binder. -/
namespace Yulang.GeneralNominalHeadSiteOrigin185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepTrace

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem site_origin (path : B4Target.Steps (Step registry root) before after) :
    ∀ site ∈ after.core.sites, site ∈ before.core.sites ∨ ∃ plan ∈ after.core.plans, site ∈ plan.emitted := by
  induction path with
  | refl => exact fun _ member => Or.inl member
  | @tail previous next path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative focus next action => exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro site member
      rcases List.mem_append.mp member with old | new
      · rcases ih site old with initial | ⟨oldPlan,registered,emitted⟩
        · exact Or.inl initial
        · exact Or.inr ⟨oldPlan,List.mem_cons_of_mem _ registered,emitted⟩
      · exact Or.inr ⟨plan,List.mem_cons_self ..,new⟩

theorem initial_site_origin
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (member : site ∈ state.core.sites) :
    site = rootSite context.state.seed root ∨ ∃ plan ∈ state.core.plans, site ∈ plan.emitted := by
  rcases site_origin path site member with initial | emitted
  · exact Or.inl (List.mem_singleton.mp initial)
  · exact Or.inr emitted

theorem plan_seed
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, plan.packet.context.state.seed = context.state.seed := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative focus after action => exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro old member
      rcases List.mem_cons.mp member with rfl | retained
      · exact (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) enabled.frame.context_eq).trans
          (configuration_trace path).1
      · exact ih old retained

 theorem root_not_eight
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (index : Fin (roles root.demand.role).arity) :
    (rootSite context.state.seed root).center index ≠
      fresh context.state.seed invocation declaration 8 owner position := by
  by_cases point : (root.demand.arguments index).1 = (root.demand.arguments index).2
  · rw [point_center _ _ _ point]
    have below := source.below_seed _ (source.linked.1 index).1
    have above := GeneralNominalIdentities.source_above_seed context.state.seed
      (invocation,declaration,8,owner,position)
    change context.state.seed < fresh context.state.seed invocation declaration 8 owner position at above
    omega
  · simp only [rootSite,point,ite_false]
    exact GeneralNominalCenteredAllocation.fresh_namespaces (by decide : 7 ≠ 8)

/-- A producer rather than a schema-coverage assumption: it is obtained from
actual registrations and the disjoint allocation namespaces. -/
theorem purpose_eight_site_binder
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh context.state.seed invocation declaration 8 owner position) :
    ∃ plan ∈ state.core.plans, ∃ name, plan.binder name = site.center index := by
  rcases initial_site_origin path site member with rfl | ⟨plan,registered,emitted⟩
  · exact False.elim (root_not_eight source index center)
  · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
    let signature := plan.packet.checked.signature.2.2.2 clause.val clause.property
    let pattern := clause.val.arguments[index.val]'(by rw [signature.1]; exact index.isLt)
    have center' : plan.emittedCenter clause.val.id index.val pattern =
        fresh context.state.seed invocation declaration 8 owner position := center
    cases normalized : GeneralDeclarationPatterns.normalize pattern with
    | var name =>
      refine ⟨plan,registered,name,?_⟩
      change plan.binder name = plan.emittedCenter clause.val.id index.val pattern
      simp [Plan.emittedCenter,normalized]
    | _ =>
      have impossible : fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity
          plan.packet.declaration.id 9 clause.val.id index.val =
          fresh context.state.seed invocation declaration 8 owner position := by
        simpa only [Plan.emittedCenter,normalized] using center'
      rw [plan_seed path plan registered] at impossible
      exact False.elim (GeneralNominalCenteredAllocation.fresh_namespaces (by decide : 9 ≠ 8) impossible)

theorem purpose_eight_site_needed
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh context.state.seed invocation declaration 8 owner position) :
    ∃ plan ∈ state.core.plans, ∃ name, GeneralNominalSharedCaptures.Needed plan.packet name ∧ plan.binder name = site.center index := by
  rcases initial_site_origin path site member with rfl | ⟨plan,registered,emitted⟩
  · exact False.elim (root_not_eight source index center)
  · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
    let signature := plan.packet.checked.signature.2.2.2 clause.val clause.property
    let pattern := clause.val.arguments[index.val]'(by rw [signature.1]; exact index.isLt)
    have center' : plan.emittedCenter clause.val.id index.val pattern =
        fresh context.state.seed invocation declaration 8 owner position := center
    cases normalized : GeneralDeclarationPatterns.normalize pattern with
    | var name =>
      refine ⟨plan,registered,name,?_,?_⟩
      · refine ⟨clause.val,clause.property,?_⟩
        have patternMember : pattern ∈ clause.val.arguments := List.getElem_mem ..
        have normalMember : GeneralDeclarationPatterns.normalize pattern ∈
            GeneralDeclarationPatterns.normalizeArgs clause.val.arguments := by
          rw [GeneralNominalChildAssembly.normalize_map]
          exact List.mem_map.mpr ⟨pattern,patternMember,rfl⟩
        exact GeneralNominalCanonicalTemplates.argument_variables _ _ normalMember
          (by simp [normalized,GeneralDeclarationPatterns.Pattern.variables])
      · change plan.binder name = plan.emittedCenter clause.val.id index.val pattern
        simp [Plan.emittedCenter,normalized]
    | _ =>
      have impossible : fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity
          plan.packet.declaration.id 9 clause.val.id index.val =
          fresh context.state.seed invocation declaration 8 owner position := by
        simpa only [Plan.emittedCenter,normalized] using center'
      rw [plan_seed path plan registered] at impossible
      exact False.elim (GeneralNominalCenteredAllocation.fresh_namespaces (by decide : 9 ≠ 8) impossible)


theorem purpose_eight_site_fits
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh context.state.seed invocation declaration 8 owner position)
    (valid : Models state model) :
    ∃ plan ∈ state.core.plans, ∃ name, GeneralNominalSharedCaptures.Needed plan.packet name ∧
      plan.binder name = site.center index ∧
      GeneralNominalCaptureMerges.Fits model
        ((GeneralNominalPacketSupport.capture plan.packet).inputs name) (model (site.center index)).1 := by
  obtain ⟨plan,registered,name,needed,equal⟩ := purpose_eight_site_needed source path site member index center
  refine ⟨plan,registered,name,needed,equal,?_⟩
  rw [← equal]
  exact (valid.1.2.2 plan registered).2.1 name (Or.inr needed)

end Yulang.GeneralNominalHeadSiteOrigin185
