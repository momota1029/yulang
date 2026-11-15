import Yulang.GeneralDictionaryDefault214ActualReadback
import Yulang.GeneralNominalGeneratedSupport184
import Yulang.GeneralNominalSiteSeparation184

/-! Actual producers for corrected packet input, capture, and head-schema
support. High raw endpoint namespaces are excluded along the corrected trace. -/
namespace Yulang.GeneralDictionaryDefault214ActualSupport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound frame)
open GeneralDictionaryDefault214ActualReadback
open GeneralDictionaryDefault214ActualSites (initial_site_origin plan_seed)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalGeneratedSupport184 (Roots)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem registered_packets
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, plan.packet ∈ state.core.erased.current.packets := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      intro plan member
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih plan member)

theorem registered_input
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, plan.input ∈ state.core.sites := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      intro plan member
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_append_left _ (frame enabled).center_recorded
      · exact List.mem_append_left _ (ih plan member)

theorem registered_emitted
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, ∀ site ∈ plan.emitted, site ∈ state.core.sites := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      intro plan member site emitted
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_append_right _ emitted
      · exact List.mem_append_left _ (ih plan member site emitted)

theorem endpoint_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity) (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ≠
      (site.occurrence.demand.arguments index).1 ∧
    fresh context.state.seed invocation declaration purpose owner position ≠
      (site.occurrence.demand.arguments index).2 := by
  rcases initial_site_origin path site registered with rfl | ⟨plan,member,emitted⟩
  · have one := source.below_seed _ (source.linked.1 index).1
    have two := source.below_seed _ (source.linked.1 index).2
    have above := GeneralNominalIdentities.source_above_seed context.state.seed
      (invocation,declaration,purpose,owner,position)
    change context.state.seed < fresh context.state.seed invocation declaration purpose owner position at above
    change fresh context.state.seed invocation declaration purpose owner position ≠ (root.demand.arguments index).1 ∧
      fresh context.state.seed invocation declaration purpose owner position ≠ (root.demand.arguments index).2
    omega
  · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
    have seed := plan_seed path plan member
    have outside : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∉
        GeneralNominalState.sources plan.packet.context.state := by
      rw [seed]
      exact fun present => GeneralNominalCenteredAllocation.outside_pool source high
        (GeneralDictionaryDefaultRawSeparation213.packet_context_pool source bound path plan.packet
          (registered_packets path plan member) present)
    simpa only [Plan.childSite,seed] using GeneralNominalSiteSeparation184.clause_endpoints plan.packet clause.val
      (plan.packet.checked.signature.2.2.2 clause.val clause.property) high outside index

theorem site_support_actual
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (member : fresh context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalCenteredFrame179.siteSources site) :
    ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin := by
  obtain ⟨xs,present,within⟩ := List.mem_flatten.mp member
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at within
  rcases within with lower | upper | center
  · exact False.elim ((endpoint_separate source bound path site registered index (by omega)).1 lower)
  · exact False.elim ((endpoint_separate source bound path site registered index (by omega)).2 upper)
  · obtain ⟨origin,producer,_⟩ := uniform_site_readback source path site registered index center.symm
    exact ⟨origin,center.symm ▸ producer⟩

theorem capture_support_actual
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (member : fresh context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalCenteredFrame179.captureSources plan) :
    ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin := by
  obtain ⟨name,named,equal⟩ := GeneralDictionaryDefaultRawSeparation213.historical_capture_actual
    source bound path plan (registered_packets path plan registered) (by omega) member
  rw [← equal]
  exact registered_capture_actual path plan registered name
    ((GeneralNominalCenteredFrame179.capture_mem plan name).mp named)

theorem head_roots (plan : Plan roles) : Roots plan.headSchema (List.ofFn plan.input.center ++ [0]) := by
  apply GeneralNominalGeneratedSupport184.schemas_roots
  intro index
  cases found : (List.ofFn plan.input.center)[index]? with
  | none => simp [originSource]
  | some name =>
    have member : name ∈ List.ofFn plan.input.center := List.mem_of_getElem? found
    simp [originSource,member]

theorem center_list_actual
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (member : fresh context.state.seed invocation declaration 8 owner position ∈ List.ofFn site.center ++ [0]) :
    ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin := by
  rcases List.mem_append.mp member with member | member
  · obtain ⟨index,equal⟩ := List.mem_ofFn.mp member
    obtain ⟨origin,producer,_⟩ := uniform_site_readback source path site registered index equal
    exact ⟨origin,equal ▸ producer⟩
  · have zero := List.mem_singleton.mp member
    have positive := GeneralNominalIdentities.source_above_seed context.state.seed
      (invocation,declaration,8,owner,position)
    change _ < fresh context.state.seed invocation declaration 8 owner position at positive
    omega

theorem head_support_actual
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (member : fresh context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeFrame181.schemaSources plan plan.headSchema) :
    ∃ origin, Actual state (fresh context.state.seed invocation declaration 8 owner position) origin := by
  have capture := GeneralDictionaryDefaultRawSeparation213.historical_capture_separate
    (invocation := invocation) (declaration := declaration) (owner := owner) (position := position)
    source bound path plan.packet (registered_packets path plan registered) (by decide : 7 ≤ 8)
  rcases List.mem_append.mp member with test | usePart
  · obtain ⟨entry,present,equal⟩ := List.mem_map.mp test
    exact center_list_actual source path plan.input (registered_input path plan registered)
      (equal ▸ (head_roots plan).1 entry present)
  · obtain ⟨entry,present,within⟩ := List.mem_flatMap.mp usePart
    by_cases actual : entry.mode = .actual
    · simp only [GeneralNominalModeFrame181.variableSources,actual,ite_true,List.mem_cons,List.not_mem_nil,or_false] at within
      rcases within with origin | binder
      · exact center_list_actual source path plan.input (registered_input path plan registered)
          (origin.symm ▸ (head_roots plan).2 entry present)
      · exact ⟨entry.origin,plan,registered,entry,present,actual,binder.symm,rfl⟩
    · simp only [GeneralNominalModeFrame181.variableSources,actual,ite_false,List.mem_cons,List.not_mem_nil,or_false] at within
      rcases within with origin | output | lower | upper
      · exact center_list_actual source path plan.input (registered_input path plan registered)
          (origin.symm ▸ (head_roots plan).2 entry present)
      · exact False.elim ((capture entry.name).1 output)
      · exact False.elim ((capture entry.name).2.1 lower)
      · exact False.elim ((capture entry.name).2.2 upper)

end Yulang.GeneralDictionaryDefault214ActualSupport
