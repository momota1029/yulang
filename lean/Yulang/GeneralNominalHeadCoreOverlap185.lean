import Yulang.GeneralNominalHeadCoreCoverage185
import Yulang.GeneralNominalHeadRawSeparation185
import Yulang.GeneralNominalHeadCandidateReadback185
import Yulang.GeneralNominalHeadCoreCoverage185

/-! Purpose-eight full-support overlap has a registered actual-origin producer.
This classifies historical support, not agreement of an arbitrary new origin. -/
namespace Yulang.GeneralNominalHeadCoreOverlap185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalRecursiveInspection
open GeneralNominalMaterialization
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalSupportProvenance182
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalGeneratedSupport184 (Roots)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem registered_packets
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, plan.packet ∈ state.core.erased.current.packets := by
  induction path with
  | refl => intro plan impossible; cases impossible
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro previous member
      rcases List.mem_cons.mp member with rfl | old
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih previous old)

theorem capture_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      (GeneralNominalPacketSupport.capture packet).outputs name ∧
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2 := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  have seed := GeneralNominalHeadPacketSupport185.packet_seed path packet member
  have bound := GeneralNominalCenteredHeadStepAncestry.installed_depth_bound (registry := registry) point ground
  have outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state := by
    rw [seed]
    exact fun present => GeneralNominalCenteredAllocation.outside_pool source high
      (GeneralNominalHeadPacketSupport185.packet_context_pool source bound path packet member present)
  rw [(GeneralNominalCenteredHeadStepTrace.configuration_trace path).1]
  simpa only [seed, GeneralNominalCenteredHeadStepEffects.initial, GeneralNominalCenteredSteps.initial, GeneralNominalCenteredSteps.initialAt, GeneralNominalSupport.initial, GeneralNominalSaturationState.initial] using And.intro (GeneralNominalRawSupport183.capture_output_separate packet high name)
    (GeneralNominalRawSupport183.capture_inputs_separate packet high outside name)

theorem site_endpoint_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity) (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      (site.occurrence.demand.arguments index).1 ∧
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠
      (site.occurrence.demand.arguments index).2 := by
  have original := reachable
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  obtain ⟨raw,member,same⟩ := GeneralNominalCenteredHeadStepTrace.centered_site_registered path site registered
  have excluded := GeneralNominalHeadSiteSupport185.wf_sites_separate
    (invocation := invocation) (declaration := declaration) (owner := owner) (position := position)
    original raw member high
  have endpoints : (site.occurrence.demand.arguments index).1 ∈
      GeneralNominalCenteredEmptyFrame179.rawSiteSources raw ∧
      (site.occurrence.demand.arguments index).2 ∈ GeneralNominalCenteredEmptyFrame179.rawSiteSources raw := by
    unfold GeneralNominalCenteredEmptyFrame179.rawSiteSources
    rw [same]
    constructor <;> apply List.mem_append_left <;>
      exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩
  exact ⟨fun equal => excluded (equal.symm ▸ endpoints.1),fun equal => excluded (equal.symm ▸ endpoints.2)⟩

theorem site_source_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (source : SiteSource site name)
    (allocated : name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core name origin := by
  cases source with
  | lower index => exact False.elim ((site_endpoint_separate reachable site registered index (by omega)).1 allocated.symm)
  | upper index => exact False.elim ((site_endpoint_separate reachable site registered index (by omega)).2 allocated.symm)
  | center index =>
    obtain ⟨origin,witness,_⟩ := GeneralNominalHeadCoreCoverage185.uniform_wf_site_readback
      reachable site registered index allocated
    exact ⟨origin,witness⟩

theorem registered_emitted
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, ∀ site ∈ plan.emitted, site ∈ state.core.sites := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro previous member site emitted
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_append_right _ emitted
      · exact List.mem_append_left _ (ih previous member site emitted)

theorem wf_child_registered
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (clause : Clause) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) : plan.childSite clause signature ∈ state.core.sites := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  apply registered_emitted path plan registered
  exact List.mem_map.mpr ⟨⟨clause,member⟩,List.mem_attach ..,rfl⟩

theorem head_roots (plan : Plan roles) :
    Roots plan.headSchema (List.ofFn plan.input.center ++ [0]) := by
  apply GeneralNominalGeneratedSupport184.schemas_roots
  intro index
  cases found : (List.ofFn plan.input.center)[index]? with
  | none => simp [originSource]
  | some name =>
    have member : name ∈ List.ofFn plan.input.center := List.mem_of_getElem? found
    simp [originSource,member]

theorem input_requests_subset (packet : GeneralNominalSaturationState.Packet roles) :
    GeneralNominalPacketSupport.inputRequests packet ⊆
      requests packet.context.state packet.registry packet.site.occurrence packet.declaration packet.checked packet.bindings := by
  intro request member
  obtain ⟨emission,present,member⟩ := List.mem_flatMap.mp member
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨emission,present,List.mem_append_left _ member⟩

theorem wf_request_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (request : Request)
    (present : request ∈ requests plan.packet.context.state plan.packet.registry plan.packet.site.occurrence
      plan.packet.declaration plan.packet.checked plan.packet.bindings) (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠ request.target := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  have member := registered_packets path plan registered
  have bound := GeneralNominalCenteredHeadStepAncestry.installed_depth_bound (registry := registry) point ground
  have seed := GeneralNominalHeadPacketSupport185.packet_seed path plan.packet member
  rw [(GeneralNominalCenteredHeadStepTrace.configuration_trace path).1]
  change fresh context.state.seed invocation declaration purpose owner position ≠ request.target
  rw [← seed]
  apply GeneralNominalHeadPacketSupport185.packet_request_separate plan.packet high _ _ request present
  · intro output requested equal
    rw [seed] at equal
    exact GeneralNominalCenteredAllocation.outside_pool source high
      (equal.symm ▸ GeneralNominalHeadPacketSupport185.packet_outputs_pool source bound path plan.packet member output requested)
  · rw [seed]
    exact fun inside => GeneralNominalCenteredAllocation.outside_pool source high
      (GeneralNominalHeadPacketSupport185.packet_context_pool source bound path plan.packet member inside)

theorem center_list_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (site : Site roles) (registered : site ∈ state.core.sites)
    (member : name ∈ List.ofFn site.center ++ [0])
    (allocated : name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core name origin := by
  rcases List.mem_append.mp member with member | member
  · obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    exact site_source_actual reachable site registered (.center index) allocated
  · have zero := List.mem_singleton.mp member
    have positive := GeneralNominalIdentities.source_above_seed state.core.erased.current.context.state.seed
      (invocation,declaration,8,owner,position)
    change _ < fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position at positive
    omega

/-- Schema origin support has no new purpose-eight case beyond a registered
site center. Ordinary request schemas use the already excluded raw names. -/
theorem schema_root_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (location : GeneralNominalRegisteredReadback182.SchemaLocation plan body)
    (rootMember : (∃ test ∈ body.tests, originSource test.1 = name) ∨
      ∃ entry ∈ body.variables, originSource entry.origin = name)
    (allocated : name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core name origin := by
  have roots_member {names} (supported : Roots body names) : name ∈ names := by
    rcases rootMember with ⟨test,present,rfl⟩ | ⟨entry,present,rfl⟩
    · exact supported.1 test present
    · exact supported.2 entry present
  cases location with
  | head =>
    exact center_list_actual reachable plan.input
      (GeneralNominalHeadCandidateReadback185.wf_registered_input reachable plan registered)
      (roots_member (head_roots plan)) allocated
  | input =>
    have member := roots_member (GeneralNominalGeneratedSupport184.generated_roots
      plan.packet.context.state plan.packet.context.interpretation (GeneralNominalPacketSupport.inputRequests plan.packet))
    obtain ⟨request,present,equal⟩ := List.mem_map.mp member
    exact False.elim (wf_request_separate reachable plan registered request
      (input_requests_subset plan.packet present) (by omega) (allocated.symm.trans equal.symm))
  | named =>
    have member := roots_member (GeneralNominalGeneratedSupport184.generated_roots
      plan.packet.context.state plan.packet.context.interpretation
      (requests plan.packet.context.state plan.packet.registry plan.packet.site.occurrence
        plan.packet.declaration plan.packet.checked plan.packet.bindings))
    obtain ⟨request,present,equal⟩ := List.mem_map.mp member
    exact False.elim (wf_request_separate reachable plan registered request present
      (by omega) (allocated.symm.trans equal.symm))
  | child clause member signature =>
    have targets := roots_member (GeneralNominalGeneratedSupport184.generated_roots
      plan.packet.context.state plan.packet.context.interpretation (plan.childRequests clause signature))
    obtain ⟨request,present,equal⟩ := List.mem_map.mp targets
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
    exact site_source_actual reachable (plan.childSite clause signature)
      (wf_child_registered reachable plan registered clause member signature)
      (equal ▸ (SiteSource.center (site := plan.childSite clause signature) index)) allocated

theorem wf_registered_packet
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) : plan.packet ∈ state.core.erased.current.packets := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  exact registered_packets path plan registered

theorem schema_source_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (location : GeneralNominalRegisteredReadback182.SchemaLocation plan body)
    (source : SchemaSource plan body name)
    (allocated : name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core name origin := by
  cases source with
  | test entry member =>
    exact schema_root_actual reachable plan registered location (Or.inl ⟨entry,member,rfl⟩) allocated
  | useSource entry member source =>
    cases source with
    | origin =>
      exact schema_root_actual reachable plan registered location (Or.inr ⟨entry,member,rfl⟩) allocated
    | binder actual => exact ⟨entry.origin,plan,registered,body,location,entry,member,actual,rfl,rfl⟩
    | output nonactual =>
      exact False.elim ((capture_separate reachable plan.packet
        (wf_registered_packet reachable plan registered) (by omega) entry.name).1 allocated.symm)
    | lower nonactual =>
      exact False.elim ((capture_separate reachable plan.packet
        (wf_registered_packet reachable plan registered) (by omega) entry.name).2.1 allocated.symm)
    | upper nonactual =>
      exact False.elim ((capture_separate reachable plan.packet
        (wf_registered_packet reachable plan registered) (by omega) entry.name).2.2 allocated.symm)

theorem plan_source_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (source : PlanSource plan name)
    (allocated : name = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core name origin := by
  cases source with
  | input source =>
    exact site_source_actual reachable plan.input
      (GeneralNominalHeadCandidateReadback185.wf_registered_input reachable plan registered) source allocated
  | child clause member signature source =>
    exact site_source_actual reachable (plan.childSite clause signature)
      (wf_child_registered reachable plan registered clause member signature) source allocated
  | schema location source => exact schema_source_actual reachable plan registered location source allocated
  | capture source =>
    cases source with
    | binder name needed =>
      exact GeneralNominalHeadCoreCoverage185.wf_capture_actual reachable plan registered name needed
    | lower name needed =>
      exact False.elim ((capture_separate reachable plan.packet
        (wf_registered_packet reachable plan registered) (by omega) name).2.1 allocated.symm)
    | upper name needed =>
      exact False.elim ((capture_separate reachable plan.packet
        (wf_registered_packet reachable plan registered) (by omega) name).2.2 allocated.symm)

theorem wf_overlap_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (member : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state.core) :
    ∃ origin, ActualBinder state.core
      (fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) origin := by
  have source := (full_iff state.core _).mp member
  generalize equal : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position = name at source ⊢
  cases source with
  | raw present =>
    exact False.elim (GeneralNominalHeadRawSeparation185.wf_raw_separate reachable (by omega) (equal.symm ▸ present))
  | site site registered source => exact site_source_actual reachable site registered source equal.symm
  | plan plan registered source => exact plan_source_actual reachable plan registered source equal.symm

theorem uniform_wf_overlap_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (member : fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state.core) :
    ∃ origin, ActualBinder state.core
      (fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin
        (.source (fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position)) := by
  obtain ⟨origin,witness⟩ := wf_overlap_actual reachable member
  exact ⟨origin,witness,fun model valid => actual_same valid.1 witness⟩

end Yulang.GeneralNominalHeadCoreOverlap185
