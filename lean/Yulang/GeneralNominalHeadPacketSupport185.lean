import Yulang.GeneralNominalGeneratedSupport184
import Yulang.GeneralNominalCenteredHeadStepEnumeration

/-! Actual head-step historical packet support. No simulation to the older
centered step is assumed. The explicit trace depth bound is supplied by the
existing ground termination proof at the WF boundary. -/
namespace Yulang.GeneralNominalHeadPacketSupport185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepAncestry (InstalledDepthBound)
open GeneralNominalActualTraceSupport (pool)
open GeneralNominalAllocationSupport
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
theorem packet_context_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets,
      GeneralNominalState.sources packet.context.state ⊆ pool registry context root limit := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · rw [enabled.frame.context_eq]
        exact (GeneralNominalCenteredHeadStepEnumeration.source_pool source bound path).1
      · exact ih packet member

theorem packet_report_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets) :
    GeneralNominalRawFrame179.reportSources packet.context.state
      (GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds) ⊆
      pool registry context root limit :=
  fun _ present => packet_context_pool source bound path packet member
    (GeneralNominalRawOrigin182.report_sources_subset packet.context packet.declaration packet.bounds present)

theorem fresh_outside_packet_report
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
    (centerPurpose : 7 ≤ purpose) :
    GeneralNominalCenters.fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.reportSources packet.context.state
        (GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds) :=
  fun present => GeneralNominalCenteredAllocation.outside_pool source centerPurpose
    (packet_report_pool source bound path packet member present)

theorem packet_private_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets,
      GeneralNominalState.sources packet.privateContext.state ⊆ pool registry context root limit := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · have reservations := GeneralNominalCenteredHeadStepAncestry.reservations_finite bound path generated enabled novel
        have listed : GeneralNominalAllocation.reserved plan.packet.context.state plan.packet.registry
            plan.packet.site.occurrence.identity ⊆ pool registry context root limit :=
          fun _ present => List.mem_append_right _ (reservations present)
        have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
          simpa only [enabled.frame.registry_eq] using enabled.frame.visible
        apply private_sources plan.packet visible _ listed
        rw [enabled.frame.context_eq]
        exact (GeneralNominalCenteredHeadStepEnumeration.source_pool source bound path).1
      · exact ih packet member

theorem packet_seed
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets, packet.context.state.seed = context.state.seed := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · rw [enabled.frame.context_eq]
        exact (GeneralNominalCenteredHeadStepTrace.configuration_trace path).1
      · exact ih packet member

theorem historical_private_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.privateContext.state :=
  fun present => GeneralNominalCenteredAllocation.outside_pool source high
    (packet_private_pool source bound path packet member present)
theorem packet_outputs_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets, ∀ output ∈ packet.site.occurrence.demand.outputs,
      output.target ∈ pool registry context root limit := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus next action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · exact (GeneralNominalCenteredHeadStepEnumeration.source_pool source bound path).2
          plan.packet.site enabled.frame.raw_recorded
      · exact ih packet member

theorem packet_request_separate (packet : GeneralNominalSaturationState.Packet roles)
    (high : 7 ≤ purpose)
    (outputs : ∀ output ∈ packet.site.occurrence.demand.outputs,
      fresh packet.context.state.seed invocation declaration purpose owner position ≠ output.target)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state)
    (request : Request)
    (member : request ∈ requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings) :
    fresh packet.context.state.seed invocation declaration purpose owner position ≠ request.target := by
  rcases List.mem_append.mp member with member | member
  · obtain ⟨output,present,equal⟩ := GeneralNominalGeneratedSupport184.root_request_target _ _ request member
    exact fun collision => outputs output present (collision.trans equal)
  · obtain ⟨emission,present,member⟩ := List.mem_flatMap.mp member
    have old := (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity
      packet.declaration packet.checked _ _).mem_iff.mpr present
    obtain ⟨clause,_,rfl⟩ := List.mem_map.mp old
    apply GeneralNominalGeneratedSupport184.emitted_target_separate _ _ _ _ _ _ _ _ _ request member
    · exact GeneralNominalRawSupport183.capture_inputs_separate packet high outside
    · exact GeneralNominalRawSupport183.capture_output_separate packet high
    · intro index
      exact ⟨GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 3),
        GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 4)⟩
    · intro name
      exact GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 5)

theorem packet_generated_separate (packet : GeneralNominalSaturationState.Packet roles)
    (high : 7 ≤ purpose)
    (outputs : ∀ output ∈ packet.site.occurrence.demand.outputs,
      fresh packet.context.state.seed invocation declaration purpose owner position ≠ output.target)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state) :
    fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.generatedSources (GeneralNominalPacketSupport.capture packet)
        (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
          packet.declaration packet.checked packet.bounds) := by
  intro member
  have roots := GeneralNominalGeneratedSupport184.generated_roots packet.context.state packet.context.interpretation
    (requests packet.context.state packet.registry packet.site.occurrence packet.declaration packet.checked packet.bindings)
  have excluded (name) (listed : name ∈ (requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings).map Request.target) :
      fresh packet.context.state.seed invocation declaration purpose owner position ≠ name := by
    obtain ⟨request,present,rfl⟩ := List.mem_map.mp listed
    exact packet_request_separate packet high outputs outside request present
  rcases List.mem_append.mp member with member | member
  · obtain ⟨test,present,equal⟩ := List.mem_map.mp member
    exact excluded _ (roots.1 test present) equal.symm
  · obtain ⟨entry,present,member⟩ := List.mem_flatMap.mp member
    simp only [GeneralNominalRawFrame179.useSources, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with equal | equal | equal | equal
    · exact excluded _ (roots.2 entry present) equal
    · exact GeneralNominalRawSupport183.capture_output_separate packet high entry.name equal
    · exact (GeneralNominalRawSupport183.capture_inputs_separate packet high outside entry.name).1 equal
    · exact (GeneralNominalRawSupport183.capture_inputs_separate packet high outside entry.name).2 equal

theorem historical_generated_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.generatedSources (GeneralNominalPacketSupport.capture packet)
        (GeneralNominalRecursiveCandidates.generated packet.registry packet.context packet.site.occurrence
          packet.declaration packet.checked packet.bounds) := by
  have seed := packet_seed path packet member
  have outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state := by
    rw [seed]
    exact fun present => GeneralNominalCenteredAllocation.outside_pool source high
      (packet_context_pool source bound path packet member present)
  have outputs : ∀ output ∈ packet.site.occurrence.demand.outputs,
      fresh packet.context.state.seed invocation declaration purpose owner position ≠ output.target := by
    intro output present equal
    rw [seed] at equal
    exact GeneralNominalCenteredAllocation.outside_pool source high
      (equal.symm ▸ packet_outputs_pool source bound path packet member output present)
  simpa only [seed] using packet_generated_separate packet high outputs outside

theorem historical_packet_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.packetSources packet := by
  intro present
  rcases List.mem_append.mp present with present | present
  · rcases List.mem_append.mp present with present | present
    · exact historical_private_separate source bound path packet member high present
    · exact fresh_outside_packet_report source bound path packet member high present
  · exact historical_generated_separate source bound path packet member high present


end Yulang.GeneralNominalHeadPacketSupport185
