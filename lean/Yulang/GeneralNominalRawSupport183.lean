import Yulang.GeneralNominalRawOrigin182

/-! Partial raw-support producers. Private historical contexts lie in the trace
pool. Capture outputs avoid center namespaces without a finite-pool assumption.
Generated-schema roots and raw observed-site roots remain open obligations. -/
namespace Yulang.GeneralNominalRawSupport183
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredAncestry (InstalledDepthBound)
open GeneralNominalActualTraceSupport (pool)
open GeneralNominalAllocationSupport
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem packet_private_pool
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.erased.current.packets,
      GeneralNominalState.sources packet.privateContext.state ⊆ pool registry context root limit := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · have reservations := GeneralNominalCenteredAncestry.reservations_finite bound path generated enabled novel guard
        have listed : GeneralNominalAllocation.reserved plan.packet.context.state plan.packet.registry
            plan.packet.site.occurrence.identity ⊆ pool registry context root limit :=
          fun _ present => List.mem_append_right _ (reservations present)
        have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
          simpa only [enabled.1.1] using enabled.1.2.2.2.1
        apply private_sources plan.packet visible _ listed
        rw [enabled.1.2.1]
        exact (GeneralNominalCenteredEnumeration.source_pool source bound path).1
      · exact ih packet member

theorem packet_seed
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.erased.current.packets, packet.context.state.seed = context.state.seed := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · rw [enabled.1.2.1]
        exact (GeneralNominalCenteredTrace.configuration_trace path).1
      · exact ih packet member

theorem capture_output_separate (packet : GeneralNominalSaturationState.Packet roles)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh packet.context.state.seed invocation declaration purpose owner position ≠
      (GeneralNominalPacketSupport.capture packet).outputs name := by
  exact GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 2)

theorem capture_inputs_separate (packet : GeneralNominalSaturationState.Packet roles)
    (high : 7 ≤ purpose)
    (outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state) (name : Nat) :
    fresh packet.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh packet.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2 := by
  change _ ≠ (GeneralNominalAllocation.capture _ _ _ _ _ |>.inputs name).1 ∧
    _ ≠ (GeneralNominalAllocation.capture _ _ _ _ _ |>.inputs name).2
  unfold GeneralNominalAllocation.capture
  dsimp only
  split
  · rename_i bounds recorded
    have endpoints := occurrences_endpoints
      (report_endpoints packet.context.state (GeneralNominalPacketSupport.report packet)) name bounds
      (by change bounds ∈ GeneralNominalAllocation.occurrences packet.bindings name; rw [recorded]; exact List.mem_cons_self ..)
    exact ⟨fun same => outside (same ▸ endpoints.1),fun same => outside (same ▸ endpoints.2)⟩
  · exact ⟨GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 0),
      GeneralNominalCenteredAllocation.fresh_namespaces (by omega : purpose ≠ 1)⟩

theorem historical_capture_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh context.state.seed invocation declaration purpose owner position ≠
      (GeneralNominalPacketSupport.capture packet).outputs name ∧
    fresh context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2 := by
  have seed := packet_seed path packet member
  have outside : fresh packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.context.state := by
    rw [seed]
    exact fun present => GeneralNominalCenteredAllocation.outside_pool source high
      (GeneralNominalRawOrigin182.packet_context_pool source bound path packet member present)
  simpa only [seed] using And.intro (capture_output_separate packet high name)
    (capture_inputs_separate packet high outside name)

theorem historical_private_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.privateContext.state :=
  fun present => GeneralNominalCenteredAllocation.outside_pool source high
    (packet_private_pool source bound path packet member present)
end Yulang.GeneralNominalRawSupport183
