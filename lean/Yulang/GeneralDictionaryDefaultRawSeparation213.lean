import Yulang.GeneralDictionaryDefaultEnumeration208
import Yulang.GeneralNominalRawSupport183
import Yulang.GeneralDictionaryDefaultPacketSupport213
import Yulang.GeneralNominalCenteredAllocation

/-! Raw center-namespace separation for the corrected transitions. This uses
actual refresh support, not the deliberately weaker Built relation. -/
namespace Yulang.GeneralDictionaryDefaultRawSeparation213
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
variable {roles : Roles.RoleDecls}

def Low (raw : GeneralNominalState.State) : Prop :=
  ∀ invocation declaration purpose owner position, 7 ≤ purpose →
    fresh raw.seed invocation declaration purpose owner position ∉ GeneralNominalState.sources raw

theorem private_low (packet : GeneralNominalSaturationState.Packet roles)
    (visible : packet.declaration ∈ packet.registry.declarations) (low : Low packet.context.state) :
    Low packet.privateContext.state := by
  intro invocation declaration purpose owner position high present
  have supported := GeneralNominalAllocationSupport.private_sources packet visible
    (pool := GeneralNominalState.sources packet.context.state ++ GeneralNominalAllocation.reserved
      packet.context.state packet.registry packet.site.occurrence.identity)
    (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h) present
  rcases List.mem_append.mp supported with old | allocated
  · exact low invocation declaration purpose owner position high old
  · obtain ⟨key,member,equal⟩ := List.mem_map.mp allocated
    have bounded := GeneralNominalCenteredAllocation.key_purpose member
    have identities := (GeneralNominalIdentities.source_identity packet.context.state.seed _ _).mp equal
    have purposes := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.1) identities
    change key.2.2.1 = purpose at purposes
    omega

open GeneralDictionaryDefaultDepth208 (InstalledDepthBound frame configuration_trace)
open GeneralDictionaryDefaultEnumeration208 (source_pool)
open GeneralNominalActualTraceSupport (pool)

theorem current_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources state.core.erased.current.context.state :=
  fun member => GeneralNominalCenteredAllocation.outside_pool source high ((source_pool source bound path).1 member)

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
    | administrative action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · rw [(frame enabled).context_eq]
        exact (source_pool source bound path).1
      · exact ih packet member

theorem packet_seed
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets, packet.context.state.seed = context.state.seed := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · rw [(frame enabled).context_eq]
        exact (configuration_trace path).1
      · exact ih packet member

theorem historical_capture_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.core.erased.current.packets)
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
      (packet_context_pool source bound path packet member present)
  simpa only [seed] using And.intro
    (GeneralNominalRawSupport183.capture_output_separate packet high name)
    (GeneralNominalRawSupport183.capture_inputs_separate packet high outside name)
theorem packet_visible
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.core.erased.current.packets, packet.declaration ∈ packet.registry.declarations := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · exact effect.frame.registry_eq ▸ effect.frame.visible
      · exact ih packet member

/-- Historical raw-head support contributes no center-purpose identities.
Actual binder/head-schema and live output support are separate obligations. -/
theorem historical_head_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (member : plan.packet ∈ state.core.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralDictionaryDefaultPacketSupport213.headSources plan := by
  have seed := packet_seed path plan.packet member
  have low : Low plan.packet.context.state := by
    intro inv decl pur own pos hi present
    rw [seed] at present
    exact GeneralNominalCenteredAllocation.outside_pool source hi
      (packet_context_pool source bound path plan.packet member present)
  intro present
  rcases List.mem_append.mp present with privatePart | reportPart
  · have old := GeneralDictionaryDefaultRawSupport213.subset _ privatePart
    rw [← seed] at old
    exact private_low plan.packet (packet_visible path plan.packet member) low
      invocation declaration purpose owner position high old
  · have old := GeneralNominalRawOrigin182.report_sources_subset
      plan.packet.context plan.packet.declaration plan.packet.bounds reportPart
    rw [← seed] at old
    exact low invocation declaration purpose owner position high old
theorem historical_capture_actual
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (member : plan.packet ∈ state.core.erased.current.packets)
    (high : 7 ≤ purpose)
    (present : fresh context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalCenteredFrame179.captureSources plan) :
    ∃ name ∈ GeneralNominalCenteredFrame179.captureNames plan,
      plan.binder name = fresh context.state.seed invocation declaration purpose owner position := by
  obtain ⟨name,named,within⟩ := List.mem_flatMap.mp present
  have separate := historical_capture_separate (invocation := invocation) (declaration := declaration) (owner := owner) (position := position) source bound path plan.packet member high name
  rcases List.mem_cons.mp within with lower | within
  · exact False.elim (separate.2.1 lower)
  rcases List.mem_cons.mp within with upper | within
  · exact False.elim (separate.2.2 upper)
  exact ⟨name,named,(List.mem_singleton.mp within).symm⟩
end Yulang.GeneralDictionaryDefaultRawSeparation213
