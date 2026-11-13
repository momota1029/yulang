import Yulang.GeneralDictionaryPersistentCatalog

/-! Per-request filtering retains closed requests from mixed packets instead of
throwing away an entire variable-bearing packet. The predicate is syntactic;
model validity is obtained from the existing actual-reachability invariant. -/
namespace Yulang.GeneralDictionaryRequestCatalog
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralNominalSaturationState GeneralNominalMaterialization
open GeneralDictionaryReachableRequestHistory
variable {roles : Roles.RoleDecls}

noncomputable def eligibleRequests (packet : Packet roles) : List Request := by
  classical
  exact (emitted packet).filter fun request => decide
    ((generated packet.context.state packet.context.interpretation [request]).variables = [])

noncomputable def catalog (state : Tracked roles) : List Request :=
  state.current.packets.reverse.flatMap eligibleRequests

theorem eligible_iff (packet : Packet roles) (request : Request) :
    request ∈ eligibleRequests packet ↔ request ∈ emitted packet ∧
      (generated packet.context.state packet.context.interpretation [request]).variables = [] := by
  classical
  simp [eligibleRequests]

theorem member_iff (state : Tracked roles) (request : Request) :
    request ∈ catalog state ↔ ∃ packet ∈ state.current.packets,
      request ∈ emitted packet ∧
      (generated packet.context.state packet.context.interpretation [request]).variables = [] := by
  simp [catalog,List.mem_flatMap,eligible_iff]

theorem covered_iff (state : Tracked roles) (batch : List Request) :
    GeneralDictionaryRecordedBatchModels.Covered state.current batch ↔
      ∀ request ∈ batch, request ∈ catalog state := by
  simp only [GeneralDictionaryRecordedBatchModels.Covered,member_iff,emitted]

theorem safe_included (state : Tracked roles) :
    ∀ request ∈ safeCatalog state, request ∈ catalog state := by
  classical
  intro request member
  obtain ⟨packet,recorded,member⟩ := List.mem_flatMap.mp member
  have present := List.mem_reverse.mp recorded
  by_cases closed : (GeneralNominalPacketSupport.namedSchema packet).variables = []
  · rw [eligible_closed packet closed] at member
    apply (member_iff state request).mpr
    exact ⟨packet,present,member,
      GeneralDictionaryInstalledRequestProvenance.singleton_variables _ _ _ closed request member⟩
  · simp [eligible,closed] at member

theorem supported (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (batch : List Request) (included : ∀ request ∈ batch, request ∈ catalog state) :
    GeneralDictionaryRequestProvenance.Supported registry root state batch :=
  GeneralDictionaryRequestProvenance.supported_of_recorded registry root state batch
    ((covered_iff state batch).mpr included)

theorem catalog_step {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles}
    (step : GeneralNominalValueSteps.Step registry root before after) :
    ∀ request ∈ catalog before, request ∈ catalog after := by
  intro request member
  obtain ⟨packet,recorded,emitted,closed⟩ := (member_iff before request).mp member
  exact (member_iff after request).mpr
    ⟨packet,GeneralNominalValueBudget.at_packets step.choose_spec.2 packet recorded,emitted,closed⟩

theorem catalog_trace {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles}
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after) :
    ∀ request ∈ catalog before, request ∈ catalog after := by
  induction path with
  | refl => exact fun _ member => member
  | tail _ step ih => exact fun request member => catalog_step step request (ih request member)

theorem shape {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (batch : List Request) (included : ∀ request ∈ batch, request ∈ catalog state) :
    (generated state.current.context.state state.current.context.interpretation batch).variables = [] ∧
      (generated state.current.context.state state.current.context.interpretation batch).unknown = false :=
  GeneralDictionaryRequestProvenance.shape registry root state reachable batch (supported registry root state batch included)
end Yulang.GeneralDictionaryRequestCatalog
