import Yulang.GeneralDictionaryDefaultRawSupport213
import Yulang.GeneralNominalAllocationSupport

/-! Tight semantic raw support excludes unused reservation bookkeeping. -/
namespace Yulang.GeneralDictionaryHeadSharingRawSupport220
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalAllocation GeneralNominalAllocationSupport GeneralNominalState
local notation "RawSources" => GeneralDictionaryDefaultRawSupport213.sources
variable {roles : Roles.RoleDecls}

theorem slot_raw (state : GeneralNominalState.State) (slot : Fin state.base.slots) :
    state.base.source slot ∈ RawSources state :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩))

theorem report_endpoints_raw (state : GeneralNominalState.State)
    (report : GeneralNominalRecursiveInspection.Report state) :
    Endpoints (GeneralNominalRecursiveInspection.bindings state report) (RawSources state) := by
  intro entry member
  obtain ⟨capture,_,rfl⟩ := List.mem_map.mp member
  exact ⟨slot_raw state capture.bounds.1,slot_raw state capture.bounds.2⟩

/-- Only this declaration's capture endpoints, not every reserved key. -/
theorem merges_sources_tight (state : GeneralNominalState.State)
    (supported : Endpoints bindings pool)
    (targets : ∀ name ∈ declaration.inputNames,
      ((capture state registry invocation declaration.id bindings).inputs name).1 ∈ pool ∧
      ((capture state registry invocation declaration.id bindings).inputs name).2 ∈ pool)
    (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ merges state registry invocation declaration bindings) :
    atomSources atom ⊆ pool := by
  obtain ⟨name,declared,member⟩ := List.mem_flatMap.mp member
  split at member
  · cases member
  · rcases List.mem_append.mp member with left | right
    · exact equation_sources _ _ (targets name declared).1
        (lower_sources _ (occurrences_endpoints supported name)) atom left
    · exact equation_sources _ _ (targets name declared).2
        (upper_sources _ (occurrences_endpoints supported name)) atom right

theorem extend_sources_raw (state : GeneralNominalState.State) (reservations : List Nat)
    (atoms : List (PresenceNormalForm.Atom Nat)) (old : RawSources state ⊆ pool)
    (generated : ∀ atom ∈ atoms, atomSources atom ⊆ pool) :
    RawSources (GeneralNominalState.extend state reservations atoms) ⊆ pool := by
  intro name member
  have split : name ∈ RawSources state ∨ name ∈ atoms.flatMap atomSources := by
    simpa only [GeneralDictionaryDefaultRawSupport213.sources,GeneralNominalState.extend,List.flatMap_append,List.mem_append,or_assoc] using member
  rcases split with prior | fresh
  · exact old prior
  · obtain ⟨atom,present,within⟩ := List.mem_flatMap.mp fresh
    exact generated atom present within

theorem propagate_sources_raw (state : GeneralNominalState.State)
    (old : RawSources state ⊆ pool) (supported : Endpoints bindings pool)
    (targets : ∀ name ∈ declaration.inputNames,
      ((capture state registry invocation declaration.id bindings).inputs name).1 ∈ pool ∧
      ((capture state registry invocation declaration.id bindings).inputs name).2 ∈ pool) :
    RawSources (propagate state registry invocation declaration bindings) ⊆ pool := by
  apply extend_sources_raw state (reserved state registry invocation) (cross bindings ++ merges state registry invocation declaration bindings) old
  intro atom member
  rcases List.mem_append.mp member with cross | merge
  · exact cross_sources supported atom cross
  · exact merges_sources_tight state supported targets atom merge

theorem checks_sources_raw (state : GeneralNominalState.State)
    (report : GeneralNominalRecursiveInspection.Report state) (old : RawSources state ⊆ pool)
    (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ GeneralNominalRecursiveInspection.selfChecks state report) :
    atomSources atom ⊆ pool := by
  obtain ⟨bounds,_,rfl⟩ := List.mem_map.mp member
  intro name present
  rcases List.mem_append.mp present with first | last
  · cases List.mem_singleton.mp first
    exact old (slot_raw state bounds.1)
  · cases List.mem_singleton.mp last
    exact old (slot_raw state bounds.2)

/-- A private head adds no semantic dependency on unrelated reserved names. -/
theorem private_sources_raw (packet : GeneralNominalSaturationState.Packet roles)
    (old : RawSources packet.context.state ⊆ pool)
    (targets : ∀ name ∈ packet.declaration.inputNames,
      ((capture packet.context.state packet.registry packet.site.occurrence.identity
        packet.declaration.id packet.bindings).inputs name).1 ∈ pool ∧
      ((capture packet.context.state packet.registry packet.site.occurrence.identity
        packet.declaration.id packet.bindings).inputs name).2 ∈ pool) :
    RawSources packet.privateContext.state ⊆ pool := by
  apply extend_sources_raw _ [] _
  · apply propagate_sources_raw _ old _ targets
    intro binding member
    have endpoints := report_endpoints_raw packet.context.state
      (GeneralNominalPacketSupport.report packet) binding member
    exact ⟨old endpoints.1,old endpoints.2⟩
  · exact checks_sources_raw packet.context.state (GeneralNominalPacketSupport.report packet) old

end Yulang.GeneralDictionaryHeadSharingRawSupport220
