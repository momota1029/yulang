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

namespace Yulang.GeneralDictionaryHeadSharingRawSupport220
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalAllocation GeneralNominalAllocationSupport GeneralNominalState
local notation "RawSources" => GeneralDictionaryDefaultRawSupport213.sources
variable {roles : Roles.RoleDecls}

/-- The only new semantic raw names belong to the declaration being propagated. -/
def localTargets (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) : List Nat :=
  declaration.inputNames.flatMap fun name =>
    [source state registry invocation (origin invocation declaration.id 0 name 0),
     source state registry invocation (origin invocation declaration.id 1 name 0)]

theorem capture_targets_local (state : GeneralNominalState.State)
    (supported : Endpoints bindings pool) (declared : name ∈ declaration.inputNames) :
    ((capture state registry invocation declaration.id bindings).inputs name).1 ∈
        pool ++ localTargets state registry invocation declaration ∧
    ((capture state registry invocation declaration.id bindings).inputs name).2 ∈
        pool ++ localTargets state registry invocation declaration := by
  have low : source state registry invocation (origin invocation declaration.id 0 name 0) ∈
      localTargets state registry invocation declaration :=
    List.mem_flatMap.mpr ⟨name,declared,by simp⟩
  have high : source state registry invocation (origin invocation declaration.id 1 name 0) ∈
      localTargets state registry invocation declaration :=
    List.mem_flatMap.mpr ⟨name,declared,by simp⟩
  cases found : occurrences bindings name with
  | nil => simp only [capture,found]; exact ⟨List.mem_append_right _ low,List.mem_append_right _ high⟩
  | cons first rest =>
    cases rest with
    | nil =>
      have endpoints := occurrences_endpoints supported name first (by simp [found])
      simp only [capture,found]
      exact ⟨List.mem_append_left _ endpoints.1,List.mem_append_left _ endpoints.2⟩
    | cons second tail =>
      simp only [capture,found]
      exact ⟨List.mem_append_right _ low,List.mem_append_right _ high⟩

/-- This sharp one-step support theorem does not assert full-trace freshness. -/
theorem private_sources_local (packet : GeneralNominalSaturationState.Packet roles) :
    RawSources packet.privateContext.state ⊆ RawSources packet.context.state ++
      localTargets packet.context.state packet.registry packet.site.occurrence.identity packet.declaration := by
  apply private_sources_raw packet (fun _ member => List.mem_append_left _ member)
  intro name declared
  exact capture_targets_local packet.context.state
    (report_endpoints_raw packet.context.state (GeneralNominalPacketSupport.report packet)) declared

theorem localTargets_other_key (state : GeneralNominalState.State)
    (different : otherKey ≠ declaration.id) :
    source state registry invocation (origin otherInvocation otherKey purpose owner position) ∉
      localTargets state registry invocation declaration := by
  intro member
  obtain ⟨name,_,member⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp member with first | last
  · have identities := (source_identity state registry invocation _ _).mp first
    exact different (congrArg (fun key : Origin => key.2.1) identities)
  · have identities := (source_identity state registry invocation _ _).mp (List.mem_singleton.mp last)
    exact different (congrArg (fun key : Origin => key.2.1) identities)

/-- Installing this declaration cannot newly constrain another declaration's
aggregate identity through its private raw head, despite reserving every key. -/
theorem private_other_key_prior (packet : GeneralNominalSaturationState.Packet roles)
    (different : otherKey ≠ packet.declaration.id) :
    source packet.context.state packet.registry packet.site.occurrence.identity
      (origin otherInvocation otherKey purpose owner position) ∈ RawSources packet.privateContext.state →
    source packet.context.state packet.registry packet.site.occurrence.identity
      (origin otherInvocation otherKey purpose owner position) ∈ RawSources packet.context.state := by
  intro member
  rcases List.mem_append.mp (private_sources_local packet member) with old | localName
  · exact old
  · exact False.elim (localTargets_other_key packet.context.state different localName)

/-- Exact provenance for a newly read allocated origin in one private head. -/
theorem private_new_origin (packet : GeneralNominalSaturationState.Packet roles)
    (key : Origin)
    (absent : source packet.context.state packet.registry packet.site.occurrence.identity key ∉
      RawSources packet.context.state)
    (present : source packet.context.state packet.registry packet.site.occurrence.identity key ∈
      RawSources packet.privateContext.state) :
    ∃ name ∈ packet.declaration.inputNames,
      key = origin packet.site.occurrence.identity packet.declaration.id 0 name 0 ∨
      key = origin packet.site.occurrence.identity packet.declaration.id 1 name 0 := by
  rcases List.mem_append.mp (private_sources_local packet present) with old | localName
  · exact False.elim (absent old)
  · obtain ⟨name,declared,member⟩ := List.mem_flatMap.mp localName
    refine ⟨name,declared,?_⟩
    rcases List.mem_cons.mp member with first | last
    · exact Or.inl ((source_identity packet.context.state packet.registry packet.site.occurrence.identity _ _).mp first)
    · exact Or.inr ((source_identity packet.context.state packet.registry packet.site.occurrence.identity _ _).mp
        (List.mem_singleton.mp last))

end Yulang.GeneralDictionaryHeadSharingRawSupport220
