import Yulang.GeneralDictionaryRelativePacket225
import Yulang.GeneralDictionaryHeadSharingRawSupport220

namespace Yulang.GeneralDictionaryRelativeProvenance226
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalAllocation GeneralNominalAllocationSupport GeneralNominalState
open GeneralDictionaryHeadSharingRawSupport220
open GeneralDictionaryRelativePacket225
variable {roles : Roles.RoleDecls}

def baseSources (state : GeneralNominalState.State) : List Nat :=
  List.ofFn state.base.source

theorem report_endpoints (state : GeneralNominalState.State)
    (report : GeneralNominalRecursiveInspection.Report state) :
    Endpoints (GeneralNominalRecursiveInspection.bindings state report) (baseSources state) := by
  intro entry member
  obtain ⟨capture,_,rfl⟩ := List.mem_map.mp member
  exact ⟨List.mem_ofFn.mpr ⟨capture.bounds.1,rfl⟩,
    List.mem_ofFn.mpr ⟨capture.bounds.2,rfl⟩⟩

theorem checks_base (state : GeneralNominalState.State)
    (report : GeneralNominalRecursiveInspection.Report state)
    (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ GeneralNominalRecursiveInspection.selfChecks state report) :
    atomSources atom ⊆ baseSources state := by
  obtain ⟨bounds,_,rfl⟩ := List.mem_map.mp member
  intro name present
  rcases List.mem_append.mp present with first | last
  · cases List.mem_singleton.mp first
    exact List.mem_ofFn.mpr ⟨bounds.1,rfl⟩
  · cases List.mem_singleton.mp last
    exact List.mem_ofFn.mpr ⟨bounds.2,rfl⟩

def localSources (plan : Plan roles) : List Nat :=
  localTargets plan.packet.context.state plan.packet.registry
    plan.packet.site.occurrence.identity plan.packet.declaration

theorem ordinary_sources (plan : Plan roles) :
    (ordinaryAtoms plan).flatMap atomSources ⊆ baseSources plan.packet.context.state ++ localSources plan := by
  intro name member
  obtain ⟨atom,present,read⟩ := List.mem_flatMap.mp member
  have endpoints := report_endpoints plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)
  have widened : Endpoints plan.packet.bindings (baseSources plan.packet.context.state ++ localSources plan) := by
    intro entry member
    exact ⟨List.mem_append_left _ (endpoints entry member).1,
      List.mem_append_left _ (endpoints entry member).2⟩
  rcases List.mem_append.mp present with ordinary | check
  · rcases List.mem_append.mp ordinary with cross | merge
    · exact cross_sources widened atom cross read
    · exact merges_sources_tight plan.packet.context.state widened
        (fun n declared => capture_targets_local plan.packet.context.state endpoints declared) atom merge read
  · exact List.mem_append_left _ (checks_base plan.packet.context.state
      (GeneralNominalPacketSupport.report plan.packet) atom check read)

def observedSources (plan : Plan roles) : List Nat :=
  GeneralDictionaryTightProjection224.reportSources plan.packet.context.state
    (GeneralNominalPacketSupport.report plan.packet)

theorem base_observed (plan : Plan roles) : baseSources plan.packet.context.state ⊆ observedSources plan := by
  intro name member
  simp only [observedSources,GeneralDictionaryTightProjection224.reportSources,List.mem_append]
  exact Or.inl (Or.inl (Or.inl member))

theorem head_sources (plan : Plan roles) :
    headSources plan ⊆ observedSources plan ++ localSources plan := by
  intro name member
  rcases List.mem_append.mp member with ordinary | observed
  · rcases List.mem_append.mp (ordinary_sources plan ordinary) with base | localName
    · exact List.mem_append_left _ (base_observed plan base)
    · exact List.mem_append_right _ localName
  · exact List.mem_append_left _ observed

/-- An origin newly read by this relative head belongs to this declaration's
input aggregates; report-observed origins are explicitly excluded. -/
theorem head_new_origin (plan : Plan roles) (key : Origin)
    (absent : source plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity key ∉ observedSources plan)
    (present : source plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity key ∈ headSources plan) :
    ∃ name ∈ plan.packet.declaration.inputNames,
      key = origin plan.packet.site.occurrence.identity plan.packet.declaration.id 0 name 0 ∨
      key = origin plan.packet.site.occurrence.identity plan.packet.declaration.id 1 name 0 := by
  rcases List.mem_append.mp (head_sources plan present) with observed | localName
  · exact False.elim (absent observed)
  · obtain ⟨name,declared,member⟩ := List.mem_flatMap.mp localName
    refine ⟨name,declared,?_⟩
    rcases List.mem_cons.mp member with first | last
    · exact Or.inl ((source_identity plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity _ _).mp first)
    · exact Or.inr ((source_identity plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity _ _).mp (List.mem_singleton.mp last))

end Yulang.GeneralDictionaryRelativeProvenance226
