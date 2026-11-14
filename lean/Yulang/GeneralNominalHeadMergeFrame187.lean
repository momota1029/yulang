import Yulang.GeneralNominalHeadProjectionFrame187
import Yulang.GeneralNominalHeadDeclaredBounds187
import Yulang.GeneralNominalAllocationSupport

/-! Merge equations use precisely current raw sources and declared capture
endpoints, not all reserved allocation keys. The head extension retains them. -/
namespace Yulang.GeneralNominalHeadMergeFrame187
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalHeadConservativeExtension186 (support)
open GeneralNominalHeadEquationExtension186 (uses)
open GeneralNominalAllocationSupport
open GeneralNominalAllocation
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (atomSources)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {state : State roles}

 theorem merge_sources (context : GeneralNominalState.State)
    (supported : Endpoints bindings pool)
    (captured : ∀ name ∈ declaration.inputNames,
      ((capture context registry invocation declaration.id bindings).inputs name).1 ∈ pool ∧
      ((capture context registry invocation declaration.id bindings).inputs name).2 ∈ pool)
    (atom : PresenceNormalForm.Atom Nat) (member : atom ∈ merges context registry invocation declaration bindings) :
    atomSources atom ⊆ pool := by
  obtain ⟨name,declared,member⟩ := List.mem_flatMap.mp member
  split at member
  · cases member
  · rcases List.mem_append.mp member with left | right
    · exact equation_sources _ _ (captured name declared).1
        (lower_sources _ (occurrences_endpoints supported name)) atom left
    · exact equation_sources _ _ (captured name declared).2
        (upper_sources _ (occurrences_endpoints supported name)) atom right

 theorem candidate_raw_sources (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) :
    GeneralNominalState.sources candidate.packet.context.state ⊆ support state candidate (uses candidate) := by
  intro name member
  apply List.mem_append_left
  apply GeneralNominalHeadCandidateSupport186.current_source state
  simpa only [frame.context_eq] using member

 theorem candidate_endpoints (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) :
    Endpoints candidate.packet.bindings (support state candidate (uses candidate)) := by
  intro binding member
  have both := report_endpoints candidate.packet.context.state
    (GeneralNominalPacketSupport.report candidate.packet) binding member
  exact ⟨candidate_raw_sources candidate frame both.1,candidate_raw_sources candidate frame both.2⟩

 theorem candidate_merge_sources (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate)
    (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ merges candidate.packet.context.state candidate.packet.registry
      candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings) :
    atomSources atom ⊆ support state candidate (uses candidate) := by
  apply merge_sources candidate.packet.context.state (candidate_endpoints candidate frame) _ atom member
  intro name declared
  obtain ⟨index,equal⟩ := GeneralNominalHeadDeclaredBounds187.frame_name_use candidate frame name declared
  subst name
  exact ⟨List.mem_append_right _ (GeneralNominalHeadConservativeExtension186.lower_mem candidate _ index),
    List.mem_append_right _ (GeneralNominalHeadConservativeExtension186.upper_mem candidate _ index)⟩

 theorem merges_iff (candidate : Plan roles)
    (frame : Frame registry state.core focus key candidate) (first last : Assignment)
    (same : ∀ name ∈ support state candidate (uses candidate), first name = last name) :
    PresenceNormalForm.All CommonNominalFullCarrier.model first
      (merges candidate.packet.context.state candidate.packet.registry candidate.packet.site.occurrence.identity
        candidate.packet.declaration candidate.packet.bindings) ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model last
      (merges candidate.packet.context.state candidate.packet.registry candidate.packet.site.occurrence.identity
        candidate.packet.declaration candidate.packet.bindings) := by
  apply forall_congr'; intro atom
  apply forall_congr'; intro member
  exact GeneralNominalCenteredModelExtension.atom_same atom
    (fun name present => same name (candidate_merge_sources candidate frame atom member present))

 theorem extension_retains_inspection (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model)
    (projection : GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
      (GeneralNominalQueryProvenance183.headInspection candidate) model)
    (recorded : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges candidate.packet.context.state candidate.packet.registry candidate.packet.site.occurrence.identity
        candidate.packet.declaration candidate.packet.bindings)) :
    ∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = model name) ∧
      HeadEquations candidate extended ∧
      GeneralNominalRecursiveInspection.ProjectionModels candidate.packet.context.state
        (GeneralNominalQueryProvenance183.headInspection candidate) extended ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model extended
        (merges candidate.packet.context.state candidate.packet.registry candidate.packet.site.occurrence.identity
          candidate.packet.declaration candidate.packet.bindings) := by
  obtain ⟨extended,models,kept,head⟩ := GeneralNominalHeadInitialExtension187.frame_extension_of_projection
    checked reachable candidate frame model valid projection recorded
  refine ⟨extended,models,kept,head,?_,?_⟩
  · exact (GeneralNominalHeadProjectionFrame187.projection_iff candidate frame extended model
      (fun name member => kept name (List.mem_append_left _ member))).mpr projection
  · exact (merges_iff candidate frame extended model kept).mpr recorded

end Yulang.GeneralNominalHeadMergeFrame187
