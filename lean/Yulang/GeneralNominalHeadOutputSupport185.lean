import Yulang.GeneralNominalHeadRawSeparation185
import Yulang.GeneralNominalSupportProvenance182

/-! Output-equation support has an exact actual-binder overlap case. Source
roots and capture endpoints are excluded separately; the remaining binder has
semantic readback from the equation itself, not merely a capture bound. -/
namespace Yulang.GeneralNominalHeadOutputSupport185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalGeneratedSupport184 (Roots)
open GeneralNominalHeadLedgerFrame182 (outputSources)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

theorem output_roots (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles) :
    Roots (outputSchema state root plan) ((requests state root).map (·.target)) := by
  apply GeneralNominalGeneratedSupport184.roots_mono
    (GeneralNominalGeneratedSupport184.generated_roots plan.packet.context.state plan.packet.context.interpretation _)
  intro name member
  obtain ⟨request,within,rfl⟩ := List.mem_map.mp member
  obtain ⟨output,present,within⟩ := List.mem_flatMap.mp within
  obtain ⟨equation,_,rfl⟩ := List.mem_map.mp within
  exact List.mem_map.mpr ⟨output,present,rfl⟩

theorem output_overlap_iff (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles) (high : 7 ≤ purpose)
    (outside : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources plan.packet.context.state)
    (targets : ∀ output ∈ requests state root,
      fresh plan.packet.context.state.seed invocation declaration purpose owner position ≠ output.target) :
    fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ outputSources state root plan ↔
    ∃ entry ∈ (outputSchema state root plan).variables, entry.mode = .actual ∧
      fresh plan.packet.context.state.seed invocation declaration purpose owner position = plan.binder entry.name := by
  have roots := output_roots state root plan
  have excluded name (member : name ∈ (requests state root).map (·.target)) :
      fresh plan.packet.context.state.seed invocation declaration purpose owner position ≠ name := by
    obtain ⟨output,present,rfl⟩ := List.mem_map.mp member
    exact targets output present
  constructor
  · intro member
    rcases List.mem_append.mp member with schema | target
    · generalize equal : fresh plan.packet.context.state.seed invocation declaration purpose owner position = name at schema
      have source := (GeneralNominalSupportProvenance182.schema_iff plan _ _).mp schema
      cases source with
      | test entry present => exact False.elim (excluded _ (roots.1 entry present) equal)
      | useSource entry present source =>
        cases source with
        | origin => exact False.elim (excluded _ (roots.2 entry present) equal)
        | binder actual => exact ⟨entry,present,actual,rfl⟩
        | output nonactual =>
          exact False.elim (GeneralNominalRawSupport183.capture_output_separate plan.packet high entry.name equal)
        | lower nonactual =>
          exact False.elim ((GeneralNominalRawSupport183.capture_inputs_separate plan.packet high outside entry.name).1 equal)
        | upper nonactual =>
          exact False.elim ((GeneralNominalRawSupport183.capture_inputs_separate plan.packet high outside entry.name).2 equal)
    · exact False.elim (excluded _ target rfl)
  · rintro ⟨entry,present,actual,equal⟩
    apply List.mem_append_left
    rw [equal]
    exact (GeneralNominalSupportProvenance182.schema_iff plan _ _).mpr
      (.useSource entry present (.binder actual))

theorem output_overlap_readback (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles) (high : 7 ≤ purpose)
    (outside : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources plan.packet.context.state)
    (targets : ∀ output ∈ requests state root,
      fresh plan.packet.context.state.seed invocation declaration purpose owner position ≠ output.target)
    (overlap : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∈ outputSources state root plan) :
    ∃ entry ∈ (outputSchema state root plan).variables, entry.mode = .actual ∧
      fresh plan.packet.context.state.seed invocation declaration purpose owner position = plan.binder entry.name ∧
      ∀ model : Assignment, OutputEquations state root plan model →
        GeneralNominalOriginTerms.Same model entry.origin
          (.source (fresh plan.packet.context.state.seed invocation declaration purpose owner position)) := by
  obtain ⟨entry,present,actual,equal⟩ := (output_overlap_iff state root plan high outside targets).mp overlap
  refine ⟨entry,present,actual,equal,?_⟩
  intro model valid
  rw [equal]
  simpa only [actual,ite_true] using valid.1.2 entry present

end Yulang.GeneralNominalHeadOutputSupport185
