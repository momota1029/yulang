import Yulang.GeneralDictionaryVariableRegistryIntervals
import Yulang.GeneralNominalValueExamples

/-! Nonroot regression: the actual shared-output P installation generates three
variable-input children. Interval formation applies to those emitted demands,
not to an assumed child or a manually installed semantic ordering fact. -/
namespace Yulang.GeneralDictionaryGeneratedIntervalExample
open GeneralNominalSupportSiblings
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState GeneralNominalSupport GeneralSourceDictionaries
open GeneralDictionaryCapturedChildIntervals GeneralDictionaryGeneratedIntervals

theorem capture_bindings : pk.bindings = [(0,(1,1))] := by
  unfold Packet.bindings
  rw [p_report]
  rfl

theorem variable_inputs : VariableInputs pk := by
  intro clause member signature index
  change clause ∈ [cp,wp,pp] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    refine ⟨0,?_⟩
    simp [cp,wp,pp,GeneralDeclarationPatterns.normalize]

theorem registry_fragment : GeneralDictionaryVariableRegistryIntervals.VariableRegistry reg := by
  intro declaration visible clause declared pattern present
  change declaration ∈ [p,c,GeneralDeclarationExamples.wrap] at visible
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · change clause ∈ [cp,wp,pp] at declared
    simp only [List.mem_cons,List.not_mem_nil,or_false] at declared
    rcases declared with rfl | rfl | rfl
    all_goals
      have same : pattern = .var 0 := List.mem_singleton.mp present
      subst pattern
      exact ⟨0,rfl⟩
  · cases declared
  · have same : clause = GeneralDeclarationExamples.containerChild := List.mem_singleton.mp declared
    subst clause
    have same : pattern = .var 0 := List.mem_singleton.mp present
    subst pattern
    exact ⟨0,rfl⟩

theorem journal : VariableJournal afterP := by
  intro packet member
  have same : packet = pk := List.mem_singleton.mp member
  subst packet
  exact variable_inputs

theorem reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) reg root afterP :=
  ⟨start,⟨ctx,initial_source,rfl⟩,.tail .refl GeneralNominalValueExamples.p_first_step⟩

theorem nonroot : kidC ≠ root := by
  intro equal
  have role := congrArg (fun (occurrence : Occurrence roles) => occurrence.demand.role) equal
  change 2 = 0 at role
  cases role

theorem every_generated_interval (child : Occurrence roles) (generated : Generated afterP.current root child)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models afterP.current model) (index) :
    CommonNominalFullCarrier.Subtype (model (child.demand.arguments index).1).1
      (model (child.demand.arguments index).2).1 :=
  generated_intervals reachable journal generated model valid index

theorem positive_model : Models afterP.current (GeneralNominalOutputGrowth.finiteModel 1) := by
  apply (GeneralNominalFeedbackSites.install_models _ _ _ rfl _).mpr
  have valid := (GeneralNominalOutputGrowthModels.source_models 1 _).mpr
    (GeneralNominalOutputGrowth.finite_prefix_models 1)
  exact ⟨(initial_models ..).mpr valid,p_branch _ valid⟩

theorem actual_nonroot_intervals :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) reg root afterP ∧
    Generated afterP.current root kidC ∧ kidC ≠ root ∧
    ∃ model, Models afterP.current model ∧ ∀ index,
      CommonNominalFullCarrier.Subtype (model (kidC.demand.arguments index).1).1
        (model (kidC.demand.arguments index).2).1 :=
  ⟨reachable,children_generated.1,nonroot,_,positive_model,
    fun index => every_generated_interval kidC children_generated.1 _ positive_model index⟩

end Yulang.GeneralDictionaryGeneratedIntervalExample
