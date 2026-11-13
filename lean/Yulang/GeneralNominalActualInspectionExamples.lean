import Yulang.GeneralNominalActualInspectionSteps
import Yulang.GeneralDictionarySharedDisplayInstallation

/-! The actual-position guard preserves the Display and Wrap source
certificates, including Display's real installation and emitted child. -/
namespace Yulang.GeneralNominalActualInspectionExamples
open GeneralDeclarations GeneralNominalSaturationState GeneralNominalRecursiveInspection
open GeneralNominalActualInspectionSteps GeneralNominalSharedExamples
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (registry context displayRoot wrapRoot)

abbrev start (wrapping : Bool) :=
  GeneralNominalSupport.initial (context true) (packet wrapping).site.occurrence
abbrev alternative (wrapping : Bool) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) : Packet roles :=
  ⟨registry,context true,(packet wrapping).site,declaration,checked,[(0,0)]⟩

theorem recovered (wrapping : Bool) :
    (GeneralNominalFeedbackSites.recover (start wrapping).current (packet wrapping).site).inputs = [some (.source 0)] := by
  cases wrapping <;> simp [GeneralNominalFeedbackSites.recover,GeneralNominalFeedbackSites.recoverOrigin,
    packet,GeneralNominalDemandMerging.pointSite,List.ofFn_succ,displayRoot,wrapRoot,
    GeneralNominalExamples.displayDemand,GeneralNominalExamples.wrapDemand,
    roles,GeneralDeclarationExamples.bareRole,GeneralDeclarationExamples.outputRole]

theorem reports (wrapping : Bool) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) (member : declaration ∈ registry.declarations) :
    (inspection (start wrapping).current (alternative wrapping declaration checked)).inspected = [(0,0)] ∧
      (inspection (start wrapping).current (alternative wrapping declaration checked)).tests.map Prod.fst = [.source 0] := by
  unfold inspection
  change (inspectMany _ _ _ (fun index => ((GeneralNominalFeedbackSites.recover
      (start wrapping).current (packet wrapping).site).inputs[index]?).join) 0).inspected = _ ∧ _
  rw [recovered]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> cases wrapping <;> cbv
  all_goals exact ⟨rfl,trivial⟩

theorem acyclic (wrapping : Bool) (identity : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle (start wrapping).current identity := by
  apply GeneralNominalOutputGrowthModels.feedback_acyclic _ GeneralNominalExamples.model
    ((initial_models ..).mpr (GeneralNominalExamples.state_models true))
    (fun source => if source = 0 then 1 else 0)
  · intro source
    by_cases zero : source = 0 <;>
      simp [zero,GeneralNominalOutputGrowth.tower] <;> rfl
  · rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩
    exact Fin.elim0 kind

theorem safe_alternative (wrapping : Bool) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) (member : declaration ∈ registry.declarations) :
    Safe (start wrapping).current (alternative wrapping declaration checked) := by
  have computed := reports wrapping declaration checked member
  constructor
  · rw [computed.1]
    simpa only [List.length_map,List.length_cons,List.length_nil] using (congrArg List.length computed.2).symm
  · intro entry present
    have member : entry.1 ∈ (inspection (start wrapping).current
        (alternative wrapping declaration checked)).tests.map Prod.fst :=
      List.mem_map.mpr ⟨entry,present,rfl⟩
    rw [computed.2] at member
    have same := List.mem_singleton.mp member
    rw [same]
    constructor
    · refine ⟨0,?_,GeneralNominalDemandMerging.source_same _ 0⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_ofFn.mpr ⟨(0 : Fin 2),rfl⟩)))
    · rintro ⟨identity,_,cycle,_⟩
      exact acyclic wrapping identity cycle

theorem safe_selected (wrapping : Bool) : Safe (start wrapping).current (packet wrapping) := by
  cases wrapping
  · exact safe_alternative false GeneralDeclarationExamples.display GeneralDeclarationExamples.display_checked (by simp)
  · exact safe_alternative true GeneralDeclarationExamples.wrap GeneralDeclarationExamples.wrap_checked (by simp)

theorem alternatives_safe (wrapping : Bool) :
    AlternativesSafe registry (start wrapping).current (packet wrapping).site := by
  intro declaration member checked role ready bounds located
  have exactBounds : GeneralNominalRecursiveCandidates.arguments (context true) (packet wrapping).site.occurrence =
      some [(0,0)] := by cases wrapping <;> rfl
  have same := Option.some.inj (located.symm.trans exactBounds)
  subst bounds
  exact safe_alternative wrapping declaration checked member

theorem display_guard : PacketGuard (start false) (packet false) [] :=
  ⟨GeneralNominalSharedExamples.display_guard,safe_selected false,alternatives_safe false⟩

theorem wrap_guard : PacketGuard (start true) (packet true) [] :=
  ⟨GeneralNominalSharedExamples.wrap_guard,safe_selected true,alternatives_safe true⟩

theorem display_step : Step registry displayRoot GeneralDictionarySharedDisplayInstallation.start
    GeneralDictionarySharedDisplayInstallation.after :=
  ⟨displayRoot,.root,.install (packet false) [] GeneralDictionarySharedDisplayInstallation.installable
    GeneralDictionarySharedDisplayInstallation.novel display_guard⟩

end Yulang.GeneralNominalActualInspectionExamples
