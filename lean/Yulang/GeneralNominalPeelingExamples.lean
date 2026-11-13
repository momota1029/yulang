import Yulang.GeneralNominalPeelingAccessibility
import Yulang.GeneralNominalHierarchyExamples

/-! Recursive Display has unconditional accessibility on the real source
fixture. Its first actual-inspection transition is the existing certified
installation, with its emitted child and all later observations retained. -/
namespace Yulang.GeneralNominalPeelingExamples
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalSaturationState
open GeneralNominalPeelingOrigins GeneralNominalPeelingAccessibility
open GeneralDeclarationExamples (roles display displayChild)
open GeneralNominalExamples (registry context displayRoot)
open GeneralNominalActualInspectionSteps (Step)
open CommonNominalFullCarrier

def active (role : Nat) : Prop := role = 0

theorem peeling (snapshot : GeneralNominalCandidates.Context)
    (constructors : snapshot.state.constructors = GeneralDeclarationExamples.constructors)
    (interpretation : snapshot.interpretation = GeneralNominalExamples.interpretation) :
    Peeling roles registry snapshot active 0 := by
  constructor
  · intro role live; cases live; rfl
  · intro declaration visible live nonempty
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl | rfl
    · exact False.elim (nonempty rfl)
    · refine ⟨0,?_,?_⟩
      · simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
          GeneralNominalInspection.translate,constructors,interpretation,GeneralNominalExamples.interpretation]
      · intro clause present
        cases List.mem_singleton.mp present
        exact ⟨rfl,rfl⟩
    · cases live

theorem nominal_congr (equal : Equivalent a b) (name : Nat) :
    Equivalent (nominal name [.inl a]) (nominal name [.inl b]) := by
  have below (a b : Ty) (same : Equivalent a b) : Subtype (nominal name [.inl a]) (nominal name [.inl b]) := by
    apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,rfl,?_⟩
    intro index one two left right
    cases index with
    | zero => cases Option.some.inj left; cases Option.some.inj right; exact same
    | succ index => cases left
  exact ⟨below a b equal,below b a ⟨equal.2,equal.1⟩⟩

theorem ground (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (context true).state model) :
    Equivalent (model 0).1 (tower 0 .int 1) := by
  have parent := (GeneralNominalState.denotes_singleton_exact (GeneralNominalExamples.base true) model (0 : Fin 2) (1 : Fin 2)
    GeneralNominalExamples.listDescriptor rfl).mp (valid.2.1 0 _ rfl)
  have scalar := GeneralNominalState.normalized_models (context true).state model valid (1 : Fin 2) (.base .int) rfl
  have lifted := nominal_congr scalar 0
  exact ⟨subtype_trans parent.1 lifted.1,subtype_trans lifted.2 parent.2⟩

theorem point_source : GeneralNominalActualBudget.PointSource (context true) displayRoot :=
  ⟨GeneralNominalHierarchyExamples.point_source.intervals,
    GeneralNominalHierarchyExamples.point_source.nominalTypes,
    GeneralNominalHierarchyExamples.point_source.nominalRows,by intro index; rfl⟩

theorem depth_bound : GeneralNominalInvocationAncestry.InstalledDepthBound registry (context true) displayRoot 1 :=
  installed_depth_bound (peeling (context true) rfl rfl)
    GeneralDictionarySupportRecursiveExample.initial_source rfl (by rfl) ground

theorem display_accessible : Acc (fun next current => Step registry displayRoot current next)
    (GeneralNominalSupport.initial (context true) displayRoot) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound GeneralNominalExamples.registry_checked
    GeneralDictionarySupportRecursiveExample.initial_source depth_bound

theorem after_display_accessible : Acc (fun next current => Step registry displayRoot current next)
    GeneralDictionarySharedDisplayInstallation.after :=
  display_accessible.inv GeneralNominalActualInspectionExamples.display_step

theorem real_recursive_step :
    Step registry displayRoot (GeneralNominalSupport.initial (context true) displayRoot)
      GeneralDictionarySharedDisplayInstallation.after ∧
    (GeneralNominalSharedExamples.packet false).children = [GeneralNominalExamples.displayChild] :=
  ⟨GeneralNominalActualInspectionExamples.display_step,GeneralDictionarySharedDisplayInstallation.children⟩

end Yulang.GeneralNominalPeelingExamples
