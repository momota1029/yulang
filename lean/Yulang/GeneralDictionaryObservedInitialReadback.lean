import Yulang.GeneralDictionaryObservedInitialInstallation

/-! The actual where child is retained; the singleton example registry intentionally
has no declaration for its role. Parent selection/install is not whole-tree success. -/
namespace Yulang.GeneralDictionaryObservedInitialReadback
open GeneralDictionaryObservedInitialExample GeneralDictionaryObservedInitialInstallation
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence
open GeneralNominalExamples (model)
open GeneralDeclarationExamples (roles displayChild)

abbrev captures := bindings source (report context declaration [(0,0)])
abbrev frame : GeneralDictionaryEmissionPlans.Frame roles := GeneralNominalAllocation.frame source registry root.identity captures
abbrev child := GeneralDictionaryEmissionPlans.occurrence frame
  (GeneralDeclarationDemands.emit root.identity declaration displayChild
    (checked.signature.2.2.2 displayChild (List.mem_singleton_self _))
    (frame.capture declaration.id) (frame.allocation declaration.id displayChild))

theorem children_exact : children = [child] := by
  have canonical : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by decide +kernel
  simp only [children,GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
    GeneralCanonicalChildOrder.canonicalEmit,canonical]
  rfl

theorem child_role : child.demand.role = 0 := rfl

theorem no_child_instance (snapshot : GeneralNominalCandidates.Context)
    (assignment : GeneralNominalCommonBridge.Assignment) (key : Nat)
    (descendants : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ Instance registry snapshot assignment child key descendants := by
  rintro ⟨decl,visible,_,_,role,_⟩
  have same := List.mem_singleton.mp visible
  subst decl
  cases role

theorem no_child_evidence (snapshot : GeneralNominalCandidates.Context)
    (assignment : GeneralNominalCommonBridge.Assignment) (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence registry snapshot assignment child payload := by
  cases payload with
  | node key dictionaries =>
    intro evidence
    obtain ⟨descendants,instanceRule,_⟩ := evidence_node_elim registry snapshot assignment child key dictionaries evidence
    exact no_child_instance snapshot assignment key descendants instanceRule

theorem installed_models : GeneralNominalSaturationState.Models installed.current model := by
  apply (GeneralNominalFeedbackSites.install_models start.current packet _ rfl model).mpr
  exact ⟨GeneralDictionaryObservedInitialExample.initial_models,every_source_model model source_models⟩

/-- Reachability and inhabited installed Models do not supply the missing child's
source declaration. This is a diagnostic fixture, not a counterexample to V5. -/
theorem reachable_inhabited_missing_child :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root installed ∧
    GeneralNominalSaturationState.Models installed.current model ∧
    ∀ payload, ¬ Evidence registry installed.current.context model child payload :=
  ⟨installed_reachable,installed_models,no_child_evidence installed.current.context model⟩
end Yulang.GeneralDictionaryObservedInitialReadback
