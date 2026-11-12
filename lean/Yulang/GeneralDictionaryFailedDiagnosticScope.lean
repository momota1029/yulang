import Yulang.GeneralDictionaryEarlyMergeClosure
import Yulang.GeneralDictionaryEarlyMergeNoEvidence
import Yulang.B4SkeletonV5

/-! The stable failed-child diagnostic is not an EvidenceNode counterexample.
We prove the node implication at every root/generated demand of this *fixed*
reachable snapshot. At its selected parent the child-evidence premise is false;
at its rejected children the selected premise is false. This does not prove
EvidenceNode at arbitrary reachable snapshots and does not produce a dictionary.
-/
namespace Yulang.GeneralDictionaryFailedDiagnosticScope
open GeneralDictionaryEarlyMergeExample GeneralDictionaryEarlyMergeDiagnostics
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (displayRoot)
open CommonRoleOutermostResolver
abbrev b := GeneralNominalSupportBoundary.boundary roles

/-- The completed-success premise of DictionarySound is absent here, despite
Local selecting the parent and the full diagnostic retaining failed children. -/
theorem no_selected_classification (dictionary : Dictionary) :
    ¬ B4TargetV3.Classify b.toSourceBoundary registry finish displayRoot (.selected dictionary) :=
  root_no_classify (.selected dictionary)

/-- Neither of the actual selected parent's children has semantic Evidence,
so no list can meet the recursive premise of EvidenceNode. -/
theorem no_children_evidence (model : GeneralNominalCommonBridge.Assignment)
    (dictionaries : List Dictionary) :
    ¬ All₂ (fun child dictionary => b.Evidence registry finish model child dictionary)
      children dictionaries := by
  intro all
  rw [children_exact] at all
  cases all with
  | cons first rest => exact GeneralDictionaryEarlyMergeNoEvidence.child_no_evidence 10 model _ first

/-- The exact local implication used by V5 EvidenceNode holds at this fixed
failed snapshot, for every model and every root/generated focus. Stability,
reachability and model premises can be added without changing this result. -/
theorem node_at_failed_snapshot (model : GeneralNominalCommonBridge.Assignment)
    (focus : GeneralSourceDictionaries.Occurrence roles) (key : Nat)
    (kids : List (GeneralSourceDictionaries.Occurrence roles))
    (dictionaries : List Dictionary)
    (reached : focus = displayRoot ∨ b.Generated registry finish displayRoot focus)
    (safe : B4Target.SafeKnown b.toSourceBoundary registry finish focus)
    (unique : B4Target.Unique b.toSourceBoundary registry finish focus key kids)
    (all : All₂ (fun child dictionary => b.Evidence registry finish model child dictionary)
      kids dictionaries) : b.Evidence registry finish model focus (.node key dictionaries) := by
  have selected := (GeneralNominalSupportBoundary.local_correspondence registry finish focus _).mp
    (B4TargetV3.Local.selected safe unique)
  have casesFocus : focus = displayRoot ∨ focus = child 10 ∨ focus = child 11 := by
    rcases reached with same | generated
    · exact Or.inl same
    · exact GeneralDictionaryEarlyMergeClosure.generated_cases focus generated
  rcases casesFocus with rfl | rfl | rfl
  · have same := GeneralNominalLocalBoundary.local_functional selected supported_parent
    have eq : kids = children := by cases same; rfl
    rw [eq] at all
    exact False.elim (no_children_evidence model dictionaries all)
  · have impossible := GeneralNominalLocalBoundary.local_functional selected (supported_child 10)
    cases impossible
  · have impossible := GeneralNominalLocalBoundary.local_functional selected (supported_child 11)
    cases impossible
end Yulang.GeneralDictionaryFailedDiagnosticScope
