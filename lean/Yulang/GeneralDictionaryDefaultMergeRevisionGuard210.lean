import Yulang.GeneralDictionaryDefaultMergeRevisionProbe210
import Yulang.GeneralNominalCenteredHeadCandidates

/-! The raw candidate guard already rejects a uniformly inconsistent repeat
capture. The local probe alone is therefore not an EvidenceNode refutation. -/
namespace Yulang.GeneralDictionaryDefaultMergeRevisionGuard210
open GeneralDeclarations GeneralNominalAllocation
open GeneralDictionaryDefaultMergeRevisionProbe210
open GeneralNominalCenteredHeadCandidates
open GeneralNominalRecursiveInspection
open PresenceNormalForm (All)
variable {upper : Nat} {roles : Roles.RoleDecls} {root : GeneralSourceDictionaries.Occurrence roles}

 theorem head_models_excluded
    (named : name ∈ declaration.inputNames)
    (newBindings : bindings context.state
      (GeneralNominalRecursiveCandidates.report context declaration bounds) = twice name last nextUpper)
    (oldRaw : ∀ model, GeneralNominalState.Models context.state model →
      All CommonNominalFullCarrier.model model
        (merges context.state registry root.identity declaration (twice name first upper)))
    (separated : ∀ model, GeneralNominalState.Models context.state model →
      (model first).1 = .bottom ∧ (model last).1 = .base .int) :
    ¬ ∃ model, HeadModels registry context root declaration bounds model := by
  rintro ⟨model,head⟩
  have localModel := head.1
  unfold GeneralNominalRecursiveCandidates.privateState at localModel
  have propagated := ((GeneralNominalState.extend_models ..).mp localModel).1
  obtain ⟨raw,_,generated⟩ := (GeneralNominalAllocation.propagate_models ..).mp propagated
  rw [newBindings] at generated
  have values := separated model raw
  exact bottom_int_incompatible named values.1 values.2 ⟨oldRaw model raw,generated⟩

 theorem prepared_excluded
    (named : name ∈ declaration.inputNames)
    (located : GeneralNominalRecursiveCandidates.arguments context (inputs root) = some bounds)
    (newBindings : bindings context.state
      (GeneralNominalRecursiveCandidates.report context declaration bounds) = twice name last nextUpper)
    (oldRaw : ∀ model, GeneralNominalState.Models context.state model →
      All CommonNominalFullCarrier.model model
        (merges context.state registry root.identity declaration (twice name first upper)))
    (separated : ∀ model, GeneralNominalState.Models context.state model →
      (model first).1 = .bottom ∧ (model last).1 = .base .int) :
    ¬ Prepared registry context root declaration := by
  rintro ⟨_,_,_,other,found,_,models⟩
  have same := Option.some.inj (found.symm.trans located)
  subst other
  exact head_models_excluded named newBindings oldRaw separated models

end Yulang.GeneralDictionaryDefaultMergeRevisionGuard210
