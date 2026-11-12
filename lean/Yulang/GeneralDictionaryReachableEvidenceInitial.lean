import Yulang.GeneralDictionaryFeedbackEvidence

/-! The zero-step case of I-25 has no recorded-choice or alias obstruction.
The current survivor itself supplies Joint in the empty initial journal.
This is not the general reachable-state EvidenceNode bridge: installations,
merges, and arbitrary view-changing refreshes still need an inductive proof. -/
namespace Yulang.GeneralDictionaryReachableEvidenceInitial
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps
open GeneralNominalRecursiveCandidates
open GeneralDictionaryReadback (Payload)

/-- At the actual initial snapshot, one genuine survivor supplies all Joint
conditions. Its branch model is also a model of the empty journal. -/
theorem initial_survivor_joint (registry : Registry) (context : Context)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (survivor : Survivor registry context root key children) :
    GeneralNominalJointCandidates.Joint registry (initial context root) root key := by
  obtain ⟨pending,declaration,visible,checked,identity,role,bounds,located,prepared,emitted⟩ := survivor
  obtain ⟨stored,storedLocated,finished,ready,model,branch⟩ := prepared.2.2.2
  have same : stored = bounds := Option.some.inj (storedLocated.symm.trans located)
  subst stored
  rw [← identity]
  exact GeneralNominalJointCandidates.initial_joint registry context root declaration visible checked
    role bounds located prepared model branch

/-- Stable selection at a genuine empty journal admits the exact current
source instance in every model; no Joint assumption is supplied by the caller. -/
theorem stable_initial_instance (registry : Registry) (context : Context)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry (initial context root) root)
    (selected : GeneralNominalFeedbackK2.Local registry (initial context root) root (.selected key children)) :
    (∀ model, Models (initial context root) model →
      GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) ∧
    ∀ child ∈ children, Generated (initial context root) root child := by
  have survivor : Survivor registry context root key children := by
    cases selected with | selected safe unique => exact unique.1
  exact GeneralDictionaryFeedbackEvidence.stable_joint_instance registry (initial context root)
    root key children stable selected (initial_survivor_joint registry context root key children survivor)

/-- The base reachable state has full parent-node evidence from same-model
child witnesses. Child stability is not needed in this narrower result. -/
theorem stable_initial_evidence (registry : Registry) (context : Context)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry (initial context root) root)
    (selected : GeneralNominalFeedbackK2.Local registry (initial context root) root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models (initial context root) model)
    (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node key dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry context model root key children dictionaries
    ((stable_initial_instance registry context root key children stable selected).1 model valid) given

/-- Stability of a selected empty-journal root forces terminal selection.
Otherwise the first child edge would still be a novel installation. -/
theorem stable_initial_children_nil (registry : Registry) (context : Context)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry (initial context root) root)
    (selected : GeneralNominalFeedbackK2.Local registry (initial context root) root (.selected key children)) :
    children = [] := by
  have survivor : Survivor registry context root key children := by
    cases selected with | selected safe unique => exact unique.1
  obtain ⟨packet,registrySame,contextSame,rootSame,keySame,childrenSame,enabled,committed⟩ :=
    GeneralDictionaryFeedbackEvidence.stable_joint_packet registry (initial context root)
      root key children stable selected (initial_survivor_joint registry context root key children survivor)
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro child member
  have edge := committed.2 child (by simpa only [childrenSame] using member)
  cases edge

/-- A selected initial root with a nonempty where list cannot already be stable. -/
theorem nonterminal_initial_not_stable (registry : Registry) (context : Context)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry (initial context root) root (.selected key children))
    (nonempty : children ≠ []) : ¬ Stable registry (initial context root) root :=
  fun stable => nonempty (stable_initial_children_nil registry context root key children stable selected)

/-- All stable selected initial roots therefore have a model-independent
terminal dictionary. This is still only the zero-step case, not an induction
through arbitrary reachable states. -/
theorem stable_initial_terminal_evidence (registry : Registry) (context : Context)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry (initial context root) root)
    (selected : GeneralNominalFeedbackK2.Local registry (initial context root) root (.selected key children)) :
    children = [] ∧ ∀ model, Models (initial context root) model →
      GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node key []) := by
  have empty := stable_initial_children_nil registry context root key children stable selected
  subst children
  exact ⟨rfl, fun model valid => stable_initial_evidence registry context root key [] stable selected
    model valid [] .nil⟩

end Yulang.GeneralDictionaryReachableEvidenceInitial
