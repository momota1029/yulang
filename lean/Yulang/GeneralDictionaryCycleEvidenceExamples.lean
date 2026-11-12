import Yulang.GeneralDictionaryCycleEvidenceGap

/-! A nonvacuous stable initial journal instantiates the cycle evidence rule.
The wrapper list is off-cycle although its record argument is cyclic. Its len
instance has no where children or requested outputs. This is a source-backed
example, not a general executor or a general reachability invariant. -/
namespace Yulang.GeneralDictionaryCycleEvidenceExamples

open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveExamples (len lenRegistry lenRoot len_checked)
open GeneralNominalCycleWrapper (context state model state_models)
open GeneralNominalSaturationState GeneralNominalCycleSteps
open GeneralNominalRecursiveCandidates
open GeneralNominalDemandMerging (pointSite)

abbrev journal : State roles := initial context lenRoot

private theorem query : GeneralNominalInspection.queries state context.interpretation len =
    [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

private theorem schema : generated lenRegistry context lenRoot len len_checked [(1,1)] = {} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    len,List.mergeSort_nil]
  rfl

theorem every_branch (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) :
    BranchModels lenRegistry context lenRoot len len_checked [(1,1)] assignment := by
  have head := GeneralNominalUnaryCaptureFacts.private_models context lenRegistry lenRoot len 1
    GeneralNominalCycleWrapper.descriptor rfl 0 rfl (0,0) rfl query assignment valid
  refine ⟨head.1,head.2,?_⟩
  rw [schema]
  exact GeneralNominalMaterialization.empty_models ..

theorem prepared : Prepared lenRegistry context lenRoot len len_checked := by
  obtain ⟨_,declaration,visible,checked,_,_,_,_,prepared,_⟩ :=
    GeneralNominalCycleRegressions.wrapper_len_survivor
  have same := List.mem_singleton.mp visible
  subst declaration
  exact prepared

theorem joint : GeneralNominalJointCandidates.Joint lenRegistry journal lenRoot 30 :=
  GeneralNominalJointCandidates.initial_joint lenRegistry context lenRoot len (by simp) len_checked rfl
    [(1,1)] (by decide +kernel) prepared model (every_branch model state_models)

theorem generated_only_root (child : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated journal lenRoot child) : child = lenRoot := by
  induction generated with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    have same := List.mem_singleton.mp member
    exact congrArg GeneralNominalDemandMerging.Site.occurrence same

/-- All installable packets at this terminal root are already committed. -/
theorem installable_committed (packet : Packet roles) (same : packet.site.occurrence = lenRoot)
    (enabled : Installable lenRegistry journal packet) : Committed journal packet := by
  rcases packet with ⟨registry,ctx,site,declaration,checked,bounds⟩
  have reg := enabled.1
  have ctxt := enabled.2.1
  have visible := enabled.2.2.2.1
  have found := enabled.2.2.2.2.2.1
  dsimp only at reg ctxt visible found same
  subst registry
  change ctx = context at ctxt
  subst ctx
  have decl := List.mem_singleton.mp visible
  subst declaration
  rw [same] at found
  have located : arguments context lenRoot = some [(1,1)] := by decide +kernel
  have equal := Option.some.inj (located.symm.trans found)
  subst bounds
  constructor
  · intro assignment valid
    change BranchModels lenRegistry context site.occurrence len checked [(1,1)] assignment
    rw [same]
    exact every_branch assignment valid.1
  · intro child member
    change child ∈ GeneralNominalAllocation.children _ _ _ _ _ _ at member
    unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit at member
    simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
      len,GeneralDeclarationDemands.emitAll] at member
    obtain ⟨clause,present,_⟩ := member
    cases present

theorem stable : Stable lenRegistry journal lenRoot := by
  intro focus generated
  have same := generated_only_root focus generated
  subst focus
  refine ⟨?_,?_,?_,?_⟩
  · intro _
    exact ⟨pointSite lenRoot,List.mem_singleton_self _,rfl⟩
  · exact installable_committed
  · intro first one _ last two _
    have sameFirst := List.mem_singleton.mp one
    have sameLast := List.mem_singleton.mp two
    rw [sameFirst,sameLast]
    exact .refl _
  · intro _ _ source member _
    exact GeneralDictionaryCycleEvidenceGap.all_sources_known source member

theorem journal_model : Models journal model :=
  (initial_models context lenRoot model).mpr state_models

/-- The positive conditional node lemma has an actual stable, jointly selected
source instance and a nonempty model class. -/
theorem evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models journal assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence lenRegistry journal.context assignment lenRoot (.node 30 []) :=
  GeneralDictionaryCycleEvidence.stable_joint_evidence lenRegistry journal lenRoot 30 [] stable
    GeneralNominalCycleRegressions.wrapper_len_selected joint assignment valid [] .nil

theorem nonvacuous_stable_evidence :
    Stable lenRegistry journal lenRoot ∧ GeneralNominalJointCandidates.Joint lenRegistry journal lenRoot 30 ∧
    Models journal model ∧
    GeneralDictionaryRecursiveEvidence.Evidence lenRegistry journal.context model lenRoot (.node 30 []) :=
  ⟨stable,joint,journal_model,evidence model journal_model⟩

end Yulang.GeneralDictionaryCycleEvidenceExamples
