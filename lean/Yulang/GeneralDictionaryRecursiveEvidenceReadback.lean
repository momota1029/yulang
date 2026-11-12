import Yulang.GeneralDictionaryRecursiveEvidence
import Yulang.GeneralDictionaryRecursiveReadback

/-!
# Exact computed readback of recursive source evidence

The source-instance judgment, not candidate selection, determines the declaration,
capture frame and complete child list. Thus model-indexed evidence reconstructs
one fixed source tree from its runtime payload. This is a representation theorem;
it does not establish evidence in any additional model.
-/
namespace Yulang.GeneralDictionaryRecursiveEvidence

open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryReadback (Payload)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryRecursiveReadback (frames reconstruct)

/-- The complete source child list agrees with the frame computed solely from
the registry, source context, occurrence and payload key. -/
theorem instance_plan (registry : Registry) (checked : Checked registry) (context : Context)
    (model : Assignment) (root : Occurrence registry.roles) (key : Nat)
    (children : List (Occurrence registry.roles))
    (instanceRule : Instance registry context model root key children) :
    GeneralDictionaryEmissionPlans.Plan registry checked (frames registry context root) root key children := by
  obtain ⟨selected, visible, selectedChecked, identity, role, bounds, located, _, _, emitted, _⟩ := instanceRule
  refine ⟨selected, visible, identity, role, ?_⟩
  rw [emitted]
  have found := GeneralDictionaryRecursiveReadback.bindings_found registry checked context root
    selected.id selected visible rfl role bounds located
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
  simp only [frames, GeneralDictionaryRecursiveReadback.frame, GeneralNominalAllocation.frame]
  rw [found]
  rfl

/-- The semantic instance determines the same children in any two models. There
is no claim that an instance in one model is also valid in the other. -/
theorem instance_children_functional (registry : Registry) (checked : Checked registry)
    (context : Context) (firstModel lastModel : Assignment) (root : Occurrence roles)
    (key : Nat) (first last : List (Occurrence roles))
    (one : Instance registry context firstModel root key first)
    (two : Instance registry context lastModel root key last) : first = last := by
  obtain ⟨a, av, ac, ak, _, ab, al, _, _, ae, _⟩ := one
  obtain ⟨b, bv, bc, bk, _, bb, bl, _, _, be, _⟩ := two
  have equal := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked
    a b av bv (ak.trans bk.symm)
  subst b
  have same := Option.some.inj (al.symm.trans bl)
  subst bb
  exact ae.trans be.symm

/-- Actual source equations retain a reconstructible source-indexed tree. -/
theorem indexed_plan (registry : Registry) (checked : Checked registry) (context : Context)
    (model : Assignment) (tree : GeneralSourceDictionaries.Dictionary registry.roles)
    (evidence : GeneralSourceDictionaries.Evidence (Instance registry context model) tree) :
    GeneralSourceDictionaries.Evidence
      (GeneralDictionaryPayloadReconstruction.Rule registry checked (frames registry context)) tree :=
  GeneralSourceDictionaries.evidence_mono _ _ (instance_plan registry checked context model) evidence

/-- The existing payload reconstruction is complete for model-indexed source
evidence, independently of all Survivor derivations. -/
theorem reconstruct_evidence (registry : Registry) (checked : Checked registry) (context : Context)
    (model : Assignment) (tree : GeneralSourceDictionaries.Dictionary registry.roles)
    (evidence : GeneralSourceDictionaries.Evidence (Instance registry context model) tree) :
    reconstruct registry checked context (erase tree) tree.root = some tree :=
  GeneralDictionaryPayloadReconstruction.reconstruct_complete registry checked (frames registry context)
    tree (indexed_plan registry checked context model tree evidence)

/-- The evidence witness is exactly the tree returned by the computed readback. -/
theorem evidence_readback (registry : Registry) (checked : Checked registry) (context : Context)
    (model : Assignment) (root : Occurrence registry.roles) (payload : Payload)
    (evidence : Evidence registry context model root payload) :
    ∃ tree, reconstruct registry checked context payload root = some tree ∧
      Readback root payload tree ∧
      GeneralSourceDictionaries.Evidence (Instance registry context model) tree := by
  obtain ⟨tree, readback, indexed⟩ := evidence
  refine ⟨tree, ?_, readback, indexed⟩
  rw [← readback.1, ← readback.2]
  exact reconstruct_evidence registry checked context model tree indexed

/-- A fixed source witness serves every model in which this payload already has
source evidence. The quantifier does not claim all state models have evidence. -/
theorem evidence_fixed_readback (registry : Registry) (checked : Checked registry) (context : Context)
    (model : Assignment) (root : Occurrence registry.roles) (payload : Payload)
    (evidence : Evidence registry context model root payload) :
    ∃ tree, reconstruct registry checked context payload root = some tree ∧
      Readback root payload tree ∧
      GeneralSourceDictionaries.Evidence (Instance registry context model) tree ∧
      ∀ otherModel, Evidence registry context otherModel root payload →
        GeneralSourceDictionaries.Evidence (Instance registry context otherModel) tree := by
  obtain ⟨tree, reconstructed, readback, indexed⟩ := evidence_readback registry checked context model root payload evidence
  refine ⟨tree, reconstructed, readback, indexed, ?_⟩
  intro otherModel otherEvidence
  obtain ⟨other, otherReconstructed, _, otherIndexed⟩ :=
    evidence_readback registry checked context otherModel root payload otherEvidence
  have same := Option.some.inj (reconstructed.symm.trans otherReconstructed)
  subst other
  exact otherIndexed

end Yulang.GeneralDictionaryRecursiveEvidence
