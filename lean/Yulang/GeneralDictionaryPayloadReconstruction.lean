import Yulang.GeneralDictionaryPlanLookup
import Yulang.GeneralDictionaryTransactions

/-!
# Executable source reconstruction from a raw selected-key dictionary

The root and resolved frames remain inputs. Every descendant occurrence is
computed from its actual checked declaration. The traversal preserves complete
canonical child lists and multiplicity, rejecting both missing and extra payloads.
Failure is structural deferral, not candidate rejection or role unsatisfiability.
-/
namespace Yulang.GeneralDictionaryPayloadReconstruction
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralDictionaryTransactions (Frames)
open GeneralDictionaryEmissionPlans (Plan)

abbrev Rule (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles) :
    LocalInstance registry.roles := fun root => Plan registry checked (frames root) root

mutual
  def reconstruct (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
      (payload : Payload) (root : Occurrence registry.roles) : Option (Dictionary registry.roles) :=
    match payload with
    | .node key children => do
        let demands ← GeneralDictionaryPlanLookup.lookup registry checked (frames root) root key
        let trees ← reconstructChildren registry checked frames children demands
        pure (.node root key trees)
    termination_by sizeOf payload

  def reconstructChildren (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
      (payloads : List Payload) (roots : List (Occurrence registry.roles)) : Option (List (Dictionary registry.roles)) :=
    match payloads, roots with
    | [], [] => some []
    | first :: rest, root :: roots => do
        let tree ← reconstruct registry checked frames first root
        let trees ← reconstructChildren registry checked frames rest roots
        pure (tree :: trees)
    | [], _ :: _ => none
    | _ :: _, [] => none
    termination_by sizeOf payloads
end

mutual
  /-- The computed tree retains its requested root and every raw key/child, and
  every node is justified by an actual checked visible declaration. -/
  theorem reconstruct_sound (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
      (payload : Payload) (root : Occurrence registry.roles) (tree : Dictionary registry.roles)
      (success : reconstruct registry checked frames payload root = some tree) :
      Readback root payload tree ∧ Evidence (Rule registry checked frames) tree := by
    cases payload with
    | node key children =>
      rw [reconstruct] at success
      obtain ⟨demands, found, rest⟩ := Option.bind_eq_some_iff.mp success
      obtain ⟨trees, built, same⟩ := Option.bind_eq_some_iff.mp rest
      cases same
      obtain ⟨roots, erased, evidence⟩ := reconstructChildren_sound registry checked frames children demands trees built
      refine ⟨⟨rfl, ?_⟩, .node ?_ evidence⟩
      · simp only [erase, erased]
      · change Plan registry checked (frames root) root key (trees.map Dictionary.root)
        rw [roots]
        exact (GeneralDictionaryPlanLookup.lookup_exact registry checked (frames root) root key demands).mp found
    termination_by sizeOf payload

  theorem reconstructChildren_sound (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
      (payloads : List Payload) (roots : List (Occurrence registry.roles)) (trees : List (Dictionary registry.roles))
      (success : reconstructChildren registry checked frames payloads roots = some trees) :
      trees.map Dictionary.root = roots ∧ eraseChildren trees = payloads ∧
        ∀ tree ∈ trees, Evidence (Rule registry checked frames) tree := by
    cases payloads with
    | nil =>
      cases roots with
      | nil => rw [reconstructChildren] at success; cases success; exact ⟨rfl, rfl, by simp⟩
      | cons root roots => rw [reconstructChildren] at success; cases success
    | cons first rest =>
      cases roots with
      | nil => rw [reconstructChildren] at success; cases success
      | cons root roots =>
        rw [reconstructChildren] at success
        obtain ⟨tree, found, tail⟩ := Option.bind_eq_some_iff.mp success
        obtain ⟨trees, built, same⟩ := Option.bind_eq_some_iff.mp tail
        cases same
        obtain ⟨⟨oneRoot, oneErase⟩, oneEvidence⟩ := reconstruct_sound registry checked frames first root tree found
        obtain ⟨allRoots, allErased, allEvidence⟩ := reconstructChildren_sound registry checked frames rest roots trees built
        refine ⟨by simp only [List.map_cons, oneRoot, allRoots], ?_, ?_⟩
        · simp only [eraseChildren, oneErase, allErased]
        · intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact oneEvidence
          · exact allEvidence child member
    termination_by sizeOf payloads
end

mutual
  /-- Completeness for actual declaration plans, not head feasibility or full
  source role semantics. No recursive occurrence recipe is supplied. -/
  theorem reconstruct_complete (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
      (tree : Dictionary registry.roles) (evidence : Evidence (Rule registry checked frames) tree) :
      reconstruct registry checked frames (erase tree) tree.root = some tree := by
    cases tree with
    | node root key trees =>
      obtain ⟨plan, allEvidence⟩ := (evidence_node_iff ..).mp evidence
      have found := (GeneralDictionaryPlanLookup.lookup_exact registry checked (frames root) root key _).mpr plan
      change reconstruct registry checked frames (.node key (eraseChildren trees)) root = _
      rw [reconstruct, found]
      change (reconstructChildren registry checked frames (eraseChildren trees) (trees.map Dictionary.root)).bind (fun result => some (Dictionary.node root key result)) = _
      rw [reconstructChildren_complete registry checked frames trees allEvidence]
      rfl
    termination_by sizeOf tree

  theorem reconstructChildren_complete (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
      (trees : List (Dictionary registry.roles)) (evidence : ∀ tree ∈ trees, Evidence (Rule registry checked frames) tree) :
      reconstructChildren registry checked frames (eraseChildren trees) (trees.map Dictionary.root) = some trees := by
    cases trees with
    | nil => simp [eraseChildren, reconstructChildren]
    | cons tree trees =>
      simp only [eraseChildren, List.map_cons, reconstructChildren]
      rw [reconstruct_complete registry checked frames tree (evidence tree (by simp))]
      rw [reconstructChildren_complete registry checked frames trees
        (fun child member => evidence child (List.mem_cons_of_mem _ member))]
      rfl
    termination_by sizeOf trees
end

/-- Exact executable reconstruction against the pre-existing independent
source-indexed relation, including full child order and multiplicity. -/
theorem reconstruct_exact (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
    (payload : Payload) (root : Occurrence registry.roles) (tree : Dictionary registry.roles) :
    reconstruct registry checked frames payload root = some tree ↔
      Readback root payload tree ∧ Evidence (Rule registry checked frames) tree := by
  constructor
  · exact reconstruct_sound registry checked frames payload root tree
  · rintro ⟨⟨sameRoot, samePayload⟩, evidence⟩
    rw [← sameRoot, ← samePayload]
    exact reconstruct_complete registry checked frames tree evidence

/-- Success needs precisely the existing raw-payload Plan derivation, not
caller-provided descendant occurrences or a precomputed source tree. -/
theorem reconstruct_exists_iff (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
    (payload : Payload) (root : Occurrence registry.roles) :
    (∃ tree, reconstruct registry checked frames payload root = some tree) ↔
      PayloadEvidence (Rule registry checked frames) root payload := by
  constructor
  · rintro ⟨tree, success⟩
    exact (payload_iff_erased _ _ _).mpr ⟨tree, (reconstruct_exact _ _ _ _ _ _).mp success⟩
  · intro evidence
    obtain ⟨tree, readback, instanceEvidence⟩ := payload_to_indexed _ _ _ evidence
    exact ⟨tree, (reconstruct_exact _ _ _ _ _ _).mpr ⟨readback, instanceEvidence⟩⟩

/-- No checked plan derivation is lost by the executable reconstruction. This
failure criterion says nothing about unresolved or unsupported source typing. -/
theorem reconstruct_none_iff (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
    (payload : Payload) (root : Occurrence registry.roles) :
    reconstruct registry checked frames payload root = none ↔
      ¬ PayloadEvidence (Rule registry checked frames) root payload := by
  constructor
  · intro empty evidence
    obtain ⟨tree, found⟩ := (reconstruct_exists_iff _ _ _ _ _).mpr evidence
    rw [empty] at found
    cases found
  · intro absent
    cases found : reconstruct registry checked frames payload root with
    | none => rfl
    | some tree => exact False.elim (absent ((reconstruct_exists_iff _ _ _ _ _).mp ⟨tree, found⟩))

end Yulang.GeneralDictionaryPayloadReconstruction
