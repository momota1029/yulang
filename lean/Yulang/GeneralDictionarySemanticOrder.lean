import Yulang.GeneralDictionaryPayloadOrder
import Yulang.GeneralDictionaryModelEvidence

/-!
# Canonical child generation versus unordered semantic evidence

An exact package stores one canonical child list. Its semantic view admits only
permutations of that complete list, retaining all occurrence identities and the
same located equations. This separates deterministic readback from conjunction
semantics; it does not claim both properties of a single ordered local rule.
-/
namespace Yulang.GeneralDictionarySemanticOrder
open GeneralSourceDictionaries GeneralDictionaryReadback GeneralDictionaryModelEvidence
open GeneralDictionaryPayloadOrder (Equivalent)
open GeneralDictionaryStateEquations (Located Recorded)
open GeneralSourceState (State Assignment Models)

/-- Only sibling enumeration is forgotten. No occurrence, equation or key is
removed, copied, substituted, or reconstructed from the erased payload. -/
def Unordered (packages : Packages roles state) : Packages roles state :=
  fun occurrence key children located =>
    ∃ canonical, children.Perm canonical ∧ packages occurrence key canonical located

theorem unordered_intro (packages : Packages roles state) (occurrence : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) (located : Located state occurrence.demand)
    (instanceRule : packages occurrence key children located) :
    Unordered packages occurrence key children located :=
  ⟨children, .refl _, instanceRule⟩

theorem unordered_perm (packages : Packages roles state) (occurrence : Occurrence roles)
    (key : Nat) (first last : List (Occurrence roles)) (permuted : first.Perm last)
    (located : Located state occurrence.demand) :
    Unordered packages occurrence key first located ↔ Unordered packages occurrence key last located := by
  constructor
  · rintro ⟨canonical, order, instanceRule⟩
    exact ⟨canonical, permuted.symm.trans order, instanceRule⟩
  · rintro ⟨canonical, order, instanceRule⟩
    exact ⟨canonical, permuted.trans order, instanceRule⟩

theorem unordered_idempotent (packages : Packages roles state) (occurrence : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) (located : Located state occurrence.demand) :
    Unordered (Unordered packages) occurrence key children located ↔
      Unordered packages occurrence key children located := by
  constructor
  · rintro ⟨middle, first, canonical, last, instanceRule⟩
    exact ⟨canonical, first.trans last, instanceRule⟩
  · exact unordered_intro _ _ _ _ _

/-- Exact package determinism becomes permutation determinism, not literal equality. -/
theorem unordered_children_perm (packages : Packages roles state)
    (deterministic : ∀ occurrence key first last located₁ located₂,
      packages occurrence key first located₁ → packages occurrence key last located₂ → first = last)
    (occurrence : Occurrence roles) (key : Nat) (first last : List (Occurrence roles))
    (located₁ located₂) (one : Unordered packages occurrence key first located₁)
    (two : Unordered packages occurrence key last located₂) : first.Perm last := by
  obtain ⟨canonical₁, order₁, instance₁⟩ := one
  obtain ⟨canonical₂, order₂, instance₂⟩ := two
  have same := deterministic occurrence key canonical₁ canonical₂ located₁ located₂ instance₁ instance₂
  rw [← same] at order₂
  exact order₁.trans order₂.symm

theorem stored_invariant (packages : Packages roles state) :
    PermutationInvariant (StoredInstance (Unordered packages)) := by
  intro occurrence key first last permuted
  constructor
  · rintro ⟨located, instanceRule, recorded⟩
    exact ⟨located, (unordered_perm packages occurrence key first last permuted located).mp instanceRule, recorded⟩
  · rintro ⟨located, instanceRule, recorded⟩
    exact ⟨located, (unordered_perm packages occurrence key first last permuted located).mpr instanceRule, recorded⟩

theorem model_invariant (packages : Packages roles state) (assignment : Assignment) :
    PermutationInvariant (ModelInstance (Unordered packages) assignment) := by
  intro occurrence key first last permuted
  constructor
  · rintro ⟨located, instanceRule, equations⟩
    exact ⟨located, (unordered_perm packages occurrence key first last permuted located).mp instanceRule, equations⟩
  · rintro ⟨located, instanceRule, equations⟩
    exact ⟨located, (unordered_perm packages occurrence key first last permuted located).mpr instanceRule, equations⟩

theorem indexed_stored_semantic (packages : Packages roles state) (tree : Dictionary roles)
    (stored : Evidence (StoredInstance packages) tree) :
    Evidence (StoredInstance (Unordered packages)) tree := by
  apply evidence_mono _ _ _ stored
  intro occurrence key children given
  obtain ⟨located, instanceRule, recorded⟩ := given
  exact ⟨located, unordered_intro packages occurrence key children located instanceRule, recorded⟩

/-- A canonical exact witness supplies the semantic evidence of any structurally
equivalent payload. Source children are transported alongside each payload. -/
theorem equivalent_stored_payload (packages : Packages roles state) (occurrence : Occurrence roles)
    (before after : Payload) (same : Equivalent before after)
    (stored : PayloadEvidence (StoredInstance packages) occurrence before) :
    PayloadEvidence (StoredInstance (Unordered packages)) occurrence after := by
  obtain ⟨tree, ⟨root, erased⟩, evidence⟩ := payload_to_indexed _ _ _ stored
  have lifted := indexed_to_payload _ tree (indexed_stored_semantic packages tree evidence)
  rw [root, erased] at lifted
  exact (GeneralDictionaryPayloadOrder.equivalent_evidence _ (stored_invariant packages) same occurrence).mp lifted

/-- Full sibling comparison is compatible with the actual shared-state model
bridge, for one arbitrary model shared by every node. -/
theorem equivalent_payload_all_models (packages : Packages roles state) (occurrence : Occurrence roles)
    (before after : Payload) (same : Equivalent before after)
    (stored : PayloadEvidence (StoredInstance packages) occurrence before)
    (assignment : Assignment) (model : Models state assignment) :
    PayloadEvidence (ModelInstance (Unordered packages) assignment) occurrence after :=
  payload_all_models (Unordered packages) occurrence after
    (equivalent_stored_payload packages occurrence before after same stored) assignment model

/-- The changed payload still has one fixed complete source witness valid for
all shared models. This is stronger than choosing unrelated witnesses per model. -/
theorem equivalent_uniform_witness (packages : Packages roles state) (occurrence : Occurrence roles)
    (before after : Payload) (same : Equivalent before after)
    (stored : PayloadEvidence (StoredInstance packages) occurrence before) :
    ∃ tree, Readback occurrence after tree ∧
      ∀ assignment, Models state assignment → Evidence (ModelInstance (Unordered packages) assignment) tree :=
  erased_uniform_witness (Unordered packages) occurrence after
    ((payload_iff_erased _ _ _).mp (equivalent_stored_payload packages occurrence before after same stored))

end Yulang.GeneralDictionarySemanticOrder
