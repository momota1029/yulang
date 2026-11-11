import Yulang.GeneralDictionarySemanticOrder

/-!
# Unique semantic evidence up to source-preserving sibling order

The local premise says the selected implementation key and all source child
occurrences are unique modulo sibling enumeration. It is not true of arbitrary
overlapping role instances. Under that exact premise, finite dictionary evidence
is unique up to the source-indexed structural equivalence, not merely key erasure.
-/
namespace Yulang.GeneralDictionarySemanticUniqueness
open GeneralSourceDictionaries GeneralDictionaryReadback GeneralDictionaryModelEvidence
open GeneralDictionarySemanticOrder
open CommonRoleOutermostResolver (All₂)

/-- This must be derived from actual unique candidate selection, not assumed
for every role-satisfaction relation or inferred from erased key agreement. -/
def NodeFunctional (localRule : LocalInstance roles) : Prop :=
  ∀ occurrence key₁ key₂ first last, localRule occurrence key₁ first →
    localRule occurrence key₂ last → key₁ = key₂ ∧ first.Perm last

theorem all₂_mono_members (relation other : α → β → Prop) {first : List α} {last : List β}
    (given : All₂ relation first last)
    (lift : ∀ a ∈ first, ∀ b ∈ last, relation a b → other a b) : All₂ other first last := by
  induction given with
  | nil => exact .nil
  | @cons a b before after pair rest ih =>
      exact .cons (lift a (by simp) b (by simp) pair)
        (ih (fun x hx y hy h => lift x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) h))

theorem align_roots (first last : List (Dictionary roles))
    (permuted : (first.map Dictionary.root).Perm (last.map Dictionary.root)) :
    ∃ middle, first.Perm middle ∧ All₂ (fun a b : Dictionary roles => a.root = b.root) middle last := by
  have pair : ∀ xs : List (Dictionary roles),
      All₂ (fun a occurrence => a.root = occurrence) xs (xs.map Dictionary.root) := by
    intro xs
    induction xs with
    | nil => exact .nil
    | cons head tail ih => exact .cons rfl ih
  obtain ⟨middle, order, related⟩ := GeneralDictionaryPayloadOrder.all₂_perm_right _ (pair first) permuted
  have convert : ∀ (xs ys : List (Dictionary roles)),
      All₂ (fun a occurrence => a.root = occurrence) xs (ys.map Dictionary.root) →
        All₂ (fun a b => a.root = b.root) xs ys := by
    intro xs ys
    induction ys generalizing xs with
    | nil => intro h; cases h; exact .nil
    | cons head tail ih =>
        intro h
        cases h with
        | cons first rest => exact .cons first (ih _ rest)
  exact ⟨middle, order, convert _ _ related⟩

theorem replace_all_children (occurrence : Occurrence roles) (key : Nat)
    (leading : List (Dictionary roles)) {first last : List (Dictionary roles)}
    (given : All₂ DictionaryEquivalent first last) :
    DictionaryEquivalent (.node occurrence key (leading ++ first))
      (.node occurrence key (leading ++ last)) := by
  induction given generalizing leading with
  | nil => exact .refl _
  | @cons a b before after same rest ih =>
      apply DictionaryEquivalent.trans (.replace occurrence key leading before same)
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using ih (leading ++ [b])

/-- All implementation keys stay attached to their source occurrences. The proof
never pairs children merely because their erased key trees happen to coincide. -/
theorem evidence_unique (localRule : LocalInstance roles) (functional : NodeFunctional localRule)
    (first : Dictionary roles) (given : Evidence localRule first) :
    ∀ last, last.root = first.root → Evidence localRule last → DictionaryEquivalent first last := by
  induction given with
  | @node occurrence key children instanceRule allChildren ih =>
      intro last sameRoot lastEvidence
      cases last with
      | node other otherKey others =>
          change other = occurrence at sameRoot
          subst other
          obtain ⟨otherRule, otherChildren⟩ := (evidence_node_iff ..).mp lastEvidence
          obtain ⟨sameKey, order⟩ := functional occurrence key otherKey _ _ instanceRule otherRule
          subst otherKey
          obtain ⟨middle, permuted, paired⟩ := align_roots children others order
          have related : All₂ DictionaryEquivalent middle others := by
            apply all₂_mono_members _ _ paired
            intro a memberA b memberB same
            exact ih a (permuted.mem_iff.mpr memberA) b same.symm (otherChildren b memberB)
          exact .trans (.reorder occurrence key permuted)
            (replace_all_children occurrence key [] related)

/-- Erased comparison follows from source-level uniqueness, not conversely. -/
theorem payload_unique (localRule : LocalInstance roles) (functional : NodeFunctional localRule)
    (occurrence : Occurrence roles) (first last : Payload)
    (one : PayloadEvidence localRule occurrence first) (two : PayloadEvidence localRule occurrence last) :
    GeneralDictionaryPayloadOrder.Equivalent first last := by
  obtain ⟨tree₁, readback₁, evidence₁⟩ := payload_to_indexed _ _ _ one
  obtain ⟨tree₂, readback₂, evidence₂⟩ := payload_to_indexed _ _ _ two
  have same := evidence_unique localRule functional tree₁ evidence₁ tree₂
    (readback₂.1.trans readback₁.1.symm) evidence₂
  simpa only [readback₁.2, readback₂.2] using GeneralDictionaryPayloadOrder.erase_equivalent same

/-- Exact selected packages determine both the selected key and their canonical
children. This is stronger than the same-key child coherence used by local_total. -/
def PackagesFunctional (packages : Packages roles state) : Prop :=
  ∀ occurrence key₁ key₂ first last located₁ located₂,
    packages occurrence key₁ first located₁ → packages occurrence key₂ last located₂ →
      key₁ = key₂ ∧ first = last

theorem unordered_package_functional (packages : Packages roles state)
    (functional : PackagesFunctional packages) (occurrence : Occurrence roles)
    (key₁ key₂ : Nat) (first last : List (Occurrence roles)) (located₁ located₂)
    (one : Unordered packages occurrence key₁ first located₁)
    (two : Unordered packages occurrence key₂ last located₂) : key₁ = key₂ ∧ first.Perm last := by
  obtain ⟨canonical₁, order₁, instance₁⟩ := one
  obtain ⟨canonical₂, order₂, instance₂⟩ := two
  obtain ⟨keys, children⟩ := functional occurrence key₁ key₂ canonical₁ canonical₂ located₁ located₂ instance₁ instance₂
  rw [← children] at order₂
  exact ⟨keys, order₁.trans order₂.symm⟩

theorem stored_functional (packages : Packages roles state) (functional : PackagesFunctional packages) :
    NodeFunctional (StoredInstance (Unordered packages)) := by
  intro occurrence key₁ key₂ first last one two
  obtain ⟨located₁, instance₁, _⟩ := one
  obtain ⟨located₂, instance₂, _⟩ := two
  exact unordered_package_functional packages functional occurrence key₁ key₂ first last located₁ located₂ instance₁ instance₂

theorem model_functional (packages : Packages roles state) (functional : PackagesFunctional packages)
    (assignment : GeneralSourceState.Assignment) :
    NodeFunctional (ModelInstance (Unordered packages) assignment) := by
  intro occurrence key₁ key₂ first last one two
  obtain ⟨located₁, instance₁, _⟩ := one
  obtain ⟨located₂, instance₂, _⟩ := two
  exact unordered_package_functional packages functional occurrence key₁ key₂ first last located₁ located₂ instance₁ instance₂

end Yulang.GeneralDictionarySemanticUniqueness
