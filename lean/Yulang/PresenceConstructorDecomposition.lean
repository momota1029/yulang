import Yulang.PresenceMaskedCoalescing

/-!
# Exact local alternatives for constructor payload observations

These are decomposition lemmas for the existing presence **data projection**,
not a definition of the demand-based producer order. Payload obligations refer
to the predicates supplied at one observation depth. They do not silently
quantify over masks on those child predicates: payloads in `Layer.meaning`
start unmasked. Every outer mask is nevertheless quantified in `AllMasksLe`.

Pairs have genuinely disjunctive empty-component alternatives. The final
regular-graph example proves that choosing an alternative separately at each
depth cannot in general be replaced by choosing one alternative for all
depths. A local finite inspector is therefore not yet a global branch solver.
-/

namespace Yulang.PresenceConstructorDecomposition

open PresenceLayers (Layer)
open PresenceDataTypes (Ty Le never any)
open PresenceRegularObservations (observe)
open SourceDataRuntime

universe u
variable {State : Type u}

def Empty (predicate : Ty) : Prop := ∀ item, ¬ predicate item

/-- The context is deliberately a single unmasked child observation. -/
inductive Obligation (State : Type u) where
  | below : State → State → Obligation State
  | empty : State → Obligation State
  | universal : State → Obligation State
  deriving Repr, DecidableEq

def Obligation.Holds (assignment : State → Ty) : Obligation State → Prop
  | .below left right => Le (assignment left) (assignment right)
  | .empty state => Empty (assignment state)
  | .universal state => ∀ item, assignment state item

abbrev Alternative (State : Type u) := List (Obligation State)
abbrev Alternatives (State : Type u) := List (Alternative State)

def Alternative.Holds (assignment : State → Ty) (branch : Alternative State) : Prop :=
  ∀ obligation ∈ branch, obligation.Holds assignment

def Alternatives.Holds (assignment : State → Ty) (branches : Alternatives State) : Prop :=
  ∃ branch ∈ branches, Alternative.Holds assignment branch

def AllMasksLe (assignment : State → Ty) (left right : Layer State) : Prop :=
  ∀ hidden, Le (left.meaning assignment hidden) (right.meaning assignment hidden)

private theorem exists_of_not_empty (predicate : Ty) (notEmpty : ¬ Empty predicate) :
    ∃ item, predicate item := by
  classical
  apply Classical.byContradiction
  intro absent
  exact notEmpty (fun item valid => absent ⟨item, valid⟩)

/-- Exact product inversion must keep both empty-component possibilities. -/
theorem pair_le_iff (a b c d : Ty) :
    Le (PresenceDataTypes.pair a b) (PresenceDataTypes.pair c d) ↔
      Empty a ∨ Empty b ∨ (Le a c ∧ Le b d) := by
  classical
  constructor
  · intro below
    by_cases firstEmpty : Empty a
    · exact Or.inl firstEmpty
    by_cases lastEmpty : Empty b
    · exact Or.inr (Or.inl lastEmpty)
    obtain ⟨first, firstValid⟩ := exists_of_not_empty a firstEmpty
    obtain ⟨last, lastValid⟩ := exists_of_not_empty b lastEmpty
    exact Or.inr (Or.inr ⟨fun item valid => (below (.pair item last) ⟨valid, lastValid⟩).1,
      fun item valid => (below (.pair first item) ⟨firstValid, valid⟩).2⟩)
  · intro alternatives item valid
    cases item with
    | pair first last =>
        rcases alternatives with empty | empty | ⟨left, right⟩
        · exact False.elim (empty first valid.1)
        · exact False.elim (empty last valid.2)
        · exact ⟨left first valid.1, right last valid.2⟩
    | _ => cases valid

def pairAlternatives (a b c d : State) : Alternatives State :=
  [[.empty a], [.empty b], [.below a c, .below b d]]

theorem pairAlternatives_exact (assignment : State → Ty) (a b c d : State) :
    Alternatives.Holds assignment (pairAlternatives a b c d) ↔
      AllMasksLe assignment (.pair a b) (.pair c d) := by
  have pairs := pair_le_iff (assignment a) (assignment b) (assignment c) (assignment d)
  simpa [Alternatives.Holds, Alternative.Holds, pairAlternatives, Obligation.Holds,
    AllMasksLe, Layer.meaning] using pairs.symm

theorem variant_same_le_iff (tag : Nat) (a b : Ty) :
    Le (PresenceDataTypes.variant tag a) (PresenceDataTypes.variant tag b) ↔ Le a b := by
  constructor
  · intro below item valid
    exact (below (.variant tag item) ⟨rfl, valid⟩).2
  · intro below item valid
    cases item with
    | variant name payload => exact ⟨valid.1, below payload valid.2⟩
    | _ => cases valid

theorem variant_different_le_iff (first last : Nat) (different : first ≠ last) (a b : Ty) :
    Le (PresenceDataTypes.variant first a) (PresenceDataTypes.variant last b) ↔ Empty a := by
  constructor
  · intro below item valid
    exact different (below (.variant first item) ⟨rfl, valid⟩).1
  · intro empty item valid
    cases item with
    | variant name payload => exact False.elim (empty payload valid.2)
    | _ => cases valid

def variantAlternatives (first last : Nat) (a b : State) : Alternatives State :=
  if first = last then [[.below a b]] else [[.empty a]]

/-- Includes both matching and arbitrary unequal tags. -/
theorem variantAlternatives_exact (assignment : State → Ty) (first last : Nat) (a b : State) :
    Alternatives.Holds assignment (variantAlternatives first last a b) ↔
      AllMasksLe assignment (.variant first a) (.variant last b) := by
  by_cases same : first = last
  · subst last
    simpa [Alternatives.Holds, Alternative.Holds, variantAlternatives, Obligation.Holds,
      AllMasksLe, Layer.meaning] using (variant_same_le_iff first (assignment a) (assignment b)).symm
  · simpa [Alternatives.Holds, Alternative.Holds, variantAlternatives, same, Obligation.Holds,
      AllMasksLe, Layer.meaning] using
        (variant_different_le_iff first last same (assignment a) (assignment b)).symm

private theorem singleton_required (label : Nat) (predicate : Ty) (item : Value)
    (valid : predicate item) : PresenceDataTypes.required label predicate (.record [(label, item)]) := by
  exact ⟨trivial, item, by simp [PresenceDataTypes.lookup, Fields.lookup], valid⟩

theorem required_same_le_iff (label : Nat) (a b : Ty) :
    Le (PresenceDataTypes.required label a) (PresenceDataTypes.required label b) ↔ Le a b := by
  constructor
  · intro below item valid
    obtain ⟨_, result, found, holds⟩ := below _ (singleton_required label a item valid)
    have same : result = item := by
      simpa only [PresenceDataTypes.lookup, Fields.lookup, ↓reduceIte, Option.some.injEq, eq_comm] using found
    exact same ▸ holds
  · rintro below item ⟨record, payload, found, valid⟩
    exact ⟨record, payload, found, below payload valid⟩

def requiredAlternatives (first last : Nat) (a b : State) : Alternatives State :=
  if first = last then [[.below a b]] else []

/-- Different required labels fail under all-mask comparison even when the
unmasked source payload is empty: hiding only the source field exposes the
target's requirement. Unknown numeric labels are included in the theorem. -/
theorem requiredAlternatives_exact (assignment : State → Ty) (first last : Nat) (a b : State) :
    Alternatives.Holds assignment (requiredAlternatives first last a b) ↔
      AllMasksLe assignment (.required first a) (.required last b) := by
  by_cases same : first = last
  · subst last
    simp only [requiredAlternatives, ↓reduceIte, Alternatives.Holds, List.mem_singleton,
      exists_eq_left, Alternative.Holds, forall_eq, Obligation.Holds]
    constructor
    · intro below hidden
      by_cases masked : first ∈ hidden
      · simp only [Layer.meaning, masked, ↓reduceIte]
        exact PresenceDataTypes.le_refl _
      · simp only [Layer.meaning, masked, ↓reduceIte]
        exact (required_same_le_iff first (assignment a) (assignment b)).mpr below
    · intro below
      exact (required_same_le_iff first (assignment a) (assignment b)).mp (below [])
  · simp only [requiredAlternatives, same, ↓reduceIte, Alternatives.Holds, List.not_mem_nil,
      false_and, exists_false, false_iff]
    intro below
    have accepted := below [first] (.record [])
    simp [Layer.meaning, Ne.symm same, PresenceDataTypes.records,
      PresenceDataTypes.required, PresenceDataTypes.lookup, Fields.lookup] at accepted

theorem optional_same_le_iff (label : Nat) (a b : Ty) :
    Le (PresenceDataTypes.optional label a) (PresenceDataTypes.optional label b) ↔ Le a b := by
  constructor
  · intro below item valid
    have source := PresenceDataTypes.required_optional label a _ (singleton_required label a item valid)
    exact (below _ source).2 item (by simp [PresenceDataTypes.lookup, Fields.lookup])
  · rintro below item ⟨record, values⟩
    exact ⟨record, fun value found => below value (values value found)⟩

def optionalAlternatives (first last : Nat) (a b : State) : Alternatives State :=
  if first = last then [[.below a b]] else [[.universal b]]

theorem optionalAlternatives_exact (assignment : State → Ty) (first last : Nat) (a b : State) :
    Alternatives.Holds assignment (optionalAlternatives first last a b) ↔
      AllMasksLe assignment (.optional first a) (.optional last b) := by
  by_cases same : first = last
  · subst last
    simp only [optionalAlternatives, ↓reduceIte, Alternatives.Holds, List.mem_singleton,
      exists_eq_left, Alternative.Holds, forall_eq, Obligation.Holds]
    constructor
    · intro below hidden
      by_cases masked : first ∈ hidden
      · simp only [Layer.meaning, masked, ↓reduceIte]
        exact PresenceDataTypes.le_refl _
      · simp only [Layer.meaning, masked, ↓reduceIte]
        exact (optional_same_le_iff first (assignment a) (assignment b)).mpr below
    · intro below
      exact (optional_same_le_iff first (assignment a) (assignment b)).mp (below [])
  · simp only [optionalAlternatives, same, ↓reduceIte, Alternatives.Holds, List.mem_singleton,
      exists_eq_left, Alternative.Holds, forall_eq, Obligation.Holds]
    constructor
    · intro universal hidden item valid
      by_cases leftMasked : first ∈ hidden <;> by_cases rightMasked : last ∈ hidden <;>
        simp only [Layer.meaning, leftMasked, rightMasked, ↓reduceIte] at valid ⊢
      · exact valid
      · exact ⟨valid, fun value _ => universal value⟩
      · exact valid.1
      · exact ⟨valid.1, fun value _ => universal value⟩
    · intro below item
      have source : (Layer.optional first a).meaning assignment [] (.record [(last, item)]) := by
        simp [Layer.meaning, PresenceDataTypes.optional, PresenceDataTypes.records,
          PresenceDataTypes.lookup, Fields.lookup, same]
      exact (below [] _ source).2 item (by simp [PresenceDataTypes.lookup, Fields.lookup])

/-- One observation-depth instance: no all-mask child inequality is inferred. -/
theorem pair_at_depth_iff (graph : PresenceRegularObservations.Graph State)
    (depth : Nat) (a b c d : State) :
    AllMasksLe (observe graph depth) (.pair a b) (.pair c d) ↔
      Alternatives.Holds (observe graph depth) (pairAlternatives a b c d) :=
  (pairAlternatives_exact (observe graph depth) a b c d).symm

theorem pair_all_depths_iff (graph : PresenceRegularObservations.Graph State) (a b c d : State) :
    (∀ depth, AllMasksLe (observe graph depth) (.pair a b) (.pair c d)) ↔
      ∀ depth, Alternatives.Holds (observe graph depth) (pairAlternatives a b c d) := by
  exact forall_congr' fun depth => pair_at_depth_iff graph depth a b c d

namespace ChangingDepth

/-- At depth one, B is empty while records is not below optional 7 bottom.
At every depth at least two, B is inhabited and optional 7 top is records. -/
def graph : PresenceRegularObservations.Graph (Fin 5) := fun index =>
  match index.val with
  | 0 => .records
  | 1 => .variant 11 4
  | 2 => .optional 7 3
  | 3 => .top
  | _ => .base .int

def branches : Alternatives (Fin 5) := pairAlternatives 0 1 2 3

theorem local_alternatives_at_every_depth (depth : Nat) :
    Alternatives.Holds (observe graph depth) branches := by
  cases depth with
  | zero =>
      refine ⟨[.empty 0], by simp [branches, pairAlternatives], ?_⟩
      intro obligation member
      have same : obligation = .empty 0 := by simpa only [List.mem_singleton] using member
      subst obligation
      exact fun _ impossible => impossible
  | succ depth =>
      cases depth with
      | zero =>
          refine ⟨[.empty 1], by simp [branches, pairAlternatives], ?_⟩
          intro obligation member
          have same : obligation = .empty 1 := by simpa only [List.mem_singleton] using member
          subst obligation
          intro item valid
          cases item <;> simp_all [observe, graph, Layer.denote,
            Layer.meaning, PresenceDataTypes.variant, never]
      | succ depth =>
          refine ⟨[.below 0 2, .below 1 3], by simp [branches, pairAlternatives], ?_⟩
          intro obligation member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · intro item valid
            exact ⟨valid, fun _ _ => trivial⟩
          · exact fun _ _ => trivial

/-- A real regular graph satisfies the parent comparison at every depth. -/
theorem parent_all_depths :
    ∀ depth, AllMasksLe (observe graph depth) (.pair 0 1) (.pair 2 3) := by
  intro depth
  exact (pair_at_depth_iff graph depth 0 1 2 3).mpr (local_alternatives_at_every_depth depth)

/-- None of the three local alternatives works uniformly over all depths.
Thus `∀ depth, ∃ branch` cannot be replaced by `∃ branch, ∀ depth`, even
for this finite, acyclic, monotone-data observation graph. -/
theorem no_uniform_alternative :
    ¬ ∃ branch ∈ branches, ∀ depth, Alternative.Holds (observe graph depth) branch := by
  rintro ⟨branch, member, every⟩
  simp only [branches, pairAlternatives, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact every 1 (.empty 0) (List.mem_cons_self) (.record []) trivial
  · exact every 2 (.empty 1) (List.mem_cons_self) (.variant 11 (.base .int)) ⟨rfl, rfl⟩
  · have source : observe graph 1 0 (.record [(7, .base .int)]) := trivial
    have accepted := every 1 (.below 0 2) (List.mem_cons_self) _ source
    exact accepted.2 (.base .int) (by simp [PresenceDataTypes.lookup, Fields.lookup])

end ChangingDepth

end Yulang.PresenceConstructorDecomposition
