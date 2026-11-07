import Yulang.CommonCanonicalAlpha

/-!
# Canonical constructor families with first-occurrence parameter names

The semantic alpha-normalizer chooses a unique representative independently of
the input slot names. This final executable pass names the parameters in the
left-to-right order of their first appearance. Repeated occurrences keep the
same ID. Unused generalized slots are appended only to complete an invertible
renaming; they do not introduce visible names or new constraints.

The visible first-occurrence list is proved to be exactly `0, ..., k - 1`.
The output remains complete for the alpha-equivalence relation of the finite
`Form` grammar, with arbitrary common type instances and fixed shared row IDs.
Weak-variable metadata and semantic parameter elimination are separate from
this bijective naming pass.
-/

namespace Yulang.CommonCanonicalNames

open ProducerCanonicalOpen (Expr Atom)
open CommonCanonicalInterface (Form)
open CommonCanonicalAlpha (Permutation AlphaEquivalent rename renameExpr)

variable {n m : Nat}

def occurrencesExpr : Expr n → List (Fin n)
  | .atom (.var index) => [index]
  | .atom (.base _) | .bottom | .top => []
  | .union first last | .inter first last => occurrencesExpr first ++ occurrencesExpr last

def occurrences : Form n → List (Fin n)
  | .scalar expression => occurrencesExpr expression
  | .pair first last => occurrences first ++ occurrences last
  | .required _ payload | .variant _ payload => occurrences payload
  | .arrow _ _ input output => occurrencesExpr input ++ occurrences output

/-- Keep the first occurrence and discard later copies without reordering. -/
def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | first :: rest => first :: (unique rest).filter fun entry => decide (entry ≠ first)

@[simp] theorem mem_unique {α : Type} [DecidableEq α] (entry : α) (list : List α) :
    entry ∈ unique list ↔ entry ∈ list := by
  induction list with
  | nil => simp [unique]
  | cons first rest ih =>
      by_cases same : entry = first <;> simp [unique, ih, same]

theorem unique_nodup {α : Type} [DecidableEq α] (list : List α) : (unique list).Nodup := by
  induction list with
  | nil => simp [unique]
  | cons first rest ih =>
      apply List.nodup_cons.mpr
      exact ⟨by simp, List.Pairwise.filter _ ih⟩

theorem unique_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (mapping : α → β) (injective : ∀ a b, mapping a = mapping b → a = b) (list : List α) :
    unique (list.map mapping) = (unique list).map mapping := by
  have inequalities (a b : α) : mapping a ≠ mapping b ↔ a ≠ b :=
    ⟨fun different same => different (congrArg mapping same), fun different same => different (injective a b same)⟩
  induction list with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, unique, ih, List.filter_map, Function.comp_def, inequalities]

theorem occurrencesExpr_rename (mapping : Fin n → Fin m) (expression : Expr n) :
    occurrencesExpr (renameExpr mapping expression) = (occurrencesExpr expression).map mapping := by
  induction expression with
  | atom entry => cases entry <;> rfl
  | _ => simp_all [renameExpr, occurrencesExpr]

theorem occurrences_rename (mapping : Fin n → Fin m) (expression : Form n) :
    occurrences (rename mapping expression) = (occurrences expression).map mapping := by
  induction expression <;> simp_all [rename, occurrences, occurrencesExpr_rename]

def used (expression : Form n) : List (Fin n) := unique (occurrences expression)

def order (expression : Form n) : List (Fin n) :=
  used expression ++ (List.finRange n).filter fun index => decide (index ∉ used expression)

theorem mem_order (expression : Form n) (index : Fin n) : index ∈ order expression := by
  by_cases present : index ∈ used expression <;> simp [order, present]

theorem order_nodup (expression : Form n) : (order expression).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨unique_nodup _, List.Pairwise.filter _ (List.nodup_finRange n), ?_⟩
  intro first present last missing equal
  have absent : last ∉ used expression := (List.mem_filter.mp missing).2 |> of_decide_eq_true
  exact absent (equal ▸ present)

theorem order_length (expression : Form n) : (order expression).length = n := by
  have permutation : (order expression).Perm (List.finRange n) :=
    (List.perm_ext_iff_of_nodup (order_nodup expression) (List.nodup_finRange n)).mpr
      (fun index => by simp [mem_order])
  simpa using permutation.length_eq

/-- A concrete invertible renaming. Its forward direction is the first
occurrence rank; the reverse direction is the corresponding finite lookup. -/
def occurrencePermutation (expression : Form n) : Permutation n where
  forward index := ⟨(order expression).idxOf index,
    by simpa only [order_length] using List.idxOf_lt_length_of_mem (mem_order expression index)⟩
  backward index := (order expression)[index.val]'(by simpa only [order_length] using index.isLt)

theorem occurrencePermutation_valid (expression : Form n) : (occurrencePermutation expression).Valid := by
  constructor
  · intro index
    have bound := List.idxOf_lt_length_of_mem (mem_order expression index)
    change (order expression)[(order expression).idxOf index]'bound = index
    exact List.getElem_idxOf _
  · intro index
    apply Fin.eq_of_val_eq
    have bound : index.val < (order expression).length := by simpa only [order_length] using index.isLt
    change (order expression).idxOf ((order expression)[index.val]'bound) = index.val
    exact (order_nodup expression).idxOf_getElem _ _

def byOccurrence (expression : Form n) : Form n := rename (occurrencePermutation expression).forward expression

theorem byOccurrence_alpha (expression : Form n) : AlphaEquivalent expression (byOccurrence expression) :=
  ⟨occurrencePermutation expression, occurrencePermutation_valid expression,
    fun _ _ => Common.equivalent_refl _⟩

private theorem used_rename (permutation : Permutation n) (valid : permutation.Valid) (expression : Form n) :
    used (rename permutation.forward expression) = (used expression).map permutation.forward := by
  have injective (first last : Fin n) (equal : permutation.forward first = permutation.forward last) : first = last := by
    have same := congrArg permutation.backward equal
    simpa only [valid.1] using same
  simpa only [used, occurrences_rename] using unique_map permutation.forward injective (occurrences expression)

private theorem order_index_used (expression : Form n) (index : Nat)
    (bound : index < (used expression).length) :
    (order expression).idxOf ((used expression)[index]) = index := by
  rw [order, List.idxOf_append, ite_eq_left (List.getElem_mem bound)]
  exact (unique_nodup (occurrences expression)).idxOf_getElem index bound

/-- The first visible occurrence of every generalized parameter receives
the next consecutive number. The theorem also covers no parameters and
unused slots, and counts repeated occurrences only once. -/
theorem first_occurrence_order (expression : Form n) :
    (used (byOccurrence expression)).map Fin.val = List.range (used expression).length := by
  rw [byOccurrence, used_rename _ (occurrencePermutation_valid expression), List.map_map]
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp only [List.getElem_map, Function.comp_apply, List.getElem_range]
    exact order_index_used expression index (by simpa using leftBound)

def normalize (expression : Form n) : Form n :=
  byOccurrence (CommonCanonicalAlpha.normalize expression)

theorem normalize_alpha (expression : Form n) : AlphaEquivalent expression (normalize expression) :=
  CommonCanonicalAlpha.alpha_trans (CommonCanonicalAlpha.normalize_alpha expression)
    (byOccurrence_alpha _)

/-- A canonical finite syntax with the specified first-occurrence names,
complete for the separately defined semantic alpha equivalence. -/
theorem normalize_exact (first last : Form n) :
    AlphaEquivalent first last ↔ normalize first = normalize last := by
  constructor
  · intro same
    exact congrArg byOccurrence ((CommonCanonicalAlpha.normalize_exact _ _).mp same)
  · intro equal
    have normalized := normalize_alpha first
    rw [equal] at normalized
    exact CommonCanonicalAlpha.alpha_trans normalized
      (CommonCanonicalAlpha.alpha_symm (normalize_alpha last))

theorem normalize_idempotent (expression : Form n) : normalize (normalize expression) = normalize expression :=
  (normalize_exact _ _).mp (CommonCanonicalAlpha.alpha_symm (normalize_alpha expression))

theorem normalize_first_occurrence_order (expression : Form n) :
    (used (normalize expression)).map Fin.val = List.range (used (normalize expression)).length := by
  have naming := first_occurrence_order (CommonCanonicalAlpha.normalize expression)
  have length : (used (normalize expression)).length =
      (used (CommonCanonicalAlpha.normalize expression)).length := by
    rw [normalize, byOccurrence, used_rename _ (occurrencePermutation_valid _), List.length_map]
  rw [length]
  exact naming

theorem normalize_instances_exact (expression : Form n) (rows : Nat → Common.Row) (target : Common.Ty) :
    (∃ parameters : Fin n → Common.Ty, Common.Equivalent (expression.instantiate rows parameters) target) ↔
      ∃ parameters : Fin n → Common.Ty,
        Common.Equivalent ((normalize expression).instantiate rows parameters) target :=
  CommonCanonicalAlpha.alpha_instances_exact (normalize_alpha expression) rows target

namespace Examples

theorem first_seen_slot_zero :
    byOccurrence (n := 3) (.arrow 4 7 (.atom (.var 2))
      (.pair (.scalar (.atom (.var 0))) (.scalar (.atom (.var 2))))) =
      .arrow 4 7 (.atom (.var 0))
        (.pair (.scalar (.atom (.var 1))) (.scalar (.atom (.var 0)))) := by decide +kernel

end Examples

end Yulang.CommonCanonicalNames
