import Yulang.ProducerCanonicalOpen

/-!
# Canonical minimal clauses with shared variables before concrete names

This extends the complete scalar-lattice code to any finite number of shared
type parameters. Each clause is an ordered sublist of the parameter slots,
then `bool`, `int`, `str`, `unit`. The sorted list of minimal clauses has an
executable syntax readback and characterizes contextual equivalence for every
arbitrary assignment to all parameter slots simultaneously.

Slots retain their original identities. Alpha-renaming of generalized slots,
constructor/regular-graph canonicalization and complete module interfaces are
separate obligations; the finite reference algorithm here does not claim them.
-/

namespace Yulang.ProducerCanonicalOpenClauses

open Inference (Base)
open ProducerContextual ProducerCanonicalOpen

universe u
variable {n : Nat} {Row : Type u}

def atomKey : Atom n → Nat
  | .var index => index.val
  | .base .bool => n
  | .base .int => n + 1
  | .base .str => n + 2
  | .base .unit => n + 3

def clauseLE (first last : List (Atom n)) : Bool :=
  decide (first.map atomKey ≤ last.map atomKey)

theorem eval_mono (expression : Expr n) {first last : List (Atom n)}
    (subset : first ⊆ last) (accepted : expression.eval first = true) :
    expression.eval last = true := by
  induction expression with
  | atom entry =>
      have member : entry ∈ first := by simpa [Expr.eval] using accepted
      simpa [Expr.eval] using subset member
  | bottom => rfl
  | top => cases accepted
  | union a b iha ihb =>
      have both : a.eval first = true ∧ b.eval first = true := by simpa [Expr.eval] using accepted
      simp [Expr.eval, iha both.1, ihb both.2]
  | inter a b iha ihb =>
      have either : a.eval first = true ∨ b.eval first = true := by simpa [Expr.eval] using accepted
      rcases either with left | right
      · simp [Expr.eval, iha left]
      · simp [Expr.eval, ihb right]

def minimal (expression : Expr n) (profile : List (Atom n)) : Bool :=
  expression.eval profile &&
    !(profiles n).any (fun smaller =>
      decide (List.Sublist smaller profile) && decide (smaller ≠ profile) && expression.eval smaller)

def canonicalEncoding (expression : Expr n) : List (List (Atom n)) :=
  ((profiles n).filter (minimal expression)).mergeSort clauseLE

theorem mem_encoding (expression : Expr n) (profile : List (Atom n)) :
    profile ∈ canonicalEncoding expression ↔
      profile ∈ profiles n ∧ expression.eval profile = true ∧
        ∀ smaller ∈ profiles n, List.Sublist smaller profile →
          expression.eval smaller = true → smaller = profile := by
  simp only [canonicalEncoding, List.mem_mergeSort, List.mem_filter, minimal, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_false]
  constructor
  · rintro ⟨member, accepted, min⟩
    refine ⟨member, accepted, ?_⟩
    intro smaller present subset valid
    apply Classical.byContradiction
    intro different
    exact min smaller present (by simp [subset, different, valid])
  · rintro ⟨member, accepted, min⟩
    refine ⟨member, accepted, ?_⟩
    intro smaller present valid
    have facts : (List.Sublist smaller profile ∧ smaller ≠ profile) ∧
        expression.eval smaller = true := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using valid
    exact facts.1.2 (min smaller present facts.1.1 facts.2)

private theorem minimal_below (expression : Expr n) (profile : List (Atom n))
    (present : profile ∈ profiles n) (accepted : expression.eval profile = true) :
    ∃ smaller ∈ canonicalEncoding expression, List.Sublist smaller profile := by
  classical
  have induction : ∀ size, ∀ profile : List (Atom n), profile.length = size →
      profile ∈ profiles n → expression.eval profile = true →
      ∃ smaller ∈ canonicalEncoding expression, List.Sublist smaller profile := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
        intro profile length present accepted
        by_cases min : ∀ smaller ∈ profiles n, List.Sublist smaller profile →
            expression.eval smaller = true → smaller = profile
        · exact ⟨profile, (mem_encoding expression profile).mpr ⟨present, accepted, min⟩, .refl _⟩
        · have smaller : ∃ smaller ∈ profiles n, List.Sublist smaller profile ∧
              expression.eval smaller = true ∧ smaller ≠ profile := by
            obtain ⟨smaller, failure⟩ := Classical.not_forall.mp min
            obtain ⟨present, failure⟩ := not_imp.mp failure
            obtain ⟨subset, failure⟩ := not_imp.mp failure
            obtain ⟨valid, different⟩ := not_imp.mp failure
            exact ⟨smaller, present, subset, valid, different⟩
          obtain ⟨smaller, smallerPresent, subset, valid, different⟩ := smaller
          have bound := subset.length_le
          have unequal : smaller.length ≠ profile.length := fun equal => different (subset.eq_of_length equal)
          have decrease : smaller.length < size := by omega
          obtain ⟨least, member, included⟩ := ih smaller.length decrease smaller rfl smallerPresent valid
          exact ⟨least, member, included.trans subset⟩
  exact induction profile.length profile rfl present accepted

theorem eval_iff_clause (expression : Expr n) (profile : List (Atom n))
    (present : profile ∈ profiles n) :
    expression.eval profile = true ↔
      ∃ smaller ∈ canonicalEncoding expression, smaller ⊆ profile := by
  constructor
  · intro accepted
    obtain ⟨smaller, member, subset⟩ := minimal_below expression profile present accepted
    exact ⟨smaller, member, subset.subset⟩
  · rintro ⟨smaller, member, subset⟩
    exact eval_mono expression subset ((mem_encoding expression smaller).mp member).2.1

private theorem any_congr_on {α : Type} (list : List α) (first last : α → Bool)
    (same : ∀ entry ∈ list, first entry = last entry) : list.any first = list.any last := by
  induction list with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.any_cons]
      rw [same entry (by simp), ih (fun inner member => same inner (by simp [member]))]

theorem canonicalEncoding_eq_iff (first last : Expr n) :
    canonicalEncoding first = canonicalEncoding last ↔
      ∀ profile ∈ profiles n, first.eval profile = last.eval profile := by
  constructor
  · intro same profile present
    apply Bool.eq_iff_iff.mpr
    rw [eval_iff_clause first profile present, eval_iff_clause last profile present, same]
  · intro same
    have filters : (profiles n).filter (minimal first) = (profiles n).filter (minimal last) := by
      apply List.filter_congr
      intro profile present
      simp only [minimal, same profile present]
      congr 2
      apply any_congr_on
      intro smaller member
      rw [same smaller member]
    unfold canonicalEncoding
    rw [filters]

/-- All variables are quantified simultaneously over arbitrary contextual
types. The conclusion is equality of finite executable syntax data. -/
theorem canonicalEncoding_exact (leRow : Row → Row → Prop) (first last : Expr n) :
    Equivalent leRow first last ↔ canonicalEncoding first = canonicalEncoding last := by
  rw [equivalent_iff_evaluations, canonicalEncoding_eq_iff]

theorem clause_order (expression : Expr n) (clause : List (Atom n))
    (member : clause ∈ canonicalEncoding expression) : List.Sublist clause (atoms n) :=
  (mem_profiles clause).mp ((mem_encoding expression clause).mp member).1

/-- No concrete base can precede a variable in a clause. Variable IDs stay
shared; concrete names occur in the lexical order of `baseOrder`. -/
theorem clause_variables_first (expression : Expr n) (clause : List (Atom n))
    (member : clause ∈ canonicalEncoding expression) :
    ∃ variables bases,
      clause = variables.map Atom.var ++ bases.map Atom.base ∧
      List.Sublist variables (List.finRange n) ∧
      List.Sublist bases ProducerCanonicalBase.baseOrder := by
  have shape := clause_order expression clause member
  obtain ⟨variables, bases, equal, variableShape, baseShape⟩ := List.sublist_append_iff.mp shape
  obtain ⟨indices, indexShape, rfl⟩ := List.sublist_map_iff.mp variableShape
  obtain ⟨scalars, scalarShape, rfl⟩ := List.sublist_map_iff.mp baseShape
  exact ⟨indices, scalars, equal, indexShape, scalarShape⟩

theorem clauses_sorted (expression : Expr n) :
    (canonicalEncoding expression).Pairwise (fun first last =>
      first.map atomKey ≤ last.map atomKey) := by
  have sorted := List.pairwise_mergeSort (le := @clauseLE n)
    (fun first middle last left right => by
      simp only [clauseLE, decide_eq_true_eq] at left right ⊢
      exact List.le_trans left right)
    (fun first last => by
      simp only [clauseLE, Bool.or_eq_true, decide_eq_true_eq]
      exact List.le_total _ _) ((profiles n).filter (minimal expression))
  exact sorted.imp (fun ordered => of_decide_eq_true ordered)

theorem clauses_antichain (expression : Expr n) {first last : List (Atom n)}
    (firstMember : first ∈ canonicalEncoding expression) (lastMember : last ∈ canonicalEncoding expression)
    (subset : List.Sublist first last) : first = last :=
  ((mem_encoding expression last).mp lastMember).2.2 first
    ((mem_encoding expression first).mp firstMember).1 subset
    ((mem_encoding expression first).mp firstMember).2.1

def unionClause : List (Atom n) → Expr n
  | [] => .bottom
  | [entry] => .atom entry
  | entry :: next :: rest => .union (.atom entry) (unionClause (next :: rest))

def readback : List (List (Atom n)) → Expr n
  | [] => .top
  | [clause] => unionClause clause
  | clause :: next :: rest => .inter (unionClause clause) (readback (next :: rest))

theorem unionClause_eval (members profile : List (Atom n)) :
    (unionClause members).eval profile = true ↔ members ⊆ profile := by
  induction members with
  | nil => simp [unionClause, Expr.eval]
  | cons entry rest ih =>
      cases rest with
      | nil => simp [unionClause, Expr.eval]
      | cons next rest => simpa [unionClause, Expr.eval] using and_congr Iff.rfl ih

theorem readback_eval (code : List (List (Atom n))) (profile : List (Atom n)) :
    (readback code).eval profile = true ↔ ∃ clause ∈ code, clause ⊆ profile := by
  induction code with
  | nil => simp [readback, Expr.eval]
  | cons clause rest ih =>
      cases rest with
      | nil => simp [readback, unionClause_eval]
      | cons next rest => simpa [readback, Expr.eval, unionClause_eval] using or_congr Iff.rfl ih

def normalize (expression : Expr n) : Expr n := readback (canonicalEncoding expression)

theorem normalize_eval (expression : Expr n) (profile : List (Atom n)) (present : profile ∈ profiles n) :
    (normalize expression).eval profile = expression.eval profile := by
  apply Bool.eq_iff_iff.mpr
  rw [normalize, readback_eval, eval_iff_clause expression profile present]

theorem normalize_equivalent (leRow : Row → Row → Prop) (expression : Expr n) :
    Equivalent leRow (normalize expression) expression :=
  (equivalent_iff_evaluations leRow _ _).mpr (normalize_eval expression)

theorem normalize_idempotent (expression : Expr n) : normalize (normalize expression) = normalize expression := by
  unfold normalize
  congr 1
  exact (canonicalEncoding_eq_iff _ _).mpr (normalize_eval expression)

theorem normalize_exact (leRow : Row → Row → Prop) (first last : Expr n) :
    Equivalent leRow first last ↔ normalize first = normalize last := by
  constructor
  · intro same
    exact congrArg readback ((canonicalEncoding_exact leRow first last).mp same)
  · intro same
    apply (equivalent_iff_evaluations leRow first last).mpr
    intro profile present
    rw [← normalize_eval first profile present, same, normalize_eval last profile present]

namespace Examples

theorem variable_before_bases :
    canonicalEncoding (n := 1)
      (.union (.atom (.base .str)) (.union (.atom (.var 0)) (.atom (.base .int)))) =
      [[.var 0, .base .int, .base .str]] := by decide +kernel

theorem shared_variable_absorbed :
    normalize (n := 1) (.inter (.atom (.var 0)) (.union (.atom (.var 0)) (.atom (.base .int)))) =
      .atom (.var 0) := by decide +kernel

theorem independent_variables_kept :
    canonicalEncoding (n := 2) (.union (.atom (.var 0)) (.atom (.var 1))) = [[.var 0, .var 1]] := by decide +kernel

theorem distinct_variable_codes :
    canonicalEncoding (n := 2) (.atom (.var 0)) ≠ canonicalEncoding (.atom (.var 1)) := by decide +kernel

theorem sorted_mixed_intersection :
    canonicalEncoding (n := 1) (.inter (.atom (.base .str)) (.atom (.var 0))) =
      [[.var 0], [.base .str]] := by
  have raw : (profiles 1).filter (minimal (.inter (.atom (.base .str)) (.atom (.var 0)))) =
      [[.base .str], [.var 0]] := by decide +kernel
  rw [canonicalEncoding, raw, List.mergeSort_pair]
  decide

end Examples
end Yulang.ProducerCanonicalOpenClauses
