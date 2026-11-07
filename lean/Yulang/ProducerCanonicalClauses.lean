import Yulang.ProducerCanonicalBase

/-!
# Lexically ordered minimal clauses for base/lattice producers

The sixteen-bit complete code is converted into a unique finite antichain.
Each clause is a sorted union of base names; the outer list is an intersection
of clauses. Only inclusion-minimal accepting role profiles are retained, so
the representation removes lattice association, duplicates and absorption.
Both the encoder and its readback are executable finite computations.

Completeness is proved against the existing contextual demand semantics,
not against syntactic equality of this representation. The scope remains the
base/lattice fragment stated in `ProducerCanonicalBase`.
-/

namespace Yulang.ProducerCanonicalClauses

open Inference (Base)
open ProducerContextual ProducerCanonicalBase

universe u

def _root_.Yulang.ProducerCanonicalBase.Profile.subset (first last : Profile) : Bool :=
  first.members.all last.accepts

theorem subset_exact (first last : Profile) :
    first.subset last = true ↔
      ∀ scalar, first.accepts scalar = true → last.accepts scalar = true := by
  simp only [Profile.subset, List.all_eq_true]
  exact ⟨fun h scalar member => h scalar ((Profile.mem_members first scalar).mpr member),
    fun h scalar member => h scalar ((Profile.mem_members first scalar).mp member)⟩

theorem subset_refl (profile : Profile) : profile.subset profile = true :=
  (subset_exact profile profile).mpr (fun _ accepted => accepted)

theorem subset_trans {first middle last : Profile}
    (left : first.subset middle = true) (right : middle.subset last = true) :
    first.subset last = true :=
  (subset_exact first last).mpr fun scalar member =>
    (subset_exact middle last).mp right scalar ((subset_exact first middle).mp left scalar member)

theorem profile_ext {first last : Profile}
    (same : ∀ scalar, first.accepts scalar = last.accepts scalar) : first = last := by
  obtain ⟨b, i, s, u⟩ := first
  obtain ⟨b', i', s', u'⟩ := last
  have hb := same .bool
  have hi := same .int
  have hs := same .str
  have hu := same .unit
  simp only [Profile.accepts] at hb hi hs hu
  simp [hb, hi, hs, hu]

theorem subset_antisymm {first last : Profile}
    (left : first.subset last = true) (right : last.subset first = true) : first = last := by
  apply profile_ext
  intro scalar
  apply Bool.eq_iff_iff.mpr
  exact ⟨(subset_exact first last).mp left scalar, (subset_exact last first).mp right scalar⟩

theorem members_injective : Function.Injective Profile.members := by
  intro first last same
  apply profile_ext
  intro scalar
  apply Bool.eq_iff_iff.mpr
  rw [← Profile.mem_members, ← Profile.mem_members, same]

theorem eval_mono (expression : Expr) {first last : Profile}
    (subset : first.subset last = true) (accepted : expression.eval first = true) :
    expression.eval last = true := by
  induction expression with
  | base scalar => exact (subset_exact first last).mp subset scalar accepted
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

/-- The size measure is used only in the termination proof of minimality,
not as a cutoff or fuel parameter of the encoder. -/
def _root_.Yulang.ProducerCanonicalBase.Profile.card (profile : Profile) : Nat := profile.members.length

private theorem card_lt_of_strict (first last : Profile)
    (subset : first.subset last = true) (different : first ≠ last) :
    first.card < last.card := by
  obtain ⟨b, i, s, u⟩ := first
  obtain ⟨b', i', s', u'⟩ := last
  cases b <;> cases i <;> cases s <;> cases u <;>
    cases b' <;> cases i' <;> cases s' <;> cases u' <;>
    simp_all [Profile.subset, Profile.card, Profile.members, baseOrder, Profile.accepts] <;> decide

def minimal (expression : Expr) (profile : Profile) : Bool :=
  expression.eval profile &&
    !(profiles.any fun smaller =>
      smaller.subset profile && decide (smaller ≠ profile) && expression.eval smaller)

def clauses (expression : Expr) : List Profile :=
  profiles.filter (minimal expression)

theorem mem_clauses (expression : Expr) (profile : Profile) :
    profile ∈ clauses expression ↔
      expression.eval profile = true ∧
        ∀ smaller, smaller.subset profile = true →
          expression.eval smaller = true → smaller = profile := by
  simp only [clauses, List.mem_filter, mem_profiles, true_and, minimal, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_false]
  constructor
  · rintro ⟨accepted, min⟩
    refine ⟨accepted, ?_⟩
    intro smaller subset valid
    apply Classical.byContradiction
    intro different
    exact min smaller trivial (by simp [subset, different, valid])
  · rintro ⟨accepted, min⟩
    refine ⟨accepted, ?_⟩
    intro smaller _ valid
    have facts : (smaller.subset profile = true ∧ smaller ≠ profile) ∧
        expression.eval smaller = true := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using valid
    exact facts.1.2 (min smaller facts.1.1 facts.2)

private theorem minimal_below (expression : Expr) (profile : Profile)
    (accepted : expression.eval profile = true) :
    ∃ smaller, smaller ∈ clauses expression ∧ smaller.subset profile = true := by
  classical
  have induction : ∀ size, ∀ profile : Profile, profile.card = size →
      expression.eval profile = true →
      ∃ smaller, smaller ∈ clauses expression ∧ smaller.subset profile = true := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
        intro profile card accepted
        by_cases min : ∀ smaller, smaller.subset profile = true →
            expression.eval smaller = true → smaller = profile
        · exact ⟨profile, (mem_clauses expression profile).mpr ⟨accepted, min⟩, subset_refl profile⟩
        · have smaller : ∃ smaller, smaller.subset profile = true ∧
              expression.eval smaller = true ∧ smaller ≠ profile := by
            obtain ⟨smaller, failure⟩ := Classical.not_forall.mp min
            obtain ⟨subset, failure⟩ := not_imp.mp failure
            obtain ⟨valid, different⟩ := not_imp.mp failure
            exact ⟨smaller, subset, valid, different⟩
          obtain ⟨smaller, subset, valid, different⟩ := smaller
          have decrease : smaller.card < size := card ▸ card_lt_of_strict smaller profile subset different
          obtain ⟨least, member, included⟩ := ih smaller.card decrease smaller rfl valid
          exact ⟨least, member, subset_trans included subset⟩
  exact induction profile.card profile rfl accepted

theorem eval_iff_clause (expression : Expr) (profile : Profile) :
    expression.eval profile = true ↔
      ∃ smaller ∈ clauses expression, smaller.subset profile = true := by
  constructor
  · exact minimal_below expression profile
  · rintro ⟨smaller, member, subset⟩
    exact eval_mono expression subset ((mem_clauses expression smaller).mp member).1

/-- Every union clause has lexical member order; the outer list has the fixed
lexical order of `profiles`, independent of the source's traversal order. -/
def canonicalEncoding (expression : Expr) : List (List Base) :=
  (clauses expression).map Profile.members

theorem clauses_eq_iff (first last : Expr) :
    clauses first = clauses last ↔ ∀ profile, first.eval profile = last.eval profile := by
  constructor
  · intro same profile
    apply Bool.eq_iff_iff.mpr
    rw [eval_iff_clause, eval_iff_clause, same]
  · intro same
    apply List.filter_congr
    intro profile _
    simp only [minimal, same]

theorem canonicalEncoding_eq_iff (first last : Expr) :
    canonicalEncoding first = canonicalEncoding last ↔
      ∀ profile, first.eval profile = last.eval profile := by
  unfold canonicalEncoding
  rw [List.map_inj_right (fun _ _ same => members_injective same), clauses_eq_iff]

/-- Complete canonical encoding for every base/lattice expression and every
row relation. No support check, equivalence oracle or proof witness is input. -/
theorem canonicalEncoding_exact (leRow : Row → Row → Prop) (first last : Expr) :
    ProducerEq leRow (first.embed Row) (last.embed Row) ↔
      canonicalEncoding first = canonicalEncoding last := by
  rw [equivalent_iff_evaluations, canonicalEncoding_eq_iff]

theorem clause_members_lexical (expression : Expr) (clause : List Base)
    (member : clause ∈ canonicalEncoding expression) :
    clause.Pairwise (fun a b => baseName a < baseName b) := by
  obtain ⟨profile, _, rfl⟩ := List.mem_map.mp member
  exact members_lexical profile

private theorem profiles_lexical : profiles.Pairwise (fun first last =>
    first.members.map baseName < last.members.map baseName) := by decide

theorem clauses_lexical (expression : Expr) :
    (canonicalEncoding expression).Pairwise (fun first last =>
      first.map baseName < last.map baseName) := by
  have ordered := List.Pairwise.filter (minimal expression) profiles_lexical
  simpa only [canonicalEncoding, List.pairwise_map, clauses] using ordered

theorem clauses_antichain (expression : Expr) {first last : Profile}
    (firstMember : first ∈ clauses expression) (lastMember : last ∈ clauses expression)
    (subset : first.subset last = true) : first = last :=
  ((mem_clauses expression last).mp lastMember).2 first subset
    ((mem_clauses expression first).mp firstMember).1

/-- Executable syntax readback of the canonical clauses. Empty union and
intersection lists denote `never` and `any`, respectively. -/
def unionClause : List Base → Expr
  | [] => .bottom
  | [scalar] => .base scalar
  | scalar :: next :: rest => .union (.base scalar) (unionClause (next :: rest))

def readback : List (List Base) → Expr
  | [] => .top
  | [clause] => unionClause clause
  | clause :: next :: rest => .inter (unionClause clause) (readback (next :: rest))

theorem unionClause_eval (members : List Base) (profile : Profile) :
    (unionClause members).eval profile = true ↔
      ∀ scalar ∈ members, profile.accepts scalar = true := by
  induction members with
  | nil => simp [unionClause, Expr.eval]
  | cons scalar rest ih =>
      cases rest with
      | nil => simp [unionClause, Expr.eval]
      | cons next rest => simpa [unionClause, Expr.eval] using and_congr Iff.rfl ih

theorem readback_eval (code : List (List Base)) (profile : Profile) :
    (readback code).eval profile = true ↔
      ∃ clause ∈ code, ∀ scalar ∈ clause, profile.accepts scalar = true := by
  induction code with
  | nil => simp [readback, Expr.eval]
  | cons clause rest ih =>
      cases rest with
      | nil => simp [readback, unionClause_eval]
      | cons next rest => simpa [readback, Expr.eval, unionClause_eval] using or_congr Iff.rfl ih

def normalize (expression : Expr) : Expr := readback (canonicalEncoding expression)

theorem normalize_eval (expression : Expr) (profile : Profile) :
    (normalize expression).eval profile = expression.eval profile := by
  apply Bool.eq_iff_iff.mpr
  rw [normalize, readback_eval, eval_iff_clause]
  simp only [canonicalEncoding, List.mem_map]
  constructor
  · rintro ⟨_, ⟨smaller, member, rfl⟩, accepted⟩
    exact ⟨smaller, member, (List.all_eq_true).mpr accepted⟩
  · rintro ⟨smaller, member, subset⟩
    exact ⟨smaller.members, ⟨smaller, member, rfl⟩, (List.all_eq_true).mp subset⟩

theorem normalize_equivalent (leRow : Row → Row → Prop) (expression : Expr) :
    ProducerEq leRow ((normalize expression).embed Row) (expression.embed Row) :=
  (equivalent_iff_evaluations leRow _ _).mpr (normalize_eval expression)

theorem normalize_idempotent (expression : Expr) : normalize (normalize expression) = normalize expression := by
  unfold normalize
  congr 1
  exact (canonicalEncoding_eq_iff _ _).mpr (normalize_eval expression)

/-- The readback is a complete syntactic normal form for this fragment too,
not merely a sound pass with a complete auxiliary bit table. -/
theorem normalize_exact (leRow : Row → Row → Prop) (first last : Expr) :
    ProducerEq leRow (first.embed Row) (last.embed Row) ↔ normalize first = normalize last := by
  constructor
  · intro same
    exact congrArg readback ((canonicalEncoding_exact leRow first last).mp same)
  · intro same
    apply (equivalent_iff_evaluations leRow first last).mpr
    intro profile
    rw [← normalize_eval first profile, same, normalize_eval]

def renderClause (clause : List Base) : String :=
  if clause.isEmpty then "never" else String.intercalate " | " (clause.map baseName)

def renderCode : List (List Base) → String
  | [] => "any"
  | [clause] => renderClause clause
  | clauses => String.intercalate " & " (clauses.map fun clause =>
      if clause.length ≤ 1 then renderClause clause else "(" ++ renderClause clause ++ ")")

def render (expression : Expr) : String := renderCode (canonicalEncoding expression)

theorem render_equivalent (leRow : Row → Row → Prop) {first last : Expr}
    (same : ProducerEq leRow (first.embed Row) (last.embed Row)) : render first = render last :=
  congrArg renderCode ((canonicalEncoding_exact leRow first last).mp same)

namespace Examples

theorem int_str_code :
    canonicalEncoding (.union (.base .int) (.base .str)) = [[.int, .str]] := by decide

theorem str_int_code :
    canonicalEncoding (.union (.base .str) (.base .int)) = [[.int, .str]] := by decide

theorem swapped_union_same_encoding :
    canonicalEncoding (.union (.base .int) (.base .str)) =
      canonicalEncoding (.union (.base .str) (.base .int)) := by decide

theorem swapped_union_same_normal_form :
    normalize (.union (.base .int) (.base .str)) =
      normalize (.union (.base .str) (.base .int)) := by decide

theorem int_str_normal :
    normalize (.union (.base .str) (.base .int)) = .union (.base .int) (.base .str) := by decide

theorem str_int_display : render (.union (.base .str) (.base .int)) = "int | str" := by decide

theorem sorted_intersection_display : render (.inter (.base .unit) (.base .bool)) = "bool & unit" := by decide

theorem bottom_eliminated : normalize (.union .bottom (.base .int)) = .base .int := by decide

theorem lattice_absorption :
    normalize (.inter (.base .int) (.union (.base .int) (.base .str))) = .base .int := by decide

theorem mixed_union_not_top_code :
    canonicalEncoding (.union (.base .int) (.base .str)) ≠ canonicalEncoding .top := by decide

end Examples
end Yulang.ProducerCanonicalClauses
