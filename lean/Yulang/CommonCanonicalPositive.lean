import Yulang.CommonCanonicalIntervals

/-!
# Complete canonical codes for constructor families with positive parameters

A shared generalized type parameter may occur arbitrarily often in scalar
leaves, pairs, required fields, tags, and arrow results. Arrow domains use only
fixed captured parameters; those may be repeated in either polarity and are
never generalized by this pass. Every row ID is retained literally.

For this complete syntactic sublanguage of `CommonCanonicalInterface.Form`,
substituting bottom simultaneously for all generalized slots gives a least
instance. Exact subtype-instance equality across any two generalized arities
is therefore decided by the existing complete constructor/lattice encoding of
the two lower forms. Correlation is preserved by the single simultaneous
substitution. This does not assert that exact constructor-instance sets are
intervals, or extend the sublanguage to generalized negative occurrences,
regular graph bodies, general rows, nominal/role obligations, or exporters.
-/

namespace Yulang.CommonCanonicalPositive

open ProducerCanonicalOpen (Expr Atom)
open CommonCanonicalInterface (Form)
open CommonCanonicalNames (occurrencesExpr)
open CommonCanonicalParameters (substitute)
open Common (Row Ty Subtype)

variable {fixed generalized other : Nat}

/-- A finite syntax condition, not a restriction on assigned captured types. -/
def CapturedOnly (expression : Expr (fixed + generalized)) : Prop :=
  ∀ index ∈ occurrencesExpr expression, index.val < fixed

/-- Every generalized occurrence is covariant. Captured variables may still
occur and share identities in both arrow domains and results. -/
def Positive : Form (fixed + generalized) → Prop
  | .scalar _ => True
  | .pair first last => Positive first ∧ Positive last
  | .required _ payload | .variant _ payload => Positive payload
  | .arrow _ _ input output => CapturedOnly input ∧ Positive output

def instantiate (expression : Form (fixed + generalized)) (rows : Nat → Row)
    (captured : Fin fixed → Ty) (parameters : Fin generalized → Ty) : Ty :=
  expression.instantiate rows (Fin.addCases captured parameters)

def lower (expression : Form (fixed + generalized)) : Form fixed :=
  substitute (Fin.addCases (fun index => .atom (.var index)) (fun _ => .bottom)) expression

theorem instantiate_lower (expression : Form (fixed + generalized)) (rows : Nat → Row)
    (captured : Fin fixed → Ty) :
    (lower expression).instantiate rows captured = instantiate expression rows captured (fun _ => .bottom) := by
  rw [lower, CommonCanonicalParameters.instantiate_substitute]
  congr 1
  funext index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;>
    simp [CommonCanonicalOpen.instantiate, CommonCanonicalOpen.atomType]

theorem captured_domain_unchanged (expression : Expr (fixed + generalized))
    (onlyCaptured : CapturedOnly expression) (captured : Fin fixed → Ty)
    (first last : Fin generalized → Ty) :
    CommonCanonicalOpen.instantiate (Fin.addCases captured first) expression =
      CommonCanonicalOpen.instantiate (Fin.addCases captured last) expression := by
  apply CommonCanonicalParameters.instantiateExpr_agrees
  intro index member
  have inside := onlyCaptured index member
  let original : Fin fixed := ⟨index.val, inside⟩
  have same : index = original.castAdd generalized := Fin.ext rfl
  simp only [same, Fin.addCases_left]

theorem instantiate_mono (expression : Form (fixed + generalized)) (positive : Positive expression)
    (rows : Nat → Row) (captured : Fin fixed → Ty) (first last : Fin generalized → Ty)
    (below : ∀ index, Subtype (first index) (last index)) :
    Subtype (instantiate expression rows captured first) (instantiate expression rows captured last) := by
  induction expression with
  | scalar expression =>
      apply CommonCanonicalIntervals.instantiate_mono
      intro index
      refine Fin.addCases (fun index => ?_) (fun index => ?_) index
      · simp only [Fin.addCases_left]
        exact Common.subtype_refl _
      · simpa only [Fin.addCases_right] using below index
  | pair before after ihb iha =>
      exact (Common.common_pair_iff _ _ _ _).mpr ⟨ihb positive.1, iha positive.2⟩
  | required label payload ih =>
      exact (Common.common_singleton_requirement_iff label _ _ Common.emptyRecord).mpr (ih positive)
  | variant label payload ih =>
      exact (Common.common_variant_iff label _ _).mpr (ih positive)
  | arrow incoming outgoing input output ih =>
      have domain := captured_domain_unchanged input positive.1 captured first last
      apply (Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
      refine ⟨?_, Common.rowLe_refl _, ih positive.2, Common.rowLe_refl _⟩
      rw [domain]
      exact Common.subtype_refl _

/-- Shared positive variables, including those used at several distinct
constructor leaves, are eliminated simultaneously with no instance premise. -/
theorem subtype_instances_lower (expression : Form (fixed + generalized)) (positive : Positive expression)
    (rows : Nat → Row) (captured : Fin fixed → Ty) (target : Ty) :
    (∃ parameters : Fin generalized → Ty, Subtype (instantiate expression rows captured parameters) target) ↔
      Subtype ((lower expression).instantiate rows captured) target := by
  constructor
  · rintro ⟨parameters, below⟩
    rw [instantiate_lower]
    exact Common.subtype_trans
      (instantiate_mono expression positive rows captured (fun _ => .bottom) parameters
        (fun _ => CommonBoundCoalescing.bottom_le _)) below
  · intro below
    exact ⟨fun _ => .bottom, by simpa only [instantiate_lower] using below⟩

def FamilyEquivalent (first : Form (fixed + generalized)) (last : Form (fixed + other)) : Prop :=
  ∀ rows : Nat → Row, ∀ captured : Fin fixed → Ty, ∀ target : Ty,
    (∃ parameters : Fin generalized → Ty, Subtype (instantiate first rows captured parameters) target) ↔
      ∃ parameters : Fin other → Ty, Subtype (instantiate last rows captured parameters) target

theorem familyEquivalent_iff_lower (first : Form (fixed + generalized)) (last : Form (fixed + other))
    (firstPositive : Positive first) (lastPositive : Positive last) :
    FamilyEquivalent first last ↔ CommonCanonicalInterface.Equivalent (lower first) (lower last) := by
  constructor
  · intro families rows captured
    have same (target : Ty) :
        Subtype ((lower first).instantiate rows captured) target ↔
          Subtype ((lower last).instantiate rows captured) target := by
      simpa only [subtype_instances_lower first firstPositive,
        subtype_instances_lower last lastPositive] using families rows captured target
    exact ⟨(same _).mpr (Common.subtype_refl _), (same _).mp (Common.subtype_refl _)⟩
  · intro same rows captured target
    rw [subtype_instances_lower first firstPositive, subtype_instances_lower last lastPositive]
    exact ⟨fun below => Common.subtype_trans (same rows captured).2 below,
      fun below => Common.subtype_trans (same rows captured).1 below⟩

def canonicalEncoding (expression : Form (fixed + generalized)) : CommonCanonicalInterface.Code fixed :=
  CommonCanonicalInterface.encode (lower expression)

/-- Complete for the declared constructor sublanguage, including unequal
numbers of generalized variables, arbitrary captured common types, and all
simultaneous row assignments. No same-shape or same-arity premise occurs. -/
theorem canonicalEncoding_exact (first : Form (fixed + generalized)) (last : Form (fixed + other))
    (firstPositive : Positive first) (lastPositive : Positive last) :
    FamilyEquivalent first last ↔ canonicalEncoding first = canonicalEncoding last :=
  (familyEquivalent_iff_lower first last firstPositive lastPositive).trans
    (CommonCanonicalInterface.canonicalEncoding_exact (lower first) (lower last))

end Yulang.CommonCanonicalPositive
