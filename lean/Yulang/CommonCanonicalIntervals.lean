import Yulang.CommonCanonicalParameters
import Yulang.CommonBoundCoalescing

/-!
# Complete instance-family codes for scalar lattice expressions

All generalized slots in an arbitrary scalar union/intersection expression
range independently over arbitrary common types. Captured slots remain fixed
throughout each comparison; they are never silently generalized. The numbers
of generalized slots may differ, including zero, and all sharing within the
scalar expression is retained.

For each fixed captured assignment, the exact instances are precisely the
closed subtype interval between substitution of bottom and substitution of
top for all generalized slots. A single common target in this interval can
be assigned to every generalized slot to recover it. This gives a complete,
executable code consisting of the two already canonical captured expressions.
For the separate subtype-instance judgement, the lower endpoint alone gives
a complete code and proves positive-only parameter elimination.
No candidate reparameterization, inverse substitution, same-arity bijection,
or semantic equivalence oracle is an input.

This is complete for the entire scalar lattice grammar, not for constructor
interfaces with correlated outputs, mixed polarity, row expressions, qualified
obligations, or recursive graphs. Captured slots model fixed ambient/weak type
identities, but this module does not implement weak-variable display metadata.
-/

namespace Yulang.CommonCanonicalIntervals

open ProducerCanonicalOpen (Expr Atom)
open CommonCanonicalParameters (substituteExpr)
open CommonCanonicalAlpha (renameExpr)
open Common (Ty Subtype Equivalent)

variable {fixed generalized other : Nat}

/-- Captured slots precede independently generalized slots. -/
abbrev Polynomial (fixed generalized : Nat) := Expr (fixed + generalized)

def instantiate (expression : Polynomial fixed generalized) (captured : Fin fixed → Ty)
    (parameters : Fin generalized → Ty) : Ty :=
  CommonCanonicalOpen.instantiate (Fin.addCases captured parameters) expression

def specialize (replacement : Expr fixed) (expression : Polynomial fixed generalized) : Expr fixed :=
  substituteExpr (Fin.addCases (fun index => .atom (.var index)) (fun _ => replacement)) expression

def lower (expression : Polynomial fixed generalized) : Expr fixed := specialize .bottom expression
def upper (expression : Polynomial fixed generalized) : Expr fixed := specialize .top expression

/-- The target of a diagonal assignment occupies the final fresh slot. -/
def diagonal (expression : Polynomial fixed generalized) : Expr (fixed + 1) :=
  substituteExpr
    (Fin.addCases (fun index => .atom (.var index.castSucc)) (fun _ => .atom (.var (Fin.last fixed))))
    expression

def liftCaptured (expression : Expr fixed) : Expr (fixed + 1) := renameExpr Fin.castSucc expression

def envelope (expression : Polynomial fixed generalized) : Expr (fixed + 1) :=
  .union (liftCaptured (lower expression))
    (.inter (.atom (.var (Fin.last fixed))) (liftCaptured (upper expression)))

theorem instantiate_specialize (replacement : Expr fixed) (expression : Polynomial fixed generalized)
    (captured : Fin fixed → Ty) :
    CommonCanonicalOpen.instantiate captured (specialize replacement expression) =
      instantiate expression captured (fun _ => CommonCanonicalOpen.instantiate captured replacement) := by
  rw [specialize, CommonCanonicalParameters.instantiate_substituteExpr]
  congr 1
  funext index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;>
    simp [CommonCanonicalOpen.instantiate, CommonCanonicalOpen.atomType]

theorem instantiate_diagonal (expression : Polynomial fixed generalized)
    (captured : Fin fixed → Ty) (target : Ty) :
    CommonCanonicalOpen.instantiate (Fin.lastCases target captured) (diagonal expression) =
      instantiate expression captured (fun _ => target) := by
  rw [diagonal, CommonCanonicalParameters.instantiate_substituteExpr]
  congr 1
  funext index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;>
    simp [CommonCanonicalOpen.instantiate, CommonCanonicalOpen.atomType]

theorem instantiate_liftCaptured (expression : Expr fixed) (captured : Fin fixed → Ty) (target : Ty) :
    CommonCanonicalOpen.instantiate (Fin.lastCases target captured) (liftCaptured expression) =
      CommonCanonicalOpen.instantiate captured expression := by
  rw [liftCaptured, CommonCanonicalAlpha.instantiate_renameExpr]
  congr 1
  funext index
  simp

private def truth (variables : Fin n → Bool) (bases : Inference.Base → Bool) : Expr n → Bool
  | .atom (.var index) => variables index
  | .atom (.base scalar) => bases scalar
  | .bottom => true
  | .top => false
  | .union first last => truth variables bases first && truth variables bases last
  | .inter first last => truth variables bases first || truth variables bases last

private theorem truth_profile (profile : List (Atom n)) (expression : Expr n) :
    truth (fun index => decide (Atom.var index ∈ profile))
      (fun scalar => decide (Atom.base scalar ∈ profile)) expression = expression.eval profile := by
  induction expression with
  | atom entry => cases entry <;> rfl
  | _ => simp_all [truth, Expr.eval]

private theorem truth_substitute (replacement : Fin n → Expr m) (variables : Fin m → Bool)
    (bases : Inference.Base → Bool) (expression : Expr n) :
    truth variables bases (substituteExpr replacement expression) =
      truth (fun index => truth variables bases (replacement index)) bases expression := by
  induction expression with
  | atom entry => cases entry <;> rfl
  | _ => simp_all [truth, substituteExpr]

private theorem truth_rename (mapping : Fin n → Fin m) (variables : Fin m → Bool)
    (bases : Inference.Base → Bool) (expression : Expr n) :
    truth variables bases (renameExpr mapping expression) =
      truth (variables ∘ mapping) bases expression := by
  induction expression with
  | atom entry => cases entry <;> rfl
  | _ => simp_all [truth, renameExpr]

private theorem truth_specialize (replacement : Expr fixed)
    (expression : Polynomial fixed generalized) (captured : Fin fixed → Bool)
    (bases : Inference.Base → Bool) :
    truth captured bases (specialize replacement expression) =
      truth (Fin.addCases captured (fun _ => truth captured bases replacement)) bases expression := by
  rw [specialize, truth_substitute]
  congr 1
  funext index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;> simp [truth]

private theorem truth_diagonal (expression : Polynomial fixed generalized)
    (variables : Fin (fixed + 1) → Bool) (bases : Inference.Base → Bool) :
    truth variables bases (diagonal expression) =
      truth (Fin.addCases (fun index => variables index.castSucc) (fun _ => variables (Fin.last fixed)))
        bases expression := by
  rw [diagonal, truth_substitute]
  congr 1
  funext index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;> simp [truth]

private theorem truth_mono (expression : Expr n) (first last : Fin n → Bool)
    (bases : Inference.Base → Bool)
    (included : ∀ index, first index = true → last index = true) :
    truth first bases expression = true → truth last bases expression = true := by
  induction expression with
  | atom entry => cases entry with
      | var index => exact included index
      | base => exact id
  | bottom | top => exact id
  | union before after ihb iha =>
      simp only [truth, Bool.and_eq_true] at *
      exact fun accepted => ⟨ihb accepted.1, iha accepted.2⟩
  | inter before after ihb iha =>
      simp only [truth, Bool.or_eq_true] at *
      exact fun accepted => accepted.elim (fun h => Or.inl (ihb h)) (fun h => Or.inr (iha h))

private theorem truth_interval (expression : Polynomial fixed generalized)
    (captured : Fin fixed → Bool) (bases : Inference.Base → Bool) (value : Bool) :
    truth (Fin.addCases captured (fun _ => value)) bases expression =
      (truth (Fin.addCases captured (fun _ => true)) bases expression &&
        (value || truth (Fin.addCases captured (fun _ => false)) bases expression)) := by
  cases value with
  | true => simp
  | false =>
      have monotone := truth_mono expression
        (Fin.addCases captured (fun _ => false)) (Fin.addCases captured (fun _ => true)) bases
        (by
          intro index
          refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;> simp)
      cases first : truth (Fin.addCases captured (fun _ => true)) bases expression <;>
        cases last : truth (Fin.addCases captured (fun _ => false)) bases expression <;> simp_all

/-- The polynomial identity is proved using the independent finite profile
theorem, which quantifies over every common-type assignment. -/
theorem diagonal_equivalent (expression : Polynomial fixed generalized) :
    CommonCanonicalOpen.Equivalent (diagonal expression) (envelope expression) := by
  apply CommonCanonicalOpen.common_scalar_profile_exact _ _ |>.mpr
  intro profile _
  rw [← truth_profile profile, ← truth_profile profile]
  simp only [envelope, truth, truth_diagonal, liftCaptured, truth_rename,
    lower, upper, truth_specialize]
  exact truth_interval expression _ _ _

/-- Substitution of the same arbitrary target into all generalized slots is
exactly the interval clamp, up to common demand equivalence. -/
theorem diagonal_clamp (expression : Polynomial fixed generalized)
    (captured : Fin fixed → Ty) (target : Ty) :
    Equivalent (instantiate expression captured (fun _ => target))
      (.union (CommonCanonicalOpen.instantiate captured (lower expression))
        (.inter target (CommonCanonicalOpen.instantiate captured (upper expression)))) := by
  have exactness := diagonal_equivalent expression (Fin.lastCases target captured)
  rw [instantiate_diagonal] at exactness
  simpa only [envelope, CommonCanonicalOpen.instantiate, CommonCanonicalOpen.atomType,
    Fin.lastCases_last, instantiate_liftCaptured] using exactness

theorem instantiate_mono (expression : Expr n) (first last : Fin n → Ty)
    (below : ∀ index, Subtype (first index) (last index)) :
    Subtype (CommonCanonicalOpen.instantiate first expression)
      (CommonCanonicalOpen.instantiate last expression) := by
  induction expression with
  | atom entry => cases entry with
      | var index => exact below index
      | base scalar => exact Common.subtype_refl _
  | bottom | top => exact Common.subtype_refl _
  | union first last ihf ihl => exact Common.common_union_mono ihf ihl
  | inter first last ihf ihl => exact Common.common_inter_mono ihf ihl

theorem instance_bounds (expression : Polynomial fixed generalized) (captured : Fin fixed → Ty)
    (parameters : Fin generalized → Ty) :
    Subtype (CommonCanonicalOpen.instantiate captured (lower expression))
        (instantiate expression captured parameters) ∧
      Subtype (instantiate expression captured parameters)
        (CommonCanonicalOpen.instantiate captured (upper expression)) := by
  rw [lower, upper, instantiate_specialize, instantiate_specialize]
  constructor
  · apply instantiate_mono
    intro index
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index
    · simp only [Fin.addCases_left]
      exact Common.subtype_refl _
    · simpa only [Fin.addCases_right, CommonCanonicalOpen.instantiate] using
        CommonBoundCoalescing.bottom_le (parameters index)
  · apply instantiate_mono
    intro index
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index
    · simp only [Fin.addCases_left]
      exact Common.subtype_refl _
    · simpa only [Fin.addCases_right, CommonCanonicalOpen.instantiate] using
        CommonBoundCoalescing.le_top (parameters index)

/-- Exact instances, not only an upward closure: every target between the
two endpoint types is itself recovered by a simultaneous diagonal assignment. -/
theorem instances_interval (expression : Polynomial fixed generalized)
    (captured : Fin fixed → Ty) (target : Ty) :
    (∃ parameters : Fin generalized → Ty, Equivalent (instantiate expression captured parameters) target) ↔
      Subtype (CommonCanonicalOpen.instantiate captured (lower expression)) target ∧
        Subtype target (CommonCanonicalOpen.instantiate captured (upper expression)) := by
  constructor
  · rintro ⟨parameters, same⟩
    have bounds := instance_bounds expression captured parameters
    exact ⟨Common.subtype_trans bounds.1 same.1, Common.subtype_trans same.2 bounds.2⟩
  · rintro ⟨above, below⟩
    refine ⟨fun _ => target, Common.equivalent_trans (diagonal_clamp expression captured target) ?_⟩
    constructor
    · exact (Common.common_union_is_join _ _ _).mpr
        ⟨above, CommonBoundCoalescing.inter_le_left _ _⟩
    · exact Common.subtype_trans
        ((Common.common_inter_is_meet _ _ _).mpr ⟨Common.subtype_refl _, below⟩)
        (CommonBoundCoalescing.le_union_right _ _)

/-- Captured identities are fixed while generalized assignments are chosen
independently on each side. This permits different generalized arities. -/
def FamilyEquivalent (first : Polynomial fixed generalized) (last : Polynomial fixed other) : Prop :=
  ∀ captured : Fin fixed → Ty, ∀ target : Ty,
    (∃ parameters : Fin generalized → Ty, Equivalent (instantiate first captured parameters) target) ↔
      ∃ parameters : Fin other → Ty, Equivalent (instantiate last captured parameters) target

private theorem lower_instance (expression : Polynomial fixed generalized) (captured : Fin fixed → Ty) :
    ∃ parameters : Fin generalized → Ty,
      Equivalent (instantiate expression captured parameters)
        (CommonCanonicalOpen.instantiate captured (lower expression)) := by
  refine ⟨fun _ => .bottom, ?_⟩
  rw [lower, instantiate_specialize]
  exact Common.equivalent_refl _

private theorem upper_instance (expression : Polynomial fixed generalized) (captured : Fin fixed → Ty) :
    ∃ parameters : Fin generalized → Ty,
      Equivalent (instantiate expression captured parameters)
        (CommonCanonicalOpen.instantiate captured (upper expression)) := by
  refine ⟨fun _ => .top, ?_⟩
  rw [upper, instantiate_specialize]
  exact Common.equivalent_refl _

theorem familyEquivalent_iff_endpoints (first : Polynomial fixed generalized)
    (last : Polynomial fixed other) :
    FamilyEquivalent first last ↔
      CommonCanonicalOpen.Equivalent (lower first) (lower last) ∧
        CommonCanonicalOpen.Equivalent (upper first) (upper last) := by
  constructor
  · intro families
    constructor <;> intro captured
    · exact ⟨((instances_interval first captured _).mp
          ((families captured _).mpr (lower_instance last captured))).1,
        ((instances_interval last captured _).mp
          ((families captured _).mp (lower_instance first captured))).1⟩
    · exact ⟨((instances_interval last captured _).mp
          ((families captured _).mp (upper_instance first captured))).2,
        ((instances_interval first captured _).mp
          ((families captured _).mpr (upper_instance last captured))).2⟩
  · rintro ⟨lowerSame, upperSame⟩ captured target
    rw [instances_interval, instances_interval]
    constructor
    · rintro ⟨above, below⟩
      exact ⟨Common.subtype_trans (lowerSame captured).2 above,
        Common.subtype_trans below (upperSame captured).1⟩
    · rintro ⟨above, below⟩
      exact ⟨Common.subtype_trans (lowerSame captured).1 above,
        Common.subtype_trans below (upperSame captured).2⟩

abbrev Code (fixed : Nat) := List (List (Atom fixed)) × List (List (Atom fixed))

def canonicalEncoding (expression : Polynomial fixed generalized) : Code fixed :=
  (CommonCanonicalOpen.canonicalEncoding (lower expression),
    CommonCanonicalOpen.canonicalEncoding (upper expression))

/-- A complete finite decision criterion for all scalar-lattice instance
families, across arbitrary generalized arities and with all captured values
held fixed. No reparameterization witness is assumed. -/
theorem canonicalEncoding_exact (first : Polynomial fixed generalized)
    (last : Polynomial fixed other) :
    FamilyEquivalent first last ↔ canonicalEncoding first = canonicalEncoding last := by
  rw [familyEquivalent_iff_endpoints, CommonCanonicalOpen.canonicalEncoding_exact,
    CommonCanonicalOpen.canonicalEncoding_exact]
  simp only [canonicalEncoding, Prod.mk.injEq]


/-- For a result used through ordinary subsumption, every positive-only
parameter is eliminated by the lower endpoint. This is a different judgement
from exact instance equality, whose upper endpoint remains significant. -/
theorem subtype_instances_lower (expression : Polynomial fixed generalized)
    (captured : Fin fixed → Ty) (target : Ty) :
    (∃ parameters : Fin generalized → Ty, Subtype (instantiate expression captured parameters) target) ↔
      Subtype (CommonCanonicalOpen.instantiate captured (lower expression)) target := by
  constructor
  · rintro ⟨parameters, below⟩
    exact Common.subtype_trans (instance_bounds expression captured parameters).1 below
  · intro below
    refine ⟨fun _ => .bottom, ?_⟩
    simpa only [lower, instantiate_specialize, CommonCanonicalOpen.instantiate] using below

def SubtypeFamilyEquivalent (first : Polynomial fixed generalized) (last : Polynomial fixed other) : Prop :=
  ∀ captured : Fin fixed → Ty, ∀ target : Ty,
    (∃ parameters : Fin generalized → Ty, Subtype (instantiate first captured parameters) target) ↔
      ∃ parameters : Fin other → Ty, Subtype (instantiate last captured parameters) target

theorem subtypeFamilyEquivalent_iff_lower (first : Polynomial fixed generalized)
    (last : Polynomial fixed other) :
    SubtypeFamilyEquivalent first last ↔ CommonCanonicalOpen.Equivalent (lower first) (lower last) := by
  constructor
  · intro families captured
    have same (target : Ty) :
        Subtype (CommonCanonicalOpen.instantiate captured (lower first)) target ↔
          Subtype (CommonCanonicalOpen.instantiate captured (lower last)) target := by
      simpa only [subtype_instances_lower] using families captured target
    exact ⟨(same _).mpr (Common.subtype_refl _), (same _).mp (Common.subtype_refl _)⟩
  · intro same captured target
    rw [subtype_instances_lower, subtype_instances_lower]
    exact ⟨fun below => Common.subtype_trans (same captured).2 below,
      fun below => Common.subtype_trans (same captured).1 below⟩

def subtypeCanonicalEncoding (expression : Polynomial fixed generalized) : List (List (Atom fixed)) :=
  CommonCanonicalOpen.canonicalEncoding (lower expression)

/-- Complete for the scalar scheme judgement used with a subtype target.
Captured values remain universally fixed on both sides of the comparison. -/
theorem subtypeCanonicalEncoding_exact (first : Polynomial fixed generalized)
    (last : Polynomial fixed other) :
    SubtypeFamilyEquivalent first last ↔ subtypeCanonicalEncoding first = subtypeCanonicalEncoding last :=
  (subtypeFamilyEquivalent_iff_lower first last).trans
    (CommonCanonicalOpen.canonicalEncoding_exact (lower first) (lower last))

end Yulang.CommonCanonicalIntervals
