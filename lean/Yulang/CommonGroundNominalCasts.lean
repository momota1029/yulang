import Yulang.CommonGroundScalarCasts
import Yulang.CommonNominalRoots

/-!
# A concrete ground cast compatibility for common nominal roots

The declared ground grammar contains closed scalar expressions and nominal
applications whose value arguments are closed scalar expressions. Nominal
arguments are normalized before translation to `Casts.Ty`; their raw equality
then agrees exactly with common demand equivalence. Arbitrary unnormalized
cast syntax is not identified with semantic argument equality.

The actual `Casts.Compatibility` below is total. Outside this ground grammar
it uses raw equality for two nonscalar endpoints; those cases are only a
totalization of the old interface, not a common structural-subtyping theorem.
The exact common theorem quantifies every input of `Ground` and the computed
normalization image. It excludes nested nominal arguments, structural
constructors around nominal values, row arguments and regular nominal graphs.
-/

namespace Yulang.CommonGroundNominalCasts

open CommonGroundScalarCasts (Scalar)
open CommonNominalHeads (Argument ArgumentsEquivalent)

def Rel (source target : Casts.Ty) : Prop :=
  match CommonGroundScalarCasts.read source, CommonGroundScalarCasts.read target with
  | some first, some last => Common.Subtype
      (CommonGroundScalarCasts.meaning first) (CommonGroundScalarCasts.meaning last)
  | some first, none => Common.Subtype (CommonGroundScalarCasts.meaning first) .bottom
  | none, some last => Common.Subtype .top (CommonGroundScalarCasts.meaning last)
  | none, none => source = target

def check (source target : Casts.Ty) : Bool :=
  match CommonGroundScalarCasts.read source, CommonGroundScalarCasts.read target with
  | some first, some last => CommonGroundScalarCasts.check first last
  | some first, none => CommonGroundScalarCasts.check first .bottom
  | none, some last => CommonGroundScalarCasts.check .top last
  | none, none => decide (source = target)

theorem check_exact (source target : Casts.Ty) : check source target = true ↔ Rel source target := by
  cases first : CommonGroundScalarCasts.read source <;>
    cases last : CommonGroundScalarCasts.read target <;>
    simp only [check, Rel, first, last]
  · simp
  all_goals exact CommonGroundScalarCasts.check_exact _ _

theorem rel_refl (type : Casts.Ty) : Rel type type := by
  cases found : CommonGroundScalarCasts.read type with
  | none => simp [Rel, found]
  | some scalar => exact (show Rel type type from by
      simpa only [Rel, found] using Common.subtype_refl (CommonGroundScalarCasts.meaning scalar))

/-- Constructed from a finite checker. No compatibility oracle is supplied. -/
def fitsCommonGround : Casts.Compatibility where
  Rel := Rel
  check := check
  exact := check_exact
  refl := rel_refl
  nominalInvariant := by
    intro name arguments otherName otherArguments same
    simpa only [Rel, CommonGroundScalarCasts.read, Casts.Ty.nominal.injEq] using same

inductive Ground where
  | scalar : Scalar → Ground
  | nominal : Nat → List Scalar → Ground

def argumentMeaning (expression : Scalar) : Argument :=
  .value (CommonGroundScalarCasts.meaning expression)

def argumentCode (expression : Scalar) : Casts.Ty :=
  CommonGroundScalarCasts.quote (CommonCanonicalOpen.normalize expression)

/-- Normalize exactly the invariant arguments before entering the old raw
ground cast interface. Scalar outer expressions keep their original syntax. -/
def lower : Ground → Casts.Ty
  | .scalar expression => CommonGroundScalarCasts.quote expression
  | .nominal name arguments => .nominal name (arguments.map argumentCode)

def meaning : Ground → CommonNominalRoots.Ty
  | .scalar expression => .common (CommonGroundScalarCasts.meaning expression)
  | .nominal name arguments => .nominal ⟨name, arguments.map argumentMeaning⟩

theorem arguments_normalized_exact (first last : List Scalar) :
    ArgumentsEquivalent (first.map argumentMeaning) (last.map argumentMeaning) ↔
      first.map argumentCode = last.map argumentCode := by
  induction first generalizing last with
  | nil => cases last <;> simp [ArgumentsEquivalent]
  | cons head rest ih =>
      cases last with
      | nil => simp [ArgumentsEquivalent]
      | cons last tail =>
          simp only [List.map_cons, ArgumentsEquivalent, List.cons.injEq, ih]
          exact and_congr (CommonGroundScalarCasts.scalar_normalized_quote_exact head last) Iff.rfl

theorem nominal_meaning_exact (name otherName : Nat) (arguments otherArguments : List Scalar) :
    CommonNominalRoots.Subtype (meaning (.nominal name arguments))
      (meaning (.nominal otherName otherArguments)) ↔
      name = otherName ∧ arguments.map argumentCode = otherArguments.map argumentCode := by
  rw [meaning, meaning, CommonNominalRoots.nominal_root_invariant_exact]
  simp only [List.length_map]
  constructor
  · rintro ⟨identity, _, same⟩
    exact ⟨identity, (arguments_normalized_exact arguments otherArguments).mp same⟩
  · rintro ⟨identity, same⟩
    have size := congrArg List.length same
    exact ⟨identity, by simpa only [List.length_map] using size,
      (arguments_normalized_exact arguments otherArguments).mpr same⟩

/-- Every source and target of the explicitly stated ground grammar. The
normalization image is computed by `lower`, not assumed as a certificate. -/
theorem normalized_ground_compatibility_exact (source target : Ground) :
    fitsCommonGround.Rel (lower source) (lower target) ↔
      CommonNominalRoots.Subtype (meaning source) (meaning target) := by
  cases source with
  | scalar first =>
      cases target with
      | scalar last =>
          simp only [fitsCommonGround, Rel, lower, CommonGroundScalarCasts.read_quote,
            meaning, CommonNominalRoots.common_subtype_exact]
      | nominal name arguments =>
          simp only [fitsCommonGround, Rel, lower, CommonGroundScalarCasts.read_quote,
            CommonGroundScalarCasts.read, meaning, CommonNominalRoots.common_nominal_exact]
  | nominal name arguments =>
      cases target with
      | scalar last =>
          simp only [fitsCommonGround, Rel, lower, CommonGroundScalarCasts.read_quote,
            CommonGroundScalarCasts.read, meaning, CommonNominalRoots.nominal_common_exact]
      | nominal otherName otherArguments =>
          simp only [fitsCommonGround, Rel, lower, CommonGroundScalarCasts.read,
            Casts.Ty.nominal.injEq, nominal_meaning_exact]

theorem normalized_ground_check_exact (source target : Ground) :
    fitsCommonGround.check (lower source) (lower target) = true ↔
      CommonNominalRoots.Subtype (meaning source) (meaning target) :=
  (fitsCommonGround.exact _ _).trans (normalized_ground_compatibility_exact source target)

namespace Examples

private def integer : Scalar := .atom (.base .int)
private def string : Scalar := .atom (.base .str)

/-- Raw spelling order does not spuriously distinguish invariant arguments. -/
theorem reordered_union_arguments :
    fitsCommonGround.check (lower (.nominal 7 [.union integer string]))
      (lower (.nominal 7 [.union string integer])) = true := by decide +kernel

/-- Semantic scalar inclusion is not covariance of a nominal argument. -/
theorem invariant_argument_not_widened :
    fitsCommonGround.check (lower (.nominal 7 [integer]))
      (lower (.nominal 7 [.union integer string])) = false := by decide +kernel

end Examples

end Yulang.CommonGroundNominalCasts
