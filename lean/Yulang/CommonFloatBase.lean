import Yulang.CommonNominalModel
import Yulang.CoreExpr
import Yulang.Binary64

/-!
# Literal and binary64 carriers in the extended Common base layer

The four legacy base identities are retained and float is a distinct dedicated
base. Payloads, including NaN words and signed zero, are retained as source
data; their pattern equality does not redefine their static type.

This module closes the literal leaf's finite constraints and zero-parameter
family. It does not claim nominal/list expression inference or an old Common
embedding theorem for arbitrary non-scalar types.
-/

namespace Yulang.CommonFloatBase

open CommonNominalCarrier
open Core.PresenceGeneration (Comp CompTerm)

inductive Base where
  | legacy : Inference.Base → Base
  | float
  deriving DecidableEq, Repr

def Base.meaning : Base → Ty
  | .legacy scalar => .base scalar
  | .float => .float

def literalBase : LiteralValues.Literal F → Base
  | .int _ => .legacy .int
  | .float _ => .float
  | .str _ => .legacy .str
  | .bool _ => .legacy .bool
  | .unit => .legacy .unit

def literalType (literal : LiteralValues.Literal F) : Ty := (literalBase literal).meaning

/-- Every payload of each literal kind has its one static base type. The float
carrier is unrestricted here, and is instantiated by binary64 below. -/
theorem base_subtype_exact (first last : Base) :
    Subtype first.meaning last.meaning ↔ first = last := by
  constructor
  · intro below
    let environment : CommonNominalFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
    cases first with
    | legacy first =>
        cases last with
        | legacy last =>
            have same := (CommonNominalFinite.producerLe_iff_probe _ _).mp (below 0)
              0 environment (.base last) (by rfl)
            change first = last at same
            exact congrArg Base.legacy same
        | float =>
            have impossible := (CommonNominalFinite.producerLe_iff_probe _ _).mp (below 0)
              0 environment .float trivial
            contradiction
    | float =>
        cases last with
        | legacy last =>
            have impossible := (CommonNominalFinite.producerLe_iff_probe _ _).mp (below 0)
              0 environment (.base last) (by rfl)
            contradiction
        | float => rfl
  · rintro rfl
    exact subtype_refl _

theorem float_distinct_from_legacy (scalar : Inference.Base) :
    ¬ Subtype (Base.meaning .float) (Base.meaning (.legacy scalar)) ∧
      ¬ Subtype (Base.meaning (.legacy scalar)) (Base.meaning .float) := by
  simp [base_subtype_exact]

/-- Source typing is independent of the generated finite constraint object. -/
inductive Typing (signature : Core.Signature) :
    List Ty → Core.Expr signature → Comp model → Prop where
  | literal : Subtype (literalType value) result.1 → Common.rowLe Common.rowEmpty result.2 →
      Typing signature environment (.literal value) result
  | marker : Subtype (.base scalar) result.1 → Common.rowLe Common.rowEmpty result.2 →
      Typing signature environment (.lit scalar) result

/-- A finite base-bound constraint and the original symbolic output. No
source-typing judgment or arbitrary semantic predicate is stored as an atom. -/
structure Constraint (α : Type) where
  base : Base
  output : CompTerm α

def Constraint.Models (assignment : α → Comp model) (constraint : Constraint α) : Prop :=
  Subtype constraint.base.meaning (constraint.output.eval model assignment).1 ∧
    Common.rowLe Common.rowEmpty (constraint.output.eval model assignment).2

def generate (literal : LiteralValues.Literal F) (output : CompTerm α) : Constraint α :=
  ⟨literalBase literal, output⟩

/-- Arbitrary signature (including a nonempty Float carrier), environment,
literal payload, output term and assignment; no solver-success premise. -/
theorem generate_literal_exact (signature : Core.Signature) (environment : List Ty)
    (literal : LiteralValues.Literal signature.Float) (output : CompTerm α)
    (assignment : α → Comp model) :
    (generate literal output).Models assignment ↔
      Typing signature environment (.literal literal) (output.eval model assignment) := by
  constructor
  · rintro ⟨type, row⟩
    exact .literal type row
  · intro typed
    cases typed with
    | literal type row => exact ⟨type, row⟩

structure Scheme where
  base : Base

def Scheme.instantiate (scheme : Scheme) (_parameters : PUnit) : Comp model :=
  (scheme.base.meaning, Common.rowEmpty)

def infer (literal : LiteralValues.Literal F) : List Scheme := [⟨literalBase literal⟩]

theorem literal_all_parameters (signature : Core.Signature) (environment : List Ty)
    (literal : LiteralValues.Literal signature.Float) (scheme : Scheme)
    (returned : scheme ∈ infer literal) (parameters : PUnit) :
    Typing signature environment (.literal literal) (scheme.instantiate parameters) := by
  have same : scheme = ⟨literalBase literal⟩ := List.mem_singleton.mp returned
  subst scheme
  exact .literal (subtype_refl _) (Common.rowLe_refl _)

theorem literal_all_models (signature : Core.Signature) (environment : List Ty)
    (literal : LiteralValues.Literal signature.Float) (result : Comp model) :
    Typing signature environment (.literal literal) result ↔
      ∃ scheme ∈ infer literal, ∃ parameters : PUnit,
        Comp.le model (scheme.instantiate parameters) result := by
  constructor
  · intro typed
    cases typed with
    | literal type row => exact ⟨⟨literalBase literal⟩, by simp [infer], ⟨⟩, type, row⟩
  · rintro ⟨scheme, returned, parameters, type, row⟩
    have same : scheme = ⟨literalBase literal⟩ := List.mem_singleton.mp returned
    subst scheme
    exact .literal type row

/-- Retain all other signature carriers while using the actual 64-bit model. -/
def binary64Signature (signature : Core.Signature) : Core.Signature :=
  { signature with Float := Binary64.Value }

@[simp] theorem binary64_literal_type (value : Binary64.Value) :
    literalType (.float value) = Base.meaning .float := rfl

/-- Every one of the 2^64 storage words has the float static type. No numeric
equality or finite/non-NaN premise is imposed by literal typing. -/
theorem binary64_word_typing (signature : Core.Signature) (environment : List Ty)
    (word : Fin (2 ^ 64)) :
    Typing (binary64Signature signature) environment
      (.literal (.float (Binary64.ofWord word)))
      (Base.meaning .float, Common.rowEmpty) :=
  .literal (subtype_refl _) (Common.rowLe_refl _)

end Yulang.CommonFloatBase
