import Yulang.StructuralDecisions

/-!
# Ground subtype decisions with unions, records and signed latent effects

Negative cases use the completeness theorem, so they exclude every derivation
in the existing reference preorder, including arbitrary transitivity cuts.
-/

namespace Yulang.StructuralDecisions.Examples

open StructuralBase

abbrev T := SignedStructural.Ty 1 Nat

def integer : T := .base .int
def string : T := .base .str
def unit : T := .base .unit

def debt : Directed.Occurrence 1 Nat := Directed.release 0 Directed.allowNone (Directed.raw 0)
def shield : Directed.Occurrence 1 Nat := Directed.protect 0 Directed.allowNone (Directed.raw 0)

def shadowed : T := .record 0 integer (.record 0 string (.record 1 unit .emptyRecord))


theorem union_order_equivalent :
    equivalentSigned (.union integer string) (.union string integer) = true := by decide +kernel

theorem lattice_absorption :
    equivalentSigned (.inter (.union integer string) integer) integer = true := by decide +kernel

theorem source_union_checks_every_branch :
    ¬ SignedStructural.Subtype (.union integer string) integer :=
  (checkSigned_rejects _ _).mp (by decide +kernel)

theorem pair_covariance :
    checkSigned (.pair integer string)
      (.pair (.union integer string) (.union string unit)) = true := by decide +kernel

theorem variant_payload_covariance :
    checkSigned (.union (.variant 7 integer) (.variant 7 string))
      (.variant 7 (.union integer string)) = true := by decide +kernel

theorem variant_label_mismatch :
    ¬ SignedStructural.Subtype (.variant 7 integer) (.variant 8 integer) :=
  (checkSigned_rejects _ _).mp (by decide +kernel)

theorem record_width_and_first_field :
    checkSigned shadowed (.record 0 integer .emptyRecord) = true := by decide +kernel

theorem hidden_field_cannot_supply_required_type :
    ¬ SignedStructural.Subtype shadowed (.record 0 string .emptyRecord) :=
  (checkSigned_rejects _ _).mp (by decide +kernel)

theorem missing_record_field_rejected :
    ¬ SignedStructural.Subtype shadowed (.record 2 integer .emptyRecord) :=
  (checkSigned_rejects _ _).mp (by decide +kernel)

theorem arrow_variance_including_both_rows :
    checkSigned
      (.arrow (.union integer string) [Directed.raw 0, debt] integer [shield])
      (.arrow integer [Directed.raw 0] (.union integer string) [shield, Directed.raw 1]) = true :=
  by decide +kernel

theorem arrow_input_wrong_direction_rejected :
    ¬ SignedStructural.Subtype
      (.arrow integer [] integer [])
      (.arrow (.union integer string) [] integer []) :=
  (checkSigned_rejects _ _).mp (by decide +kernel)

theorem negative_balance_is_not_erased :
    ¬ SignedStructural.Subtype
      (.arrow unit [] unit [debt]) (.arrow unit [] unit []) :=
  (checkSigned_rejects _ _).mp (by decide +kernel)

theorem protected_balance_is_not_raw :
    ¬ SignedStructural.Subtype
      (.arrow unit [] unit [shield]) (.arrow unit [] unit [Directed.raw 0]) :=
  (checkSigned_rejects _ _).mp (by decide +kernel)

theorem finite_row_order_irrelevant :
    equivalentSigned
      (.arrow unit [] unit [debt, shield, debt])
      (.arrow unit [] unit [shield, debt]) = true := by decide +kernel

/-! `any` is the writable top type from decision 36. It forgets value
structure while leaving latent row comparisons on arrows intact. -/

theorem every_type_is_below_any (type : T) : checkSigned type .top = true :=
  (checkSigned_exact _ _).mpr (.top _)

theorem any_is_not_an_integer : checkSigned (.top : T) integer = false := by decide +kernel

theorem any_is_not_callable :
    checkSigned (.top : T) (.arrow integer [] integer []) = false := by decide +kernel

theorem any_meet_and_join :
    equivalentSigned (.inter integer .top) integer = true ∧
      equivalentSigned (.union integer .top) .top = true := by decide +kernel

theorem any_arrow_input_is_contravariant :
    checkSigned (.arrow .top [] integer []) (.arrow integer [] integer []) = true ∧
      checkSigned (.arrow integer [] integer []) (.arrow .top [] integer []) = false := by
  decide +kernel

theorem any_input_preserves_protected_latent_effects :
    ¬ SignedStructural.Subtype
      (.arrow .top [] integer [shield]) (.arrow integer [] integer []) :=
  (checkSigned_rejects _ _).mp (by decide +kernel)

theorem any_input_preserves_negative_latent_effects :
    ¬ SignedStructural.Subtype
      (.arrow .top [] integer [debt]) (.arrow integer [] integer []) :=
  (checkSigned_rejects _ _).mp (by decide +kernel)

end Yulang.StructuralDecisions.Examples
