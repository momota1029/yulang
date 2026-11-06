import Yulang.TypeSimplification

/-!
# Executable simplification and all-instance regressions

The examples use the existing type syntax and subtype relation. In particular,
the mixed identity parameter is retained, and an unsafe diagonal merge loses a
real `int -> str` instance. None of these tests relies on a distributive law.
-/

namespace Yulang.TypeSimplificationExamples

open Inference StructuralBase TypeSimplification

def identity : TyTerm (Fin 1) := .arrow (.var 0) .empty (.var 0) .empty

theorem identity_is_mixed : occurs true 0 identity = true ∧ occurs false 0 identity = true :=
  ⟨rfl, rfl⟩

theorem identity_parameter_is_shared : simplify identity = identity := rfl

def ignoredArgument : TyTerm (Fin 1) := .arrow (.var 0) .empty (.base .int) .empty

theorem negative_parameter_becomes_any :
    simplify ignoredArgument = .arrow .top .empty (.base .int) .empty := rfl

theorem positive_parameter_becomes_never :
    simplify (n := 1) (.pair (.var 0) (.base .int)) = .pair .bottom (.base .int) := rfl

/-- The two slots' value components disappear in opposite directions, while
both row components retain their original, independent assignment. -/
theorem value_simplification_preserves_row_variables :
    simplify (n := 2) (.arrow (.var 0) (.var 0) (.var 1) (.var 1)) =
      .arrow .top (.var 0) .bottom (.var 1) := rfl

theorem variable_record_tail_is_unsupported :
    simplifyChecked (n := 2) (.record 0 (.var 0) (.var 1)) = none := rfl

def positiveCooccurrence : TyTerm (Fin 2) :=
  .arrow (.var 0) .empty
    (.arrow (.var 1) .empty (.union (.var 0) (.var 1)) .empty) .empty

theorem positive_cooccurrence_checked :
    mergeCheck true 0 1 positiveCooccurrence = true := by decide +kernel

def negativeCooccurrence : TyTerm (Fin 2) :=
  .arrow (.inter (.var 0) (.var 1)) .empty (.pair (.var 0) (.var 1)) .empty

theorem negative_cooccurrence_checked :
    mergeCheck false 0 1 negativeCooccurrence = true := by decide +kernel

def primitiveSandwich : TyTerm (Fin 1) :=
  .arrow (.inter (.var 0) (.base .int)) .empty (.union (.var 0) (.base .int)) .empty

theorem primitive_sandwich_checked :
    sandwichCheck 0 (.base .int) primitiveSandwich = true := by decide +kernel

def independentArrow : TyTerm (Fin 2) := .arrow (.var 0) .empty (.var 1) .empty

theorem independent_parameters_are_not_merged :
    mergeChecked 0 1 independentArrow = none := by decide +kernel

def rowJoin (_ _ : Unit) : Unit := ()
def rowLe (_ _ : Unit) : Prop := True

theorem positive_cooccurrence_preserves_all_instances (expected : Ty Unit) :
    Instances () rowJoin rowLe (fun _ => ()) (merge 0 1 positiveCooccurrence) expected ↔
      Instances () rowJoin rowLe (fun _ => ()) positiveCooccurrence expected :=
  merge_instances_exact () rowJoin rowLe (fun _ => trivial) (fun _ _ => trivial)
    (fun _ => ()) true 0 1 positiveCooccurrence positive_cooccurrence_checked expected

theorem negative_cooccurrence_preserves_all_instances (expected : Ty Unit) :
    Instances () rowJoin rowLe (fun _ => ()) (merge 0 1 negativeCooccurrence) expected ↔
      Instances () rowJoin rowLe (fun _ => ()) negativeCooccurrence expected :=
  merge_instances_exact () rowJoin rowLe (fun _ => trivial) (fun _ _ => trivial)
    (fun _ => ()) false 0 1 negativeCooccurrence negative_cooccurrence_checked expected

theorem primitive_sandwich_preserves_all_instances (expected : Ty Unit) :
    Instances () rowJoin rowLe (fun _ => ()) (sandwich 0 (.base .int) primitiveSandwich) expected ↔
      Instances () rowJoin rowLe (fun _ => ()) primitiveSandwich expected :=
  sandwich_instances_exact () rowJoin rowLe (fun _ => trivial) (fun _ _ => trivial)
    (fun _ => ()) 0 (.base .int) primitiveSandwich primitive_sandwich_checked expected

private theorem identity_cannot_map_int_to_str (type : Ty Unit) :
    ¬ Subtype rowLe (.arrow type () type ()) (.arrow (.base .int) () (.base .str) ()) := by
  intro subtype
  have comparison := StructuralDecisions.Comparison.complete
    (leRow := rowLe) (fun _ _ => trivial) subtype
  cases comparison with
  | arrow input _ output _ => exact int_not_str (.trans input.sound output.sound)
  | record sourceShape _ _ _ => cases sourceShape

/-- Replacing unrelated parameters by a shared one would lose an actual
instance. The sufficient merge checker therefore has a non-vacuous rejection. -/
theorem an_unchecked_merge_loses_an_instance :
    Instances () rowJoin rowLe (fun _ => ()) independentArrow
        (.arrow (.base .int) () (.base .str) ()) ∧
      ¬ Instances () rowJoin rowLe (fun _ => ()) (merge 0 1 independentArrow)
        (.arrow (.base .int) () (.base .str) ()) := by
  constructor
  · refine ⟨fun i => if i = 0 then .base .int else .base .str, ?_⟩
    exact .refl _
  · rintro ⟨value, fits⟩
    exact identity_cannot_map_int_to_str (value 1) fits

theorem automatic_pass_preserves_identity : simplifyAll identity = identity := by decide +kernel

theorem automatic_pass_merges_positive_cooccurrence :
    simplifyAll positiveCooccurrence =
      .arrow (.var 1) .empty
        (.arrow (.var 1) .empty (.union (.var 1) (.var 1)) .empty) .empty := by decide +kernel

theorem automatic_pass_eliminates_primitive_sandwich :
    simplifyAll primitiveSandwich =
      .arrow (.inter (.base .int) (.base .int)) .empty
        (.union (.base .int) (.base .int)) .empty := by decide +kernel

theorem automatic_pass_preserves_all_instances (term : TyTerm (Fin n)) (expected : Ty Unit) :
    Instances () rowJoin rowLe (fun _ => ()) (simplifyAll term) expected ↔
      Instances () rowJoin rowLe (fun _ => ()) term expected :=
  simplifyAll_instances_exact () rowJoin rowLe (fun _ => trivial) (fun _ _ => trivial)
    (fun _ => ()) term expected

end Yulang.TypeSimplificationExamples
