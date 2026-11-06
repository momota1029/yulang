import Yulang.TypeConstraintInference

/-!
# Principal inference executed on actual nested type terms

Every example calls the public compiler-and-solver entry. No prebuilt graph,
successful cache, guessed recursive type, or caller fuel is supplied. Positive
results are related to all original source instances in the common inference
carrier; negative results exclude all source assignments in that carrier.
-/

namespace Yulang.TypeConstraintInferenceExamples

open Inference TypeConstraintGraph TypeConstraintInference

def pureJoin (_ _ : Unit) : Unit := ()
def pureRow (_ _ : Unit) : Prop := True
def pureCheck (_ _ : Unit) : Bool := true

theorem pureCheck_exact (left right : Unit) : pureCheck left right = true ↔ pureRow left right := by
  simp [pureCheck, pureRow]

abbrev PureModel := RegularInferenceModel.model Unit () pureJoin pureRow

def identityApplication : Problem 2 :=
  [(.arrow (.var 0) .empty (.var 0) .empty,
    .arrow (.base .int) .empty (.var 1) .empty)]

theorem identity_application_infers :
    (infer () pureJoin pureCheck (fun _ => ()) identityApplication).status = .inferred := by decide +kernel

theorem identity_application_instances_exact (expected : Value Unit) :
    SourceInstance () pureJoin pureRow (fun _ => ()) identityApplication 1 expected ↔
      (infer () pureJoin pureCheck (fun _ => ()) identityApplication).Instance pureRow 1 expected :=
  infer_instances_exact () pureJoin pureCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureCheck_exact (fun _ => ()) identityApplication (by decide +kernel) 1 expected

theorem identity_application_integer_instance :
    (infer () pureJoin pureCheck (fun _ => ()) identityApplication).Instance pureRow 1 (.base .int) := by
  apply (identity_application_instances_exact (.base .int)).mp
  refine ⟨fun _ => .base .int, ?_, RegularInferenceModel.subtype_refl pureRow _⟩
  intro edge present
  simp only [identityApplication, List.mem_singleton] at present
  subst edge
  exact RegularInferenceModel.subtype_refl pureRow _

/-- The same unknown occurs as the function and its own argument. The source
collector preserves that shared occurrence and the inferred scheme is regular. -/
def selfApplication : Problem 2 := [(.var 0, .arrow (.var 0) .empty (.var 1) .empty)]

theorem self_application_infers :
    (infer () pureJoin pureCheck (fun _ => ()) selfApplication).status = .inferred := by decide +kernel

theorem self_application_instances_exact (output : Fin 2) (expected : Value Unit) :
    SourceInstance () pureJoin pureRow (fun _ => ()) selfApplication output expected ↔
      (infer () pureJoin pureCheck (fun _ => ()) selfApplication).Instance pureRow output expected :=
  infer_instances_exact () pureJoin pureCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureCheck_exact (fun _ => ()) selfApplication (by decide +kernel) output expected

theorem self_application_every_parameter_solves
    (scheme : Scheme 2 Unit)
    (returned : infer () pureJoin pureCheck (fun _ => ()) selfApplication = .inferred scheme)
    (parameter : Fin scheme.size → Value Unit) :
    Holds PureModel (fun _ => ()) (scheme.instantiate parameter) selfApplication :=
  infer_inferred_sound () pureJoin pureCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureCheck_exact (fun _ => ()) selfApplication scheme returned parameter

/-- Both directions explicitly demand a recursive arrow equation, rather
than merely allowing bottom as a value below a function upper bound. -/
def recursiveArrowEquation : Problem 2 :=
  [(.var 0, .arrow (.var 0) .empty (.var 1) .empty),
   (.arrow (.var 0) .empty (.var 1) .empty, .var 0)]

theorem recursive_arrow_equation_infers :
    (infer () pureJoin pureCheck (fun _ => ()) recursiveArrowEquation).status = .inferred := by decide +kernel

theorem recursive_arrow_equation_has_a_model :
    ∃ input : Fin 2 → Value Unit, Holds PureModel (fun _ => ()) input recursiveArrowEquation :=
  ((infer_inferred_iff () pureJoin pureCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureCheck_exact (fun _ => ()) recursiveArrowEquation).mp recursive_arrow_equation_infers).2

def contravariantConflict : Problem 1 :=
  [(.arrow (.var 0) .empty (.base .str) .empty,
    .arrow (.base .int) .empty (.base .str) .empty),
   (.var 0, .base .str)]

theorem contravariant_conflict_rejected :
    (infer () pureJoin pureCheck (fun _ => ()) contravariantConflict).status = .rejected := by decide +kernel

theorem contravariant_conflict_has_no_recursive_model :
    ¬ ∃ input : Fin 1 → Value Unit, Holds PureModel (fun _ => ()) input contravariantConflict :=
  ((infer_rejected_iff () pureJoin pureCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureCheck_exact (fun _ => ()) contravariantConflict).mp contravariant_conflict_rejected).2

def nestedPairConflict : Problem 1 :=
  [(.arrow (.base .int) .empty (.pair (.var 0) (.base .int)) .empty,
    .arrow (.var 0) .empty (.pair (.base .int) (.base .str)) .empty)]

theorem nested_pair_conflict_rejected :
    (infer () pureJoin pureCheck (fun _ => ()) nestedPairConflict).status = .rejected := by decide +kernel

theorem nested_pair_conflict_has_no_recursive_model :
    ¬ ∃ input : Fin 1 → Value Unit, Holds PureModel (fun _ => ()) input nestedPairConflict :=
  ((infer_rejected_iff () pureJoin pureCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureCheck_exact (fun _ => ()) nestedPairConflict).mp nested_pair_conflict_rejected).2

def unknownRecordTail : Problem 2 := [(.record 0 (.var 0) (.var 1), .top)]

theorem unknown_record_tail_is_unsupported :
    (infer () pureJoin pureCheck (fun _ => ()) unknownRecordTail).status = .unsupported := by decide +kernel

theorem unsupported_record_tail_has_every_assignment (input : Fin 2 → Value Unit) :
    Holds PureModel (fun _ => ()) input unknownRecordTail := by
  intro edge present
  simp only [unknownRecordTail, List.mem_singleton] at present
  subst edge
  exact RegularInferenceModel.subtype_top pureRow _

theorem union_on_target_is_unsupported :
    (infer () pureJoin pureCheck (m := 0) Fin.elim0
      [(.base .int, .union (.base .int) (.base .str))]).status = .unsupported := by decide +kernel

end Yulang.TypeConstraintInferenceExamples
