import Yulang.TypeConstraintGraph

/-!
# Executed graph compilation from nested type terms

Every graph in these examples is generated from actual `TyTerm` inequalities.
No graph, realization, guessed type assignment, or external fuel is supplied to
the compiler or solver. Negative results are connected to all input assignments.
-/

namespace Yulang.TypeConstraintGraphExamples

open Inference StructuralBase TypeConstraintGraph

def pureJoin (_ _ : Unit) : Unit := ()
def pureRow (_ _ : Unit) : Prop := True
def pureCheck (_ _ : Unit) : Bool := true

theorem pureCheck_exact (left right : Unit) : pureCheck left right = true ↔ pureRow left right := by
  simp [pureCheck, pureRow]

abbrev PureModel := StructuralBase.model Unit () pureJoin pureRow

def identityApplication : Problem 2 :=
  [(.arrow (.var 0) .empty (.var 0) .empty,
    .arrow (.base .int) .empty (.var 1) .empty)]

theorem identity_allocates_only_five_nodes :
    (compile () pureJoin (fun _ => ()) identityApplication).map Compiled.size = some 5 := by decide +kernel

theorem identity_occurrences_share_the_input_node :
    (compile () pureJoin (fun _ => ()) identityApplication).map (fun compiled =>
      (List.finRange compiled.size).any fun node =>
        match compiled.graph node with
        | .arrow input _ output _ => decide (input = compiled.input 0) && decide (output = compiled.input 0)
        | _ => false) = some true := by decide +kernel

theorem identity_application_runs :
    (run () pureJoin pureCheck (fun _ => ()) identityApplication).status = .saturated := by decide +kernel

/-- The unknown function appears inside its own upper bound. The finite syntax
collector shares that occurrence and produces a cyclic constraint graph. -/
def selfApplication : Problem 2 := [(.var 0, .arrow (.var 0) .empty (.var 1) .empty)]

theorem self_application_runs :
    (run () pureJoin pureCheck (fun _ => ()) selfApplication).status = .saturated := by decide +kernel

def contravariantConflict : Problem 1 :=
  [(.arrow (.var 0) .empty (.base .str) .empty,
    .arrow (.base .int) .empty (.base .str) .empty),
   (.var 0, .base .str)]

theorem contravariant_conflict_rejected :
    (run () pureJoin pureCheck (fun _ => ()) contravariantConflict).status = .rejected := by decide +kernel

theorem contravariant_conflict_has_no_input_assignment :
    ¬ ∃ value : Fin 1 → Ty Unit, Holds PureModel (fun _ => ()) value contravariantConflict :=
  run_rejects () pureJoin pureCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureCheck_exact (fun _ => ()) contravariantConflict contravariant_conflict_rejected

def nestedPairConflict : Problem 1 :=
  [(.arrow (.base .int) .empty (.pair (.var 0) (.base .int)) .empty,
    .arrow (.var 0) .empty (.pair (.base .int) (.base .str)) .empty)]

theorem nested_pair_conflict_rejected :
    (run () pureJoin pureCheck (fun _ => ()) nestedPairConflict).status = .rejected := by decide +kernel

theorem nested_pair_conflict_has_no_input_assignment :
    ¬ ∃ value : Fin 1 → Ty Unit, Holds PureModel (fun _ => ()) value nestedPairConflict :=
  run_rejects () pureJoin pureCheck pureRow (fun _ => trivial) (fun _ _ => trivial)
    pureCheck_exact (fun _ => ()) nestedPairConflict nested_pair_conflict_rejected

def duplicateRecord : TyTerm (Fin 0) := .record 7 (.base .int) (.record 7 (.base .str) .emptyRecord)

theorem record_first_field_preserved :
    (run () pureJoin pureCheck Fin.elim0 [(duplicateRecord, .record 7 (.base .int) .emptyRecord)]).status =
      .saturated := by decide +kernel

theorem hidden_record_field_cannot_supply_str :
    (run () pureJoin pureCheck Fin.elim0 [(duplicateRecord, .record 7 (.base .str) .emptyRecord)]).status =
      .rejected := by decide +kernel

theorem variant_payload_is_compiled :
    (run () pureJoin pureCheck (m := 0) Fin.elim0
      [(.variant 9 (.base .int), .variant 9 (.base .str))]).status = .rejected := by decide +kernel

theorem union_left_and_intersection_right_are_split :
    splitProblem (m := 0) [(.union (.base .int) (.base .str), .inter .top .top)] =
      some [(.base .int, .top), (.base .int, .top), (.base .str, .top), (.base .str, .top)] := by decide +kernel

theorem split_lattice_constraints_run :
    (run () pureJoin pureCheck (m := 0) Fin.elim0
      [(.union (.base .int) (.base .str), .inter .top .top)]).status = .saturated := by decide +kernel

theorem split_union_conflict_rejected :
    (run () pureJoin pureCheck (m := 0) Fin.elim0
      [(.union (.base .int) (.base .str), .base .int)]).status = .rejected := by decide +kernel

theorem union_right_is_unsupported :
    (run () pureJoin pureCheck (m := 0) Fin.elim0
      [(.base .int, .union (.base .int) (.base .str))]).status = .unsupported := by decide +kernel

theorem unsupported_union_right_has_a_model :
    Holds PureModel (m := 0) Fin.elim0 Fin.elim0
      [(.base .int, .union (.base .int) (.base .str))] := by
  intro edge member
  simp only [List.mem_singleton] at member
  subst edge
  exact .unionLeft _ _

def openRecord : Problem 2 := [(.record 0 (.var 0) (.var 1), .top)]

theorem unknown_record_spine_is_unsupported :
    (run () pureJoin pureCheck (fun _ => ()) openRecord).status = .unsupported := by decide +kernel

theorem unsupported_record_spine_has_every_assignment (value : Fin 2 → Ty Unit) :
    Holds PureModel (fun _ => ()) value openRecord := by
  intro edge member
  simp only [openRecord, List.mem_singleton] at member
  subst edge
  exact .top _

def numericRows (index : Fin 2) : Nat := if index = 0 then 1 else 2

def inputRowConflict : Problem 2 :=
  [(.arrow (.base .int) (.var 0) (.base .int) .empty,
    .arrow (.base .int) (.var 1) (.base .int) .empty)]

def outputRowConflict : Problem 2 :=
  [(.arrow (.base .int) .empty (.base .int) (.var 1),
    .arrow (.base .int) .empty (.base .int) (.var 0))]

theorem arrow_input_rows_keep_their_direction :
    (run 0 Nat.max (fun a b => decide (a ≤ b)) numericRows inputRowConflict).status = .rejected := by decide +kernel

theorem arrow_output_rows_keep_their_direction :
    (run 0 Nat.max (fun a b => decide (a ≤ b)) numericRows outputRowConflict).status = .rejected := by decide +kernel

end Yulang.TypeConstraintGraphExamples
