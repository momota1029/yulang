import Yulang.GeneralDeclarativeI65I74OrderedProjectionCut464

namespace Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeHead320 (Equation State)
open Yulang.GeneralDeclarativeI65.I72.List410 (ExactEscapeWire)
#print axioms every_checked_append_result_reads_exact_order
#print axioms ordered_append_exact_independent_guard
#print axioms literal_row_order_and_ordinary_constraints_are_exact
#print axioms accepted_old_row_ordinal_is_unchanged
#print axioms accepted_new_row_has_exact_appended_ordinal
#print axioms accepted_batch_preserves_exact_original_aliases
#print axioms accepted_batch_preserves_every_exact_original_k2
#print axioms batch_keeps_all_original_ordinary_models_under_separate_entailment

private def start : State := ⟨⟨[],[]⟩,[]⟩
private def field (left child : Nat) : Equation :=
  ⟨left,.record 30 (.variable child) (.primitive .emptyRecord [])⟩
private def cutAt (root child : Nat) : ExactEscapeWire :=
  ⟨List.range 8,(List.range 8).map fun n => if n = root then 0 else if n = child then 1 else 2⟩
private def proposed (a b : Nat) : CheckedAppendData := ⟨field a b,cutAt a b⟩

/- Checking rows one by one against an unchanged initial snapshot is not
enough: separately each of the two opposed edges passes. -/
#guard (readOrderedAppends start [proposed 1 2]).isSome &&
  (readOrderedAppends start [proposed 2 1]).isSome

-- In the real ordered read the earlier new edge is already present.
#guard (readOrderedAppends start [proposed 1 2,proposed 2 1]).isNone

-- Finite explicit safe prefix with real append order.
#guard (readOrderedAppends start [proposed 1 2,proposed 2 3]).any
  (fun s => s.equations.map Equation.left == [1,2])
end Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
