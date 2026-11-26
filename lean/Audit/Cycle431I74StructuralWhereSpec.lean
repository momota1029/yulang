import Yulang.GeneralDeclarativeI65I74StructuralWhereEntry431
import Yulang.GeneralDeclarativeI65I74StructuralWhereAuditSupport429

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereSpec431
open GeneralDeclarativeI65
open StructuralWhere427 StructuralWhere428 StructuralWhere431
open StructuralWhereAuditFixture429 StructuralWhereReadback427
open Checker408 (Problem Result)

def actualWire : Wire :=
  ⟨positiveWire,⟨parentEscape,nestedEscape⟩,⟨childEscape,scalarEscape⟩⟩

def actualReport : Result :=
  ⟨.selected 218 [.selected 219 []],.selected (.node 218 [.node 219 []]),[]⟩

theorem public_entry_accepts_actual_same_role_structural_where431 :
    check fixture actualReport (.originalStructuralWhere actualWire) = true := by decide +kernel

theorem visible_order_permutation_keeps_actual_original_where431 :
    check reversedFixture actualReport (.originalStructuralWhere
      {actualWire with selected := ⟨{rootHeadWire with ordinal := 1},4,{leafHeadWire with ordinal := 0},
        {blockedBase with declarationOrdinal := 0},{blockedCompound with declarationOrdinal := 1}⟩}) = true :=
  by decide +kernel

def actualPacket : ActualPair fixture.state fixture.root :=
  (readOriginal fixture actualWire).get (by decide +kernel)

theorem original_source_row_recovers_exact_child431 :
    (∃ a, readOriginal fixture actualWire = some a ∧ a.pair.original.rowOrdinal = 4 ∧
      a.pair.original.child.occurrence = [71,0] ∧
      a.pair.original.child.demand.role = fixture.root.demand.role ∧
      a.pair.original.name = 4 ∧ (a.pair.frame.names.input a.pair.original.binder).center = 3) := by
  have yes : (readOriginal fixture actualWire).isSome = true := by decide +kernel
  exact ⟨actualPacket,Option.eq_some_of_isSome yes,by decide +kernel⟩

theorem original_trace_selects_same_event_at_literal_ordinal_zero431 :
    TraceChild428 (actualSourceTrace431 actualPacket) 0 actualPacket.pair.original.child actualPacket.child :=
  selected_trace_keeps_real_child_event431 actualPacket

theorem wrong_row_and_wrong_display_are_not_admitted431 :
    check fixture actualReport (.originalStructuralWhere
      {actualWire with selected := {actualWire.selected with originalWhereRow := 5}}) = false ∧
    check fixture {actualReport with tree := .selected 218 [.selected 88 []]}
      (.originalStructuralWhere actualWire) = false ∧
    check fixture {actualReport with tree := .selected 218 []}
      (.originalStructuralWhere actualWire) = false ∧
    check fixture {actualReport with verdict := .selected (.node 218 [.node 88 []])}
      (.originalStructuralWhere actualWire) = false := by decide +kernel

theorem wrong_writes_and_unsupported_not_admitted431 :
    check fixture {actualReport with writes :=
      [⟨[71],0,0,⟨0,0⟩,.explicit ⟨0,0,.var 0⟩,.node 0 [] []⟩]}
      (.originalStructuralWhere actualWire) = false ∧
    check fixture actualReport .unsupported = false := by decide +kernel

theorem actual_entered_field_K2_not_admitted_as_structural431 :
    check cyclic actualReport (.originalStructuralWhere actualWire) = false := by decide +kernel

theorem same_role_original_result_has_dictionary_in_every_fit431
    (m : I72.Model) (fit : I72.Fits fixture.state m) :
    DictionaryEvidence fixture.state m fixture.root (.node 218 [.node 219 []]) :=
  dictionary_sound_R15 _ _ _
    (verified_R15_result_classifies_in_same_State431 _ _ _
      public_entry_accepts_actual_same_role_structural_where431).1 m fit

theorem actual_selected_same_role_is_nonvacuous431 :
    I72.Fits fixture.state model ∧
      DictionaryEvidence fixture.state model fixture.root (.node 218 [.node 219 []]) :=
  ⟨same_role_original_snapshot_fits427,
    same_role_original_result_has_dictionary_in_every_fit431 model same_role_original_snapshot_fits427⟩

#print axioms actual_pair_each_opposite_candidate_cannot_displace431
#print axioms dictionary_sound_R15
#print axioms OriginalWhereFromSource431
#print axioms actual_tree_has_no_support_or_writes431
#print axioms previous_entry_is_identical431
#print axioms previous_named_trace_retains_writes_and_support431
#print axioms check_sound
#print axioms verified_R15_result_classifies_in_same_State431
#print axioms public_entry_accepts_actual_same_role_structural_where431
#print axioms visible_order_permutation_keeps_actual_original_where431
#print axioms original_source_row_recovers_exact_child431
#print axioms original_trace_selects_same_event_at_literal_ordinal_zero431
#print axioms real_raw_root_cycle_never_selects_R15_431
#print axioms wrong_row_and_wrong_display_are_not_admitted431
#print axioms wrong_writes_and_unsupported_not_admitted431
#print axioms actual_entered_field_K2_not_admitted_as_structural431
#print axioms actual_selected_same_role_is_nonvacuous431

end Yulang.GeneralDeclarativeI65.I72.StructuralWhereSpec431
