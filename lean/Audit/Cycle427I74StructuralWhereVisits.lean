import Yulang.GeneralDeclarativeI65I74StructuralWhereVisit427
import Yulang.GeneralDeclarativeI65I74StructuralWhereAuditSupport429

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereVisits427
open GeneralDeclarativeI65
open StructuralWhere427 StructuralWhereAuditFixture429 StructuralWhereReadback427
open GeneralDeclarativeInspect321 (PatternK2 Visit)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeK2Alias321 (AliasCycle)

def parentSites : ExactRecordVisitWire427 := ⟨parentEscape,nestedEscape⟩
def childSites : ExactRecordVisitWire427 := ⟨childEscape,scalarEscape⟩

theorem checked_complete_candidate_lists_do_not_hide_raw_K2_at_either_call427 :
    (∀ d ∈ visible fixture.state.core fixture.root,
      ∃ src code, d.head = [src] ∧ translateWhere427 fixture.state.core src = some code ∧
        ¬ PatternK2 fixture.state.core.current.ordinary rebuilt.parentRival.found.root code) ∧
    (∀ d ∈ visible fixture.state.core rebuilt.original.child,
      ∃ src code, d.head = [src] ∧ translateWhere427 fixture.state.core src = some code ∧
        ¬ PatternK2 fixture.state.core.current.ordinary rebuilt.childRival.found.root code) :=
  whole_pair_preserves_original_raw_K2_for_both_complete_candidate_lists427
    (p:=rebuilt) (parent:=parentSites) (child:=childSites) (by decide +kernel)

def extra (label : Nat) : List GeneralDeclarativeHead320.Equation :=
  rows ++ [RecordK2412.recordRow412 0 label 8,RecordK2412.recordRow412 8 41 8]
def outside : Checker408.Problem := (build (ordinary := extra 40)).get (by decide +kernel)
def hiddenSameField : Checker408.Problem := (build (ordinary := extra 30)).get (by decide +kernel)
def outsideRoot : List410.ExactEscapeWire := ⟨[0,1,2,3,4,5,6,7,8],[0,1,2,1,2,2,2,2,1]⟩
def outsideInner : List410.ExactEscapeWire := ⟨[0,1,2,3,4,5,6,7,8],[2,0,2,1,2,2,2,2,2]⟩
def outsideSites : ExactRecordVisitWire427 := ⟨outsideRoot,outsideInner⟩
def outsideCycle : RecordK2412.FieldCycleWire := ⟨⟨9,.same,8⟩,[],.same⟩

theorem a_reachable_off_query_field_cycle_is_not_a_visited_candidate_K2427 :
    structural outside.state.core.current.ordinary 0 (.record [(40,8)]) ∧
    AliasCycle outside.state.core.current.ordinary (observed outside.state.core.current.ordinary) 8 ∧
    ¬ PatternK2 outside.state.core.current.ordinary 0 (RecordK2412.query412 30 31 8) := by
  refine ⟨?_,RecordK2412.cycle_at_sound412 (w:=outsideCycle) (by decide +kernel),?_⟩
  · exact GeneralDeclarativeGraphRows321.literal_head
      (List.mem_of_getElem? (show outside.state.core.current.ordinary.equations[8]? =
        some (RecordK2412.recordRow412 0 40 8) from by decide +kernel)) rfl
  · exact checked_literal_record_candidate_preserves_raw_K2_priority427
      (known:=1) (w:=outsideSites) (by decide +kernel) (.inr ⟨31,8,rfl⟩)

theorem same_label_alternate_row_cannot_be_hidden_by_one_positive_trace427 :
    checkExactRecordVisits427 hiddenSameField.state.core.current.ordinary 0 30 1 outsideSites = false ∧
    PatternK2 hiddenSameField.state.core.current.ordinary 0 (RecordK2412.query412 30 31 8) := by
  refine ⟨by decide +kernel,8,?_,RecordK2412.cycle_at_sound412 (w:=outsideCycle) (by decide +kernel)⟩
  have field := GeneralDeclarativeGraphRows321.literal_head
    (List.mem_of_getElem? (show hiddenSameField.state.core.current.ordinary.equations[8]? =
      some (RecordK2412.recordRow412 0 30 8) from by decide +kernel)) rfl
  exact .field field List.mem_cons_self List.mem_cons_self (.here .record)

#print axioms literal_record_candidate_visits_only_original_root_or_field427
#print axioms whole_pair_preserves_original_raw_K2_for_both_complete_candidate_lists427
#print axioms checked_complete_candidate_lists_do_not_hide_raw_K2_at_either_call427
#print axioms a_reachable_off_query_field_cycle_is_not_a_visited_candidate_K2427
#print axioms same_label_alternate_row_cannot_be_hidden_by_one_positive_trace427
end Yulang.GeneralDeclarativeI65.I72.StructuralWhereVisits427
