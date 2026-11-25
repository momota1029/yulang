import Yulang.GeneralDeclarativeI65I74StructuralWherePairRead427
import «Cycle427I74StructuralWhereSameRole»

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2400
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereReadback427
open GeneralDeclarativeI65
open StructuralWhere427
open StructuralWhereSameRole427
open GeneralDeclarativeWitnessDeclaredState357 (point)

def emptyEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,2,0,2,2]⟩
def rootHeadWire : PositiveHeadWire427 :=
  ⟨0,0,2,parentEscape,nestedEscape,emptyEscape,.nested 1 2 scalarEscape emptyEscape⟩
def leafHeadWire : PositiveHeadWire427 :=
  ⟨1,5,2,childEscape,scalarEscape,emptyEscape,.scalar 3⟩
def positiveWire : PositivePairWire427 :=
  ⟨rootHeadWire,4,leafHeadWire,blockedBase,blockedCompound⟩
theorem positiveWire_some :
    (readOriginalPositivePair427 fixture.state.core fixture.root positiveWire).isSome = true := by decide +kernel
def rebuilt : ReadPositivePair427 fixture.state.core fixture.root :=
  (readOriginalPositivePair427 fixture.state.core fixture.root positiveWire).get positiveWire_some

theorem executable_original_where_rebuilds_exact_child_and_center427 :
    rebuilt.frame.decl.id = 218 ∧ rebuilt.childFrame.decl.id = 219 ∧
    rebuilt.original.child.occurrence = [71,0] ∧
    rebuilt.original.child.demand.role = fixture.root.demand.role ∧
    rebuilt.original.name = 4 ∧ rebuilt.original.binder = 8 ∧
    (rebuilt.frame.names.input rebuilt.original.binder).center = 3 := by decide +kernel

theorem executable_original_where_produces_same_model_dictionary427 :
    I72.DictionaryEvidence fixture.state model fixture.root (.node 218 [.node 219 []]) := by
  have evidence := read_original_structural_pair_exact_fixed_dictionary427
    (w:=positiveWire) (p:=rebuilt) (Option.eq_some_of_isSome positiveWire_some)
    fixture.state.b6 model same_role_original_snapshot_fits427
  rw [executable_original_where_rebuilds_exact_child_and_center427.1,
    executable_original_where_rebuilds_exact_child_and_center427.2.1] at evidence
  exact evidence

theorem executable_original_where_is_not_just_any_candidate427 :
    (readOriginalPositivePair427 fixture.state.core fixture.root
      {positiveWire with originalWhereRow := 5}).isNone = true ∧
    (readOriginalPositivePair427 fixture.state.core fixture.root
      {positiveWire with child := {leafHeadWire with ordinal := 0}}).isNone = true ∧
    (readOriginalPositivePair427 fixture.state.core fixture.root
      {positiveWire with parent := {rootHeadWire with payload := .nested 0 2 scalarEscape emptyEscape}}).isNone = true ∧
    (readOriginalPositivePair427 cyclic.state.core cyclic.root positiveWire).isNone = true := by decide +kernel

def reversedWire : PositivePairWire427 :=
  ⟨{rootHeadWire with ordinal := 1},4,{leafHeadWire with ordinal := 0},
    {blockedBase with declarationOrdinal := 0},{blockedCompound with declarationOrdinal := 1}⟩

def rebuiltReverse : ReadPositivePair427 reversedFixture.state.core reversedFixture.root :=
  (readOriginalPositivePair427 reversedFixture.state.core reversedFixture.root reversedWire).get (by decide +kernel)

theorem executable_original_where_is_stable_under_source_ordinal_permutation427 :
    rebuiltReverse.root.ordinal = 1 ∧ rebuiltReverse.child.ordinal = 0 ∧
    rebuiltReverse.frame.decl.id = 218 ∧ rebuiltReverse.childFrame.decl.id = 219 ∧
    rebuiltReverse.original.child.occurrence = [71,0] ∧
    rebuiltReverse.original.name = 4 := by decide +kernel

#print axioms read_original_structural_pair_lexical_capture_from_same_source427
#print axioms read_original_structural_pair_excludes_rivals_at_both_actual_requests427
#print axioms executable_original_where_rebuilds_exact_child_and_center427
#print axioms executable_original_where_produces_same_model_dictionary427
#print axioms executable_original_where_is_not_just_any_candidate427
#print axioms executable_original_where_is_stable_under_source_ordinal_permutation427
end Yulang.GeneralDeclarativeI65.I72.StructuralWhereReadback427
