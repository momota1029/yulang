import Yulang.GeneralDeclarativeI65I74StructuralWhereForest427
import Yulang.GeneralDeclarativeI65I74StructuralWhereAuditSupport429

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereForest427
open GeneralDeclarativeI65
open StructuralWhere427 StructuralWhereAuditFixture429 StructuralWhereReadback427
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarations (Clause Declaration)
open GeneralDeclarativeEmissionForest322 (Placement)
open CommonNominalFullCarrier (Ty record subtype_refl)
open GeneralDeclarativeHead320 (Equation Read)

def firstClause : Clause := {recursiveWhere with id := 50}
def secondClause : Clause := {recursiveWhere with id := 6}
def parentTwo : Declaration := {compoundParent with requirements := [firstClause,secondClause]}
def secondWhere : Equation := RecordK2412.recordRow412 5 30 3
def secondDestructure : Equation := ⟨5,.record 30 (.variable 3) (.variable 2)⟩
def twoRows : List Equation := rows ++ [secondWhere,secondDestructure]
def p : Checker408.Problem := (build [parentTwo,scalarBase] twoRows).get (by decide +kernel)
def actualPlacement : Placement :=
  ⟨fun c _ => if c.id = firstClause.id then point 4 else point 5,fun _ _ => 0⟩
def twoFrame : AuthoredBodyFrame393 p.state.core p.root :=
  ⟨0,parentTwo,by decide +kernel,by decide +kernel,actualPlacement,bindRoot⟩

def sameModel (n : Nat) : Ty := if n = 5 then record 30 (.base .int) .emptyRecord else say n
def fitModel : I72.Model :=
  ⟨fun n => (sameModel n,Common.rowEmpty),fun _ => none,
    fun n => if n = 0 then some (RecordK2412.recordInput412 30 1) else none⟩
theorem two_source_model_fits427 : I72.Fits p.state fitModel := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ e; cases e
  · intro _ e; cases e
  · intro e present
    change e ∈ twoRows at present
    simp only [twoRows,rows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ e; cases e
  · intro _ a
    change _ ∈ [auth] at a
    cases List.mem_singleton.mp a
    rfl

def secondEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4,5],[2,2,2,1,2,0]⟩
def secondEscAsOther : List410.ExactEscapeWire := ⟨[0,1,2,3,4,5],[2,2,2,0,2,2]⟩
def secondHead : PositiveHeadWire427 :=
  ⟨1,9,2,secondEscape,secondEscAsOther,emptyEscape,.scalar 3⟩
def secondRival : RivalWire427 :=
  ⟨0,8,3,secondEscape,secondEscAsOther⟩
def firstWire : ReviewedWhereWire427 :=
  ⟨4,⟨leafHeadWire,blockedCompound,⟨childEscape,scalarEscape⟩⟩⟩
def secondWire : ReviewedWhereWire427 :=
  ⟨8,⟨secondHead,secondRival,⟨secondEscape,secondEscAsOther⟩⟩⟩
def keepSecondOffRoot (w : List410.ExactEscapeWire) : List410.ExactEscapeWire :=
  ⟨w.ranks ++ [5],w.palette ++ [2]⟩
def rootWire : VisiblePointWire427 :=
  let root := keepSecondOffRoot parentEscape
  let inner := keepSecondOffRoot nestedEscape
  let tail := keepSecondOffRoot emptyEscape
  let hd : PositiveHeadWire427 := ⟨0,0,2,root,inner,tail,
    .nested 1 2 (keepSecondOffRoot scalarEscape) tail⟩
  let rv : RivalWire427 := ⟨1,6,7,root,inner⟩
  ⟨hd,rv,⟨root,inner⟩⟩
theorem prepared_root_reads_same_original_event427 :
    (readOriginalPreparedRoot427 twoFrame rootWire).isSome = true ∧
    (readOriginalPreparedRoot427 {twoFrame with input := fun _ => point 4} rootWire).isNone = true := by
  decide +kernel
def prepared : OriginalPreparedRoot427 twoFrame :=
  (readOriginalPreparedRoot427 twoFrame rootWire).get prepared_root_reads_same_original_event427.1

def wire : List ReviewedWhereWire427 := [firstWire,secondWire]
theorem read_ordered_source_forests427 :
    (readReviewedWhere427 twoFrame wire).isSome = true := by decide +kernel
def recovered : ReviewedForest427 twoFrame (List.range twoFrame.decl.requirements.length) :=
  (readReviewedWhere427 twoFrame wire).get read_ordered_source_forests427

theorem actual_authored_order_keeps_two_equal_denoting_where_arguments_distinct427 :
    recovered.originalNames = [4,5] ∧ recovered.requests.map Request.occurrence = [[71,0],[71,1]] ∧
    recovered.dictionaries = [.node 219 [],.node 219 []] ∧
    (fitModel.assignment 4).1 = (fitModel.assignment 5).1 ∧
    (readReviewedWhere427 twoFrame wire.reverse).isNone = true ∧
    (readReviewedWhere427 twoFrame [firstWire,firstWire]).isNone = true ∧
    (readReviewedWhere427 twoFrame (wire.take 1)).isNone = true := by
  have compare : GeneralDeclarativeWitnessTree349.eqResult
      (.selected (.node 218 recovered.dictionaries))
      (.selected (.node 218 [.node 219 [],.node 219 []])) = true := by decide +kernel
  have d := CommonRoleOutermostResolver.Result.selected.inj
    ((GeneralDeclarativeWitnessTree349.eq_result _ _).mp compare)
  refine ⟨?_,?_,(CommonRoleOutermostResolver.Dictionary.node.inj d).2,rfl,?_,?_,?_⟩ <;>
    decide +kernel

theorem exact_original_two_where_same_model_dictionary427 :
    I72.DictionaryEvidence p.state fitModel p.root (.node 218 [.node 219 [],.node 219 []]) := by
  have result := reviewed_original_where_forest_has_same_model_parent427
    (atlas:=p.state.b6) (v:=recovered)
    (prepared.declaration ▸ prepared.visiblePoint.positive.head) rfl
    (Option.eq_some_of_isSome read_ordered_source_forests427) fitModel two_source_model_fits427
  rw [actual_authored_order_keeps_two_equal_denoting_where_arguments_distinct427.2.2.1] at result
  exact result

#print axioms complete_visible_point_has_no_filtered_K2_assumption427
#print axioms reviewed_source_order_is_entire_original_where427
#print axioms reviewed_source_order_and_same_model_forest427
#print axioms reviewed_original_where_forest_has_same_model_parent427
#print axioms actual_prepared_root_keeps_original_input_capture427
#print axioms prepared_root_reads_same_original_event427
#print axioms actual_authored_order_keeps_two_equal_denoting_where_arguments_distinct427
#print axioms exact_original_two_where_same_model_dictionary427
end Yulang.GeneralDeclarativeI65.I72.StructuralWhereForest427
