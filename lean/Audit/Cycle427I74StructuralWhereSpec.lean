import Yulang.GeneralDeclarativeI65I74StructuralWhereParent427
import Yulang.GeneralDeclarativeI65I74StructuralWhereChildRead427
import Yulang.GeneralDeclarativeI65I74RecordDeclaration412

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1600
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereSpec427
open GeneralDeclarativeI65
open StructuralWhere427
open Checker408 (Problem)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarations (Declaration Clause)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation byMode)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEmissionForest322 (Placement)
open RecordK2412 (closedHead412 query412 recordInput412 recordRow412)
open CommonNominalFullCarrier (Ty record subtype_refl Equivalent)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def clFirst : Clause := ⟨6,20,[writtenRecord427 30 8 9],[]⟩
def clSecond : Clause := ⟨12,21,[writtenRecord427 30 8 9],[]⟩
def rootDecl : Declaration := ⟨218,19,[closedHead412 30 31 9 8],[clFirst,clSecond],[],[]⟩
def leafFirst : Declaration := ⟨219,20,[writtenRecord427 30 13 9],[],[],[]⟩
def leafSecond : Declaration := ⟨220,21,[writtenRecord427 30 15 9],[],[],[]⟩
def surface : InputBundle :=
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩,⟨20,1,[]⟩,⟨21,1,[]⟩]⟩,
    [rootDecl,leafFirst,leafSecond]⟩

def outerRow : Equation := ⟨0,.record 30 (.variable 1) (.variable 2)⟩
def middleRow : Equation := ⟨1,.record 31 (.variable 3) (.variable 2)⟩
def nilRow : Equation := ⟨2,.primitive .emptyRecord []⟩
def scalarRow : Equation := ⟨3,.primitive (.scalar .int) []⟩
def emittedFirst : Equation := recordRow412 4 30 3
def emittedSecond : Equation := recordRow412 5 30 3
def normalizedOuter : Equation := recordRow412 0 30 1
def normalizedMiddle : Equation := recordRow412 1 31 3
def rawRows : List Equation :=
  [outerRow,middleRow,nilRow,scalarRow,emittedFirst,emittedSecond,normalizedOuter,normalizedMiddle]
def outerAuthored : Origin := ⟨0,[32],recordInput412 30 1⟩

def build : Option Problem := do
  let graph ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile surface
  let env : Environment := ⟨0,0,0,bodies,graph,source⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨env,⟨⟨[],[]⟩,rawRows⟩,[]⟩,[],[outerAuthored],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[71],⟨19,[point 0],[]⟩⟩⟩

def fixture : Problem := build.get (by decide +kernel)

def bindRoot (n : Nat) : Capture := if n = 8 then point 3 else point 0

def actualPlacement : Placement :=
  ⟨fun cl _ => if cl.id = 6 then point 4 else point 5,fun _ _ => 0⟩

def actualFrame : AuthoredBodyFrame393 fixture.state.core fixture.root :=
  ⟨0,rootDecl,by decide +kernel,by decide +kernel,actualPlacement,bindRoot⟩

def wFirst : RecordArgumentWire427 := ⟨0,0,4⟩
def wSecond : RecordArgumentWire427 := ⟨1,0,5⟩

def firstRead : OriginalRecordArgument427 actualFrame 0 0 :=
  (readOriginalRecordArgument427 actualFrame wFirst).get (by decide +kernel)
def secondRead : OriginalRecordArgument427 actualFrame 1 0 :=
  (readOriginalRecordArgument427 actualFrame wSecond).get (by decide +kernel)

def firstLeaf : LeafWire427 := ⟨1,⟨[0,1,2,3,4,5],[2,2,2,1,0,2]⟩⟩
def secondLeaf : LeafWire427 := ⟨2,⟨[0,1,2,3,4,5],[2,2,2,1,2,0]⟩⟩
def positiveFirst : ReadClosedChild427 firstRead fixture.state.b6 :=
  (readClosedChild427 firstRead fixture.state.b6 firstLeaf).get (by decide +kernel)
def positiveSecond : ReadClosedChild427 secondRead fixture.state.b6 :=
  (readClosedChild427 secondRead fixture.state.b6 secondLeaf).get (by decide +kernel)

theorem real_two_compound_children_keep_both_source_ordinals427 :
    (frameWhereKids400 actualFrame)[0]? = some firstRead.child ∧
    (frameWhereKids400 actualFrame)[1]? = some secondRead.child ∧
    firstRead.child.occurrence = [71,0] ∧ secondRead.child.occurrence = [71,1] ∧
    firstRead.child.demand.role = 20 ∧ secondRead.child.demand.role = 21 :=
  ⟨structural_where_keeps_original_child_at_ordinal427 firstRead,
    structural_where_keeps_original_child_at_ordinal427 secondRead,
    by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem equal_rhs_at_distinct_placements_cannot_swap_where_ordinals427 :
    (readOriginalRecordArgument427 actualFrame {wFirst with rowOrdinal := 5}).isNone = true ∧
    (readOriginalRecordArgument427 actualFrame {wSecond with rowOrdinal := 4}).isNone = true ∧
    (readClosedChild427 firstRead fixture.state.b6 secondLeaf).isNone = true ∧
    (readClosedChild427 secondRead fixture.state.b6 firstLeaf).isNone = true := by
  decide +kernel

def say (n : Nat) : Ty :=
  if n = 0 then record 30 (record 31 (.base .int) .emptyRecord) .emptyRecord
  else if n = 1 then record 31 (.base .int) .emptyRecord
  else if n = 2 then .emptyRecord
  else if n = 4 ∨ n = 5 then record 30 (.base .int) .emptyRecord
  else .base .int

def model : I72.Model :=
  ⟨fun n => (say n,Common.rowEmpty),fun _ => none,
    fun n => if n = 0 then some (recordInput412 30 1) else none⟩

theorem genuine_X10_shaped_acyclic_snapshot_fits427 : I72.Fits fixture.state model := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ absent; cases absent
  · intro _ absent; cases absent
  · intro eq found
    change eq ∈ rawRows at found
    simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ absent; cases absent
  · intro src entry
    change src ∈ [outerAuthored] at entry
    cases List.mem_singleton.mp entry
    rfl

theorem genuine_compound_children_both_have_dictionary_evidence427 :
    I72.DictionaryEvidence fixture.state model firstRead.child (.node 219 []) ∧
    I72.DictionaryEvidence fixture.state model secondRead.child (.node 220 []) := by
  have id1 : positiveFirst.source.decl.id = 219 := by decide +kernel
  have id2 : positiveSecond.source.decl.id = 220 := by decide +kernel
  constructor
  · simpa only [id1] using original_compound_child_has_positive_same_model_dictionary427
      (atlas:=fixture.state.b6) positiveFirst.source model genuine_X10_shaped_acyclic_snapshot_fits427
  · simpa only [id2] using original_compound_child_has_positive_same_model_dictionary427
      (atlas:=fixture.state.b6) positiveSecond.source model genuine_X10_shaped_acyclic_snapshot_fits427


open GeneralDeclarativeHead320 (Read)
open GeneralDeclarativeBounds319 (Bound)

theorem actual_nested_parent_has_source_head427 :
    Nonempty (SourceHead fixture.state.core fixture.root actualFrame.decl) := by
  let base := fixture.state.core.current.ordinary
  have empty : Read base bindRoot .actual 2 (.primitive .emptyRecord []) :=
    .primitive (n:=0) (fun t => t.elim0) (fun t => t.elim0)
      (by change nilRow ∈ rawRows; simp [rawRows]) (fun t => t.elim0)
  have getScalar : Read base bindRoot .actual 3 (.variable 8) := by
    apply Read.capture <;>
      (change Bound base.normal 3 3; exact .refl 3)
  have inside : Read base bindRoot .actual 1
      (.record 31 (.variable 8) (.primitive .emptyRecord [])) :=
    .record (by change middleRow ∈ rawRows; simp [rawRows]) getScalar empty
  have entire : Read base bindRoot .actual 0 (query412 30 31 8) :=
    .record (by change outerRow ∈ rawRows; simp [rawRows]) inside empty
  refine ⟨.ordered bindRoot (.cons (.ordinary ⟨⟨.refl 0,.refl 0⟩,
    query412 30 31 8,?_, .direct (.structural entire)⟩) .nil)⟩
  rfl

theorem actual_parent_original_structural_clauses_pass_header427 :
    GeneralDeclarations.DeclarationChecked (authoredRegistry fixture.state.core.current).constructors
      (authoredRegistry fixture.state.core.current).roles rootDecl := by
  let e := fixture.state.core.current.environment
  have roles : GeneralSourceMetadataRoles291.Valid e.source.roles :=
    (GeneralSourceMetadataRoles291.check_exact _).mp (by decide +kernel)
  have cov := (GeneralDeclarativeWitnessModeCoverage357.check_exact roles).mp (by decide +kernel)
  have uses : rootDecl ∈ e.source.declarations := by decide +kernel
  apply every_original_closed_where_clause_passes_parent_header427 (cov.1 _ uses)
    (by decide +kernel) rfl
  intro c rec
  change c ∈ [clFirst,clSecond] at rec
  simp only [List.mem_cons,List.not_mem_nil,or_false] at rec
  rcases rec with rfl|rfl <;> exact ⟨rfl,by decide +kernel⟩

def orderedWires : List OrderedWhereWire427 :=
  [⟨4,firstLeaf⟩,⟨5,secondLeaf⟩]

theorem actual_whole_structural_where_batch_runs_in_original_order427 :
    (readAllOriginalWhere427 actualFrame fixture.state.b6 orderedWires).isSome = true ∧
    (readAllOriginalWhere427 actualFrame fixture.state.b6 orderedWires.reverse).isNone = true ∧
    (readAllOriginalWhere427 actualFrame fixture.state.b6 (orderedWires.take 1)).isNone = true := by
  decide +kernel

theorem actual_X10_shaped_parent_has_ordered_positive_dictionary427 :
    ∃ xs, readAllOriginalWhere427 actualFrame fixture.state.b6 orderedWires = some xs ∧
      xs.dictionaries = [.node 219 [],.node 220 []] ∧
      I72.DictionaryEvidence fixture.state model fixture.root (.node 218 xs.dictionaries) := by
  have accepted := actual_whole_structural_where_batch_runs_in_original_order427.1
  cases all : readAllOriginalWhere427 actualFrame fixture.state.b6 orderedWires with
  | none => simp [all] at accepted
  | some xs =>
    obtain ⟨head⟩ := actual_nested_parent_has_source_head427
    refine ⟨xs,rfl,?_,original_structural_parent_and_all_children_share_given_model427 head
      (by rfl) all model genuine_X10_shaped_acyclic_snapshot_fits427⟩
    -- Simple equality of the exact decoded dictionaries, not model equivalence.
    have orig := Option.some.inj (all.symm.trans
      ((Option.some_get (x:=readAllOriginalWhere427 actualFrame fixture.state.b6 orderedWires)
        (by decide +kernel)).symm))
    rw [orig]
    let fromWire := (readAllOriginalWhere427 actualFrame fixture.state.b6 orderedWires).get
      (by decide +kernel)
    have compared : GeneralDeclarativeWitnessTree349.eqResult
        (.selected (.node 218 fromWire.dictionaries))
        (.selected (.node 218 [.node 219 [],.node 220 []])) = true := by
      decide +kernel
    exact (CommonRoleOutermostResolver.Dictionary.node.inj
      (CommonRoleOutermostResolver.Result.selected.inj
        ((GeneralDeclarativeWitnessTree349.eq_result _ _).mp compared))).2

theorem actual_parent_entered_nested_record_is_raw_safe427 :
    GeneralDeclarativeInspect321.Visit
      (GeneralDeclarativeGraphRows321.structural fixture.state.core.current.ordinary)
        0 (query412 30 31 8) 1 ∧
    ¬ GeneralDeclarativeK2Alias321.AliasCycle fixture.state.core.current.ordinary
      (GeneralDeclarativeGraphRows321.observed fixture.state.core.current.ordinary) 1 := by
  have present : (⟨0,.record 30 (.variable 1) (.primitive .emptyRecord [])⟩ : Equation) ∈
      fixture.state.core.current.ordinary.equations := by
    change normalizedOuter ∈ rawRows
    simp [rawRows]
  have exactShape := GeneralDeclarativeGraphRows321.literal_head present
    (show GeneralDeclarativeGraphRows321.shapeOf normalizedOuter.right = some (.record [(30,1)]) from rfl)
  refine ⟨.field exactShape List.mem_cons_self List.mem_cons_self (.here .record),?_⟩
  let w : List410.ExactEscapeWire := ⟨[0,1,2,3,4,5],[2,0,2,1,2,2]⟩
  exact List410.exact_escape_refutes_raw_root_K2410 (w:=w) (by decide +kernel)

#print axioms actual_parent_entered_nested_record_is_raw_safe427
#print axioms actual_nested_parent_has_source_head427
#print axioms actual_parent_original_structural_clauses_pass_header427
#print axioms actual_whole_structural_where_batch_runs_in_original_order427
#print axioms actual_X10_shaped_parent_has_ordered_positive_dictionary427

#print axioms real_two_compound_children_keep_both_source_ordinals427
#print axioms equal_rhs_at_distinct_placements_cannot_swap_where_ordinals427
#print axioms genuine_X10_shaped_acyclic_snapshot_fits427
#print axioms genuine_compound_children_both_have_dictionary_evidence427

end Yulang.GeneralDeclarativeI65.I72.StructuralWhereSpec427
