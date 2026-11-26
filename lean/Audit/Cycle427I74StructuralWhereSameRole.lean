import Yulang.GeneralDeclarativeI65I74StructuralWherePair427

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1600
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereSameRole427
open GeneralDeclarativeI65
open StructuralWhere427
open Checker408 (Problem)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarations (Declaration Clause)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation Read)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEmissionForest322 (Placement)
open RecordK2412 (closedHead412 query412 recordInput412 recordRow412)
open CommonNominalFullCarrier (Ty record subtype_refl Equivalent)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def recursiveWhere : Clause := ⟨6,19,[writtenRecord427 30 8 9],[]⟩
def compoundParent : Declaration := ⟨218,19,[closedHead412 30 31 9 8],[recursiveWhere],[],[]⟩
def scalarPattern : GeneralDeclarationPatterns.Pattern :=
  .record 30 (.app 10 []) (.app 9 [])
def scalarBase : Declaration := ⟨219,19,[scalarPattern],[],[],[]⟩
def surface (order : List Declaration) : InputBundle :=
  let catalogue : List Row := [⟨9,some ⟨[],9⟩,.primitive .emptyRecord⟩,
    ⟨10,some ⟨[],10⟩,.primitive (.scalar .int)⟩]
  ⟨⟨.absent,catalogue⟩,⟨.absent,catalogue⟩,⟨0,[⟨19,1,[]⟩]⟩,order⟩

def deepRow : Equation := ⟨0,.record 30 (.variable 1) (.variable 2)⟩
def nestedRow : Equation := ⟨1,.record 31 (.variable 3) (.variable 2)⟩
def emptyRow : Equation := ⟨2,.primitive .emptyRecord []⟩
def integerRow : Equation := ⟨3,.primitive (.scalar .int) []⟩
def whereRow : Equation := recordRow412 4 30 3
def childDestructure : Equation := ⟨4,.record 30 (.variable 3) (.variable 2)⟩
def originalShape0 : Equation := recordRow412 0 30 1
def originalShape1 : Equation := recordRow412 1 31 3
def rows : List Equation :=
  [deepRow,nestedRow,emptyRow,integerRow,whereRow,childDestructure,originalShape0,originalShape1]
def auth : Origin := ⟨0,[32],recordInput412 30 1⟩
def build (order : List Declaration := [compoundParent,scalarBase])
    (ordinary : List Equation := rows) : Option Problem := do
  let graph ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile (surface order)
  let env : Environment := ⟨0,0,0,bodies,graph,source⟩
  let s : GeneralDeclarativeI65.State :=
    ⟨⟨env,⟨⟨[],[]⟩,ordinary⟩,[]⟩,[],[auth],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[71],⟨19,[point 0],[]⟩⟩⟩
def fixture : Problem := build.get (by decide +kernel)
def bindRoot (n : Nat) : Capture := if n = 8 then point 3 else point 0
def place : Placement := ⟨fun _ _ => point 4,fun _ _ => 0⟩
def frame : AuthoredBodyFrame393 fixture.state.core fixture.root :=
  ⟨0,compoundParent,by decide +kernel,by decide +kernel,place,bindRoot⟩
def w : RecordArgumentWire427 := ⟨0,0,4⟩
def reached : OriginalRecordArgument427 frame 0 0 :=
  (readOriginalRecordArgument427 frame w).get (by decide +kernel)

def parentEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[0,1,2,1,2]⟩
def nestedEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,0,2,1,2]⟩
def childEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,2,2,1,0]⟩
def scalarEscape : List410.ExactEscapeWire := ⟨[0,1,2,3,4],[2,2,2,0,2]⟩
def blockedBase : RivalWire427 := ⟨1,6,7,parentEscape,nestedEscape⟩
def blockedCompound : RivalWire427 := ⟨0,4,3,childEscape,scalarEscape⟩
def parentRival : ReadBoxRival427 fixture.state.core fixture.root :=
  (readBoxRival427 fixture.state.core fixture.root blockedBase).get (by decide +kernel)
def childRival : ReadBoxRival427 fixture.state.core reached.child :=
  (readBoxRival427 fixture.state.core reached.child blockedCompound).get (by decide +kernel)

def say (n : Nat) : Ty :=
  if n = 0 then record 30 (record 31 (.base .int) .emptyRecord) .emptyRecord
  else if n = 1 then record 31 (.base .int) .emptyRecord
  else if n = 2 then .emptyRecord
  else if n = 4 then record 30 (.base .int) .emptyRecord
  else .base .int
def model : I72.Model :=
  ⟨fun n => (say n,Common.rowEmpty),fun _ => none,
    fun n => if n = 0 then some (recordInput412 30 1) else none⟩
theorem same_role_original_snapshot_fits427 : I72.Fits fixture.state model := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ e; cases e
  · intro _ e; cases e
  · intro e present
    change e ∈ rows at present
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ e; cases e
  · intro _ a
    change _ ∈ [auth] at a
    cases List.mem_singleton.mp a
    rfl

private theorem emptyAt (capture : Nat → Capture) :
    Read fixture.state.core.current.ordinary capture .actual 2 (.primitive .emptyRecord []) :=
  .primitive (n:=0) (fun i => i.elim0) (fun i => i.elim0)
    (by change emptyRow ∈ rows; simp [rows]) (fun i => i.elim0)

def realParentHead427 : SourceHead fixture.state.core fixture.root compoundParent := by
  let ordinary := fixture.state.core.current.ordinary
  have named : Read ordinary bindRoot .actual 3 (.variable 8) := by
    apply Read.capture <;> (change Bound ordinary.normal 3 3; exact .refl 3)
  have inner : Read ordinary bindRoot .actual 1
      (.record 31 (.variable 8) (.primitive .emptyRecord [])) :=
    .record (by change nestedRow ∈ rows; simp [rows]) named (emptyAt _)
  have root : Read ordinary bindRoot .actual 0 (query412 30 31 8) :=
    .record (by change deepRow ∈ rows; simp [rows]) inner (emptyAt _)
  refine .ordered bindRoot (.cons (.ordinary ⟨⟨.refl _, .refl _⟩,query412 30 31 8,
    ?_,.direct (.structural root)⟩) .nil)
  rfl

def noBinding (_ : Nat) : Capture := point 0
def scalarCode : Expr := .record 30 (.primitive (.scalar .int) []) (.primitive .emptyRecord [])
def realChildHead427 : SourceHead fixture.state.core reached.child scalarBase := by
  let ordinary := fixture.state.core.current.ordinary
  have actual : reached.child.demand.arguments = [point 4] := by
    have h := structural_where_child_argument_is_placed_point427 reached
    have kind : reached.child.demand.arguments.length = 1 := by decide +kernel
    have n : reached.name = 4 := by decide +kernel
    rw [n] at h
    generalize hs : reached.child.demand.arguments = xs at h kind ⊢
    cases xs with
    | nil => simp at kind
    | cons a rest =>
      have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa using kind)
      subst rest
      exact congrArg (fun x => [x]) (Option.some.inj h)
  have integer : Read ordinary noBinding .actual 3 (.primitive (.scalar .int) []) :=
    .primitive (n:=0) (fun i => i.elim0) (fun i => i.elim0)
      (by change integerRow ∈ rows; simp [rows]) (fun i => i.elim0)
  have child : Read ordinary noBinding .actual 4 scalarCode :=
    .record (by change childDestructure ∈ rows; simp [rows]) integer (emptyAt _)
  refine .ordered noBinding ?_
  rw [actual]
  refine .cons (.ordinary ⟨⟨.refl _, .refl _⟩,scalarCode,
    ?_,.direct (.structural child)⟩) .nil
  rfl

theorem actual_same_role_complete_view_switches_real_positive_head427 :
    (∀ d ∈ visible fixture.state.core fixture.root,
      Nonempty (SourceHead fixture.state.core fixture.root d) → d = compoundParent) ∧
    (∀ d ∈ visible fixture.state.core reached.child,
      Nonempty (SourceHead fixture.state.core reached.child d) → d = scalarBase) := by
  constructor
  · exact (positive_box_cannot_be_displaced_by_its_checked_rival427 parentRival
      (.inl (by decide +kernel)) ⟨realParentHead427⟩ model same_role_original_snapshot_fits427).2
  · exact (positive_box_cannot_be_displaced_by_its_checked_rival427 childRival
      (.inr (by decide +kernel)) ⟨realChildHead427⟩ model same_role_original_snapshot_fits427).2

theorem original_same_role_where_reaches_actual_new_input427 :
    (frameWhereKids400 frame)[0]? = some reached.child ∧
      reached.child.occurrence = [71,0] ∧ reached.child.demand.role = fixture.root.demand.role ∧
      parentRival.found.field = 1 ∧ childRival.found.field = 3 ∧
      (readBoxRival427 fixture.state.core reached.child {blockedCompound with payloadRow := 7}).isNone = true := by
  refine ⟨structural_where_keeps_original_child_at_ordinal427 reached,?_⟩
  decide +kernel

def leafFrame427 : AuthoredBodyFrame393 fixture.state.core reached.child :=
  ⟨1,scalarBase,by decide +kernel,by decide +kernel,place,noBinding⟩

theorem genuine_same_role_X10_positive_pair_has_one_same_model_dictionary427 :
    I72.DictionaryEvidence fixture.state model fixture.root (.node 218 [.node 219 []]) :=
  same_state_structural_where_pair_has_fixed_dictionary427 (atlas:=fixture.state.b6)
    reached leafFrame427 realParentHead427 realChildHead427
    (by decide +kernel) (by rfl) (by decide +kernel) (by rfl) model same_role_original_snapshot_fits427

theorem actual_same_role_rivals_visit_before_mismatch427 :
    GeneralDeclarativeInspect321.Visit
      (GeneralDeclarativeGraphRows321.structural fixture.state.core.current.ordinary)
      parentRival.found.root (.record parentRival.found.box parentRival.found.want parentRival.found.tail) 1 ∧
    GeneralDeclarativeInspect321.Visit
      (GeneralDeclarativeGraphRows321.structural fixture.state.core.current.ordinary)
      childRival.found.root (.record childRival.found.box childRival.found.want childRival.found.tail) 3 := by
  have p1 : parentRival.found.field = 1 := by decide +kernel
  have p2 : childRival.found.field = 3 := by decide +kernel
  exact ⟨p1 ▸ real_rival_visits_original_mismatched_field427 parentRival.found,
    p2 ▸ real_rival_visits_original_mismatched_field427 childRival.found⟩

def reversedFixture : Problem := (build [scalarBase,compoundParent]).get (by decide +kernel)
def reversedFrame : AuthoredBodyFrame393 reversedFixture.state.core reversedFixture.root :=
  ⟨1,compoundParent,by decide +kernel,by decide +kernel,place,bindRoot⟩
def reversedChild : OriginalRecordArgument427 reversedFrame 0 0 :=
  (readOriginalRecordArgument427 reversedFrame w).get (by decide +kernel)
theorem swapping_visible_declaration_order_does_not_swap_source_where_identity427 :
    (readBoxRival427 reversedFixture.state.core reversedFixture.root
      {blockedBase with declarationOrdinal := 0}).isSome = true ∧
    (readBoxRival427 reversedFixture.state.core reversedChild.child
      {blockedCompound with declarationOrdinal := 1}).isSome = true ∧
    reversedChild.child.occurrence = reached.child.occurrence ∧
    reversedChild.name = reached.name := by decide +kernel

def cyclic : Problem := (build (ordinary := rows ++ [⟨3,.variable 1⟩])).get (by decide +kernel)
def siteCycle : RecordK2412.FieldCycleWire := ⟨⟨7,.same,3⟩,[],.forward 8⟩
theorem a_true_cycle_on_the_actual_inspected_site_prevents_rival_read427 :
    GeneralDeclarativeK2Alias321.AliasCycle cyclic.state.core.current.ordinary
      (GeneralDeclarativeGraphRows321.observed cyclic.state.core.current.ordinary) 1 ∧
    (readBoxRival427 cyclic.state.core cyclic.root blockedBase).isNone = true :=
  ⟨RecordK2412.cycle_at_sound412 (w:=siteCycle) (by decide +kernel),by decide +kernel⟩

#print axioms genuine_same_role_X10_positive_pair_has_one_same_model_dictionary427
#print axioms actual_same_role_rivals_visit_before_mismatch427
#print axioms swapping_visible_declaration_order_does_not_swap_source_where_identity427
#print axioms a_true_cycle_on_the_actual_inspected_site_prevents_rival_read427
#print axioms same_role_original_snapshot_fits427
#print axioms actual_same_role_complete_view_switches_real_positive_head427
#print axioms original_same_role_where_reaches_actual_new_input427
end Yulang.GeneralDeclarativeI65.I72.StructuralWhereSameRole427
