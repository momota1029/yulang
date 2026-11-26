import Yulang.GeneralDeclarativeI65I74StructuralWherePairRead433
import Yulang.GeneralDeclarativeI65I74StructuralWhereAssociatedEntry432

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65 StructuralWhere428
open Checker408 (Problem Result)
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)

def ReadTwoNamedWrap433.secondRequest {p : Problem} (o : ReadTwoNamedWrap433 p) : Request :=
  ⟨p.root.occurrence ++ [1],(o.event.frame.whereFor o.original.sibling).demand⟩

theorem read_pair_exact_original_kids433 {p : Problem} (o : ReadTwoNamedWrap433 p) :
    o.event.kids = [o.original.origin.child,o.secondRequest] := by
  have first := o.original.origin.child_position
  rw [o.original.inOrder] at first
  change o.event.kids[0]? = some o.original.origin.child at first
  have second : o.event.kids[1]? = some o.secondRequest := by
    simp [Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses, children,
      o.original.exactlyTwo,ReadTwoNamedWrap433.secondRequest]
  have count : o.event.kids.length = 2 := by
    simp [Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses,children,o.original.exactlyTwo]
  generalize eq : o.event.kids = actual at first second count ⊢
  cases actual with
  | nil => simp at count
  | cons a rest =>
    cases rest with
    | nil => simp at count
    | cons b tail =>
      have empty : tail = [] := List.length_eq_zero_iff.mp (by simpa using count)
      subst tail
      have aEq : a = o.original.origin.child := by simpa using first
      have bEq : b = o.secondRequest := by simpa using second
      simp [aEq,bEq]

abbrev TwoNamedWhereRules433 : SourcePrimitives :=
  ruleUnion428 R16.named426 twoNamedWhereParentRule433

theorem two_named_where_existing_and_new_law433 : SelectedLaw428 TwoNamedWhereRules433 :=
  union_local_law428 associated_named_law432 original_two_named_where_parent_local_law433

private def pickSource433 {p : Problem} (a : ExplicitPick419.PickPacket p) :
    SourceTrace ExplicitPick419.R11 p.state p.root
      (.selected a.declaration.decl.id []) (some a.event) :=
  .selected a.event a.rawSafe (.inr ⟨rfl,⟨.actual a⟩⟩) .nil
    ((ExplicitPick419.actual_pick_never_switches_to_a_where_child419 a).symm ▸
      (.nil : WhereForest ExplicitPick419.R11 p.state [] []))

private theorem pick_source_has_exact_write433 {p : Problem} (a : ExplicitPick419.PickPacket p) :
    namedTraceWrites428 (pickSource433 a) = [a.retained.write] := by
  have erase : ∀ qs (eq : qs = []),
      namedForestWrites428 (eq.symm ▸ (.nil : WhereForest ExplicitPick419.R11 p.state [] [])) = [] := by
    intro qs eq
    cases eq
    rfl
  change Check408.encodedEventWrites a.event ++
    namedForestWrites428 ((ExplicitPick419.actual_pick_never_switches_to_a_where_child419 a).symm ▸
      (.nil : WhereForest ExplicitPick419.R11 p.state [] [])) = _
  rw [ExplicitPick419.actual_event_has_only_its_original_output419,
    erase _ (ExplicitPick419.actual_pick_never_switches_to_a_where_child419 a)]
  rfl

private theorem embedPick433 : NamedRuleMap428 ExplicitPick419.R11 TwoNamedWhereRules433 :=
  ⟨fun h => .inl (.inl (.inl (.inl (.inl h)))),fun h => .inl (.inl (.inl (.inl h)))⟩

def ReadTwoNamedWrap433.tree {p : Problem} (o : ReadTwoNamedWrap433 p) : Tree :=
  .selected o.event.frame.decl.id
    [.selected o.first.declaration.decl.id [],.selected o.second.declaration.decl.id []]

def ReadTwoNamedWrap433.dictionary {p : Problem} (o : ReadTwoNamedWrap433 p) : Dictionary :=
  .node o.event.frame.decl.id [.node o.first.declaration.decl.id [],.node o.second.declaration.decl.id []]

def ReadTwoNamedWrap433.report {p : Problem} (o : ReadTwoNamedWrap433 p) : Result :=
  ⟨o.tree,.selected o.dictionary,
    Check408.encodedEventWrites o.event ++ [o.first.retained.write,o.second.retained.write]⟩

theorem read_pair_has_exact_source_trace_and_order433 {p : Problem} (o : ReadTwoNamedWrap433 p) :
    ∃ (trace : SourceTrace TwoNamedWhereRules433 p.state p.root o.tree (some o.event))
      (first : SourceTrace TwoNamedWhereRules433 p.state o.original.origin.child
        (.selected o.first.declaration.decl.id []) (some o.first.event))
      (second : SourceTrace TwoNamedWhereRules433 p.state o.secondRequest
        (.selected o.second.declaration.decl.id []) (some o.second.event)),
      ActualWhereTraceAt432 trace 0 first ∧ ActualWhereTraceAt432 trace 1 second ∧
      namedTraceWrites428 trace = o.report.writes ∧ Summarizes o.tree (.selected o.dictionary) := by
  let f := mapNamedTrace428 embedPick433 (pickSource433 o.first)
  let s := mapNamedTrace428 embedPick433 (pickSource433 o.second)
  let forest : WhereForest TwoNamedWhereRules433 p.state [o.original.origin.child,o.secondRequest]
      [.selected o.first.declaration.decl.id [],.selected o.second.declaration.decl.id []] :=
    .cons f.val (.cons s.val .nil)
  let trace : SourceTrace TwoNamedWhereRules433 p.state p.root o.tree (some o.event) :=
    .selected o.event o.original.rootSafe (.inr ⟨rfl,⟨o.original⟩⟩) .nil
      ((read_pair_exact_original_kids433 o).symm ▸ forest)
  have both : ∀ qs (eq : [o.original.origin.child,o.secondRequest] = qs),
      ActualForestTraceAt432 TwoNamedWhereRules433 p.state (eq ▸ forest) 0 f.val ∧
      ActualForestTraceAt432 TwoNamedWhereRules433 p.state (eq ▸ forest) 1 s.val ∧
      namedForestWrites428 (eq ▸ forest) = [o.first.retained.write,o.second.retained.write] := by
    intro qs eq
    cases eq
    refine ⟨.here f.val _,.there f.val (.here s.val .nil),?_⟩
    change namedTraceWrites428 f.val ++ (namedTraceWrites428 s.val ++ []) = _
    rw [f.property.1.trans (pick_source_has_exact_write433 o.first),
      s.property.1.trans (pick_source_has_exact_write433 o.second)]
    rfl
  obtain ⟨zero,one,ledger⟩ := both _ (read_pair_exact_original_kids433 o).symm
  refine ⟨trace,f.val,s.val,zero,one,?_,
    .selected (.cons (.selected .nil (.selected rfl)) (.cons (.selected .nil (.selected rfl)) .nil)) (.selected rfl)⟩
  change Check408.encodedEventWrites o.event ++
    namedForestWrites428 ((read_pair_exact_original_kids433 o).symm ▸ forest) = _
  rw [ledger]
  rfl

theorem read_pair_same_model_dictionary433 {p : Problem} (o : ReadTwoNamedWrap433 p) :
    ∀ m : I72.Model, Fits p.state m → DictionaryEvidence p.state m p.root o.dictionary := by
  obtain ⟨trace,_,_,_,_,_,summary⟩ := read_pair_has_exact_source_trace_and_order433 o
  intro m fit
  exact actual_named_trace_same_model_dictionary428 two_named_where_existing_and_new_law433
    trace m fit o.dictionary summary

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
