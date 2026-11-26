import Yulang.GeneralDeclarativeI65I74StructuralWhereAssociatedRead432

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65 StructuralWhere428
open Checker408 (Problem Result)
open Check408 (Write)
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)
open GeneralDeclarativeWitnessTree349 (eqTree eq_tree eqResult eq_result)
open ExplicitPick419 (eqWrite eq_write419)

def R16 : SourcePrimitives .withEndpoint := associatedWhereKernel432

def ReadAssociatedWrap432.tree {p} (o : ReadAssociatedWrap432 p) : Tree :=
  .selected o.event.frame.decl.id [(.selected o.child.declaration.decl.id [])]

def ReadAssociatedWrap432.dictionary {p} (o : ReadAssociatedWrap432 p) : Dictionary :=
  .node o.event.frame.decl.id [.node o.child.declaration.decl.id []]

def ReadAssociatedWrap432.report {p} (o : ReadAssociatedWrap432 p) : Result :=
  ⟨o.tree,.selected o.dictionary,Check408.encodedEventWrites o.event ++ [o.child.retained.write]⟩

theorem exact_children432 {p} (o : ReadAssociatedWrap432 p) :
    o.event.kids = [o.original.origin.child] := by
  have got := o.original.origin.child_position
  have atClause := original_where_clause_position399 o.original.origin
  rw [o.original.originalWhere] at atClause
  have atZero : o.original.origin.clauseOrdinal = 0 := by
    cases h : o.original.origin.clauseOrdinal with
    | zero => rfl
    | succ i => simp [h] at atClause
  change o.event.kids[o.original.origin.clauseOrdinal]? = _ at got
  rw [atZero] at got
  have count : o.event.kids.length = 1 := by
    simp [Event.kids,frameWhereKids400,children,AuthoredBodyFrame393.clauses,o.original.originalWhere]
  generalize z : o.event.kids = all at got count ⊢
  cases all with
  | nil => simp at count
  | cons head rest =>
    have leaf : rest = [] := List.length_eq_zero_iff.mp (by simpa using count)
    subst rest
    exact congrArg (fun x => [x]) (Option.some.inj got)

private theorem prior_R11_to_R16 : NamedRuleMap428 ExplicitPick419.R11 R16.named426 :=
  ⟨fun picked => .inl (.inl (.inl (.inl picked))),fun accounted => .inl (.inl (.inl accounted))⟩

private def originalChildTrace432 {p} (o : ReadAssociatedWrap432 p) :
    SourceTrace ExplicitPick419.R11 p.state o.original.origin.child
      (.selected o.child.declaration.decl.id []) (some o.child.event) :=
  .selected o.child.event o.child.rawSafe (.inr ⟨rfl,⟨.actual o.child⟩⟩) .nil
    ((ExplicitPick419.actual_pick_never_switches_to_a_where_child419 o.child).symm ▸
      (.nil : WhereForest ExplicitPick419.R11 p.state [] []))

private theorem empty_cast_writes432 {R : SourcePrimitives} {s : I72.State} :
    ∀ qs (h : qs = []), namedForestWrites428 (h.symm ▸ (.nil : WhereForest R s [] [])) = [] := by
  intro qs h
  cases h
  rfl

theorem read_wrap_preserves_exact_selected_source_and_writes432 {p : Problem}
    (o : ReadAssociatedWrap432 p) :
    ∃ (trace : SourceTrace R16.named426 p.state p.root o.tree (some o.event))
      (child : SourceTrace R16.named426 p.state o.original.origin.child
        (.selected o.child.declaration.decl.id []) (some o.child.event)),
      ActualWhereTraceAt432 trace 0 child ∧
      Summarizes o.report.tree o.report.verdict ∧ o.report.writes = namedTraceWrites428 trace := by
  let old := originalChildTrace432 o
  let lift := mapNamedTrace428 prior_R11_to_R16 old
  have priorWrites : namedTraceWrites428 old = [o.child.retained.write] := by
    change Check408.encodedEventWrites o.child.event ++
      namedForestWrites428 ((ExplicitPick419.actual_pick_never_switches_to_a_where_child419 o.child).symm ▸
        (.nil : WhereForest ExplicitPick419.R11 p.state [] [])) = _
    rw [ExplicitPick419.actual_event_has_only_its_original_output419,
      empty_cast_writes432 _ (ExplicitPick419.actual_pick_never_switches_to_a_where_child419 o.child)]
    rfl
  let record : WhereForest R16.named426 p.state [o.original.origin.child] [(.selected o.child.declaration.decl.id [])] :=
    .cons lift.val .nil
  let original : SourceTrace R16.named426 p.state p.root o.tree (some o.event) :=
    .selected o.event o.original.rawRoot (.inr ⟨rfl,⟨o.original⟩⟩) .nil ((exact_children432 o).symm ▸ record)
  have read : ∀ qs (h : [o.original.origin.child] = qs),
      ActualForestTraceAt432 R16.named426 p.state (h ▸ record) 0 lift.val := by
    intro qs h
    cases h
    exact .here lift.val .nil
  have ledger : ∀ qs (h : [o.original.origin.child] = qs),
      namedForestWrites428 (h ▸ record) = [o.child.retained.write] := by
    intro qs h
    cases h
    change namedTraceWrites428 lift.val ++ [] = _
    rw [lift.property.1,priorWrites]
    rfl
  refine ⟨original,lift.val,read _ (exact_children432 o).symm,
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl),?_⟩
  change _ = Check408.encodedEventWrites o.event ++ namedForestWrites428 ((exact_children432 o).symm ▸ record)
  rw [ledger _ (exact_children432 o).symm]
  rfl

def compareWrites432 : List Write → List Write → Bool
  | [],[] => true
  | a::as,b::bs => eqWrite a b && compareWrites432 as bs
  | _,_ => false

theorem compare_writes_exact432 (a b : List Write) : compareWrites432 a b = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [compareWrites432]
  | cons head rest ih =>
    cases b <;> simp [compareWrites432, Bool.and_eq_true, eq_write419,ih]

def matchesAssociatedReport432 (r expected : Result) : Bool :=
  (eqTree r.tree expected.tree && eqResult r.verdict expected.verdict) &&
    compareWrites432 r.writes expected.writes

theorem matches_associated_report_exact432 (r expected : Result) :
    matchesAssociatedReport432 r expected = true ↔ r = expected := by
  cases r
  cases expected
  simp [matchesAssociatedReport432, Bool.and_eq_true, eq_tree, eq_result,compare_writes_exact432,and_assoc]

def ClassifiedAs (s : I72.State) (q : Request) (r : Result) : Prop :=
  StructuralWhere431.ClassifiedAs s q r ∨
    ∃ o : ReadAssociatedWrap432 ⟨s,q⟩, r = o.report

def ReportEvidence (s : I72.State) (m : I72.Model) (q : Request) (r : Result) : Prop :=
  StructuralWhere431.ReportEvidence s m q r ∨
    ∃ o : ReadAssociatedWrap432 ⟨s,q⟩, r = o.report ∧ DictionaryEvidence s m q o.dictionary

inductive Witness where
  | previous (old : StructuralWhere431.Witness)
  | associatedWrap (data : AssociatedWire432)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous old => StructuralWhere431.check p r old
  | .associatedWrap data => ((readAssociatedWrap432 p data).map fun o => matchesAssociatedReport432 r o.report).getD false
  | .unsupported => false

theorem previous_R15_entry_is_identical432 (p : Problem) (r : Result) (old : StructuralWhere431.Witness) :
    check p r (.previous old) = StructuralWhere431.check p r old := rfl

theorem exact_associated_report_classifies_R16_432 {p} (o : ReadAssociatedWrap432 p) :
    Classifies R16 p.state p.root o.report.verdict := by
  obtain ⟨t,_,_,summary,_⟩ := read_wrap_preserves_exact_selected_source_and_writes432 o
  exact legacy_classification_included426 ⟨o.tree,some o.event,⟨t⟩,summary⟩

theorem dictionary_sound_R16 : DictionarySound R16 :=
  dictionary_sound_for_associated_where_kernel432

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧
    ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  cases w with
  | previous old =>
    obtain ⟨prior,meaning⟩ := StructuralWhere431.check_sound p r old yes
    exact ⟨.inl prior,fun m fit => .inl (meaning m fit)⟩
  | associatedWrap data =>
    cases found : readAssociatedWrap432 p data with
    | none => simp [check,found] at yes
    | some o =>
      have equal := (matches_associated_report_exact432 r o.report).mp
        (by simpa [check,found] using yes)
      exact ⟨.inr ⟨o,equal⟩,fun m fit => .inr ⟨o,equal,
        dictionary_sound_R16 _ _ _ (exact_associated_report_classifies_R16_432 o) m fit⟩⟩
  | unsupported => simp [check] at yes

theorem all_prior_verdicts_in_R16_432 {s q r}
    (before : Classifies StructuralWhere431.R15 s q r) : Classifies R16 s q r := by
  rcases classification_has_exact_lane_rule426 before with named|endpoint
  · obtain ⟨t,e,⟨actual⟩,summary⟩ := named
    let lift := mapNamedTrace428 (left_named_rule_map428 StructuralWhere431.R15.named426
      associatedWrapLocal432) actual
    exact legacy_classification_included426 ⟨t,e,⟨lift.val⟩,summary⟩
  · exact endpoint_classification_included426 endpoint

theorem verified_R16_result_classifies_in_same_State432 (p : Problem) (r : Result)
    (w : Witness) (good : check p r w = true) :
    Classifies R16 p.state p.root r.verdict ∧
      ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  cases w with
  | previous old =>
    exact ⟨all_prior_verdicts_in_R16_432
      (StructuralWhere431.verified_R15_result_classifies_in_same_State431 p r old good).1,
      (check_sound p r (.previous old) good).2⟩
  | associatedWrap data =>
    obtain ⟨read,meaning⟩ := check_sound p r (.associatedWrap data) good
    refine ⟨?_,meaning⟩
    cases found : readAssociatedWrap432 p data with
    | none => simp [check,found] at good
    | some packet =>
      have same := (matches_associated_report_exact432 r packet.report).mp
        (by simpa [check,found] using good)
      exact same ▸ exact_associated_report_classifies_R16_432 packet
  | unsupported => simp [check] at good

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
