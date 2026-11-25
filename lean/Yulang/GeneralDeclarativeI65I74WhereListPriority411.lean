import Yulang.GeneralDeclarativeI65I74WhereListEntry411
import Yulang.GeneralDeclarativeI65I74ListPriority410

namespace Yulang.GeneralDeclarativeI65.I72.WhereCycle411
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarations (Declaration)
open Checker408 (Problem Result)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessDeclaredState357 (point)

private theorem only_one_row411 {s q d} (a : WhereListHead s q d)
    (old : 2 ≤ (visible s.core q).length) : False := by
  simp [a.only] at old

private theorem actual_child_is_variable411 {s q d} (a : WhereListHead s q d)
    {r : Declaration} (present : r ∈ visible s.core q) {written : Pattern}
    (old : r.head = [written]) {key child} (head : normalize written = .app key [child]) :
    child = .var a.binder := by
  rw [a.only] at present
  cases List.mem_singleton.mp present
  have same := (List.cons.inj (old.symm.trans a.named)).1
  rw [same] at head
  have h : Pattern.app a.key [.var a.binder] = Pattern.app key [child] := head
  exact ((List.cons.inj (Pattern.app.inj h).2).1).symm

private theorem old_authored_entry_is_not_a_visit411 {s q d r}
    (a : WhereListHead s q d) (entry : AuthoredUnaryEntry403 s q r) : False := by
  have child := actual_child_is_variable411 a entry.visibleRow entry.exactHead entry.dispatch
  have read := entry.literalQuery
  rw [child] at read
  change some (Expr.variable a.binder) = some entry.query at read
  have entered := entry.enters
  rw [← Option.some.inj read] at entered
  cases entered

private theorem old_completed_entry_is_not_a_visit411 {s q d r n}
    (a : WhereListHead s q d) (entry : CompletedUnaryEntry404 s q r n) : False := by
  have child := actual_child_is_variable411 a entry.visibleRow entry.exactHead entry.dispatch
  have read := entry.exactChild
  rw [child] at read
  change some (Expr.variable a.binder) = some entry.query at read
  have entered := entry.inspecting
  rw [← Option.some.inj read] at entered
  cases entered

private theorem no_old_repeated_ambiguity411 {s q d v}
    (a : WhereListHead s q d) (old : RepeatedOther403 s q v) : False := by
  cases old with
  | ambiguous _ count => exact only_one_row411 a count

private theorem no_old_variable_or_native_other411 {s q d v needs}
    (a : WhereListHead s q d)
    (old : variableWithNativeK2403.other s q v needs) : False := by
  rcases old.2 with repeated|⟨_,_,entry,_⟩
  · exact no_old_repeated_ambiguity411 a repeated
  · exact old_authored_entry_is_not_a_visit411 a entry

private theorem no_old_completed_native_other411 {s q d v needs}
    (a : WhereListHead s q d)
    (old : completedNativePrioritySource404.other s q v needs) : False := by
  rcases old with regular|⟨_,⟨visit⟩⟩
  · exact no_old_variable_or_native_other411 a regular
  · exact old_completed_entry_is_not_a_visit411 a visit.entry

private theorem no_old_completed_choice_other411 {s q d v needs}
    (a : WhereListHead s q d)
    (old : completedChoiceSource404.other s q v needs) : False := by
  rcases old with regular|⟨_,⟨ambiguous⟩⟩
  · exact no_old_completed_native_other411 a regular
  · exact only_one_row411 a ambiguous.two

/-- The same singleton candidate produces neither of the older
candidate-local K2 branches: both would inspect a child which is
actually a plain variable. Root K2 still has its independent veto. -/
theorem invariant_list_keeps_actual_inspection_priority411 {s q d v needs}
    (a : WhereListHead s q d) :
    ¬R3.other s q v needs := by
  rintro ⟨rule,family,old⟩
  cases family with
  | variableOnly =>
    cases old.2 with
    | ambiguous _ count => exact only_one_row411 a count
  | repeated | whereTree => exact no_old_repeated_ambiguity411 a old.2
  | nativeK2 | supported => exact no_old_variable_or_native_other411 a old
  | supportedK2 => exact no_old_completed_native_other411 a old
  | supportedAmbiguity | authoredNative => exact no_old_completed_choice_other411 a old

theorem accepted_where_wire_reflects_actual_child411 (p : Problem) (r : Result) (w : CycleWire)
    (yes : check p r (.whereChild w) = true) :
    ∃ (d : Declaration) (scope : visible p.state.core p.root = [d]) (source : VerifiedWhereList p d),
      replayWhereList411 p d scope w.parent = some source ∧ RootCycle p.state source.known.child ∧
        r = expected411 d := by
  simp only [check] at yes
  split at yes
  · rename_i d scope
    split at yes
    · cases yes
    · rename_i source found
      obtain ⟨raw,out⟩ := splitAnd yes
      obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp out
      refine ⟨d,scope,source,found,GeneralDeclarativeWitnessCycle350.rooted raw,?_⟩
      cases r
      simp only at tree verdict writes
      subst_vars
      rfl
  · simp at yes

/-- The rejection is attached to the actual emitted child at ordinal 0
of this selected declaration. The parent is independently not a raw root K2.
Neither a fabricated request nor a reported path is supplied to the checker. -/
theorem accepted_where_wire_reaches_literal_occurrence411 (p : Problem) (r : Result) (w : CycleWire)
    (yes : check p r (.whereChild w) = true) :
    ∃ (d : Declaration) (event : Event p.state p.root) (child : I72.Request) (name payload : Nat),
      event.frame.decl = d ∧ R3.elected p.state p.root event [] ∧ event.kids = [child] ∧
      child.occurrence = p.root.occurrence ++ [0] ∧
      child.demand.role = p.root.demand.role ∧
      child.demand.arguments = [event.frame.input name] ∧
      event.frame.input name = point payload ∧
      ¬RootCycle p.state p.root ∧ RootCycle p.state child ∧ r = expected411 d := by
  obtain ⟨d,_,source,_,cyclic,report⟩ := accepted_where_wire_reflects_actual_child411 p r w yes
  obtain ⟨e,rule,decl,kids,value,_⟩ := selected_where_is_exact_actual_child411 source
  refine ⟨d,e,source.known.child,source.known.binder,source.known.payload,
    decl,rule,kids,rfl,source.known.whereRole,?_,value,source.rawSafe,cyclic,report⟩
  change [point source.known.payload] = [e.frame.input source.known.binder]
  rw [value]

theorem where_and_prior_witnesses_cannot_both_succeed411 (p : Problem) (r a : Result)
    (w : CycleWire) (old : List410.Witness) (yes : check p r (.whereChild w) = true) :
    check p a (.previous old) = false := by
  obtain ⟨d,here,packet,_,_,_⟩ := accepted_where_wire_reflects_actual_child411 p r w yes
  cases success : check p a (.previous old) with
  | false => rfl
  | true =>
    have prior : List410.check p a old = true := success
    exfalso
    cases old with
    | unsupported => simp [List410.check] at prior
    | listLeaf wire =>
      obtain ⟨other,there,previous,_,_⟩ := List410.list_wire_exact410 p a wire prior
      have same := (List.cons.inj (here.symm.trans there)).1
      cases same
      have contradiction := previous.known.noWhere
      rw [packet.known.exactWhere] at contradiction
      cases contradiction
    | previous old =>
      have earlier : Named409.check p a old = true := prior
      cases old with
      | unsupported => simp [Named409.check] at earlier
      | bareName wire =>
        obtain ⟨other,there,previous,_,_⟩ := Named409.bare_name_wire_exact409 p a wire earlier
        have same := (List.cons.inj (here.symm.trans there)).1
        have scans := packet.known.named.symm.trans ((congrArg Declaration.head same).trans previous.known.named)
        have h := (List.cons.inj scans).1
        have arity := congrArg List.length (Pattern.app.inj h).2
        cases arity
      | previous old =>
        have legacy : Checker408.check p a old = true := earlier
        cases old with
        | unsupported => simp [Checker408.check] at legacy
        | rawRoot proof =>
          have actual := ((Checker408.raw_closed_cycle_uses_the_same_checker408 p a proof).mp legacy).1
          exact packet.rawSafe (GeneralDeclarativeWitnessCycle350.rooted actual)
        | nullary =>
          have branch := Checker408.accepted_implies_branch_engine408 p a .nullary legacy
          obtain ⟨_,_,hdr,_⟩ := (Check408.bool_nullary_protocol_exact408 p a).mp branch
          have none := List.isEmpty_iff.mp (splitAnd (splitAnd hdr).1).2
          rw [packet.known.asked] at none
          cases none

theorem checked_results_are_unique411 (p : Problem) (r a : Result) (x y : Witness)
    (first : check p r x = true) (second : check p a y = true) : r = a := by
  cases x with
  | unsupported => simp [check] at first
  | previous old =>
    cases y with
    | unsupported => simp [check] at second
    | previous y => exact List410.checked_results_are_unique410 p r a old y first second
    | whereChild next =>
      rw [where_and_prior_witnesses_cannot_both_succeed411 p a r next old second] at first
      cases first
  | whereChild next =>
    cases y with
    | unsupported => simp [check] at second
    | previous y =>
      rw [where_and_prior_witnesses_cannot_both_succeed411 p r a next y first] at second
      cases second
    | whereChild y =>
      obtain ⟨d,firstAt,_,_,_,firstReport⟩ := accepted_where_wire_reflects_actual_child411 p r next first
      obtain ⟨e,secondAt,_,_,_,secondReport⟩ := accepted_where_wire_reflects_actual_child411 p a y second
      have exactDecl := (List.cons.inj (firstAt.symm.trans secondAt)).1
      exact firstReport.trans ((congrArg expected411 exactDecl).trans secondReport.symm)

end Yulang.GeneralDeclarativeI65.I72.WhereCycle411
