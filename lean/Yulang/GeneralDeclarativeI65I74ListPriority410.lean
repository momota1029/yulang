import Yulang.GeneralDeclarativeI65I74ListEntry410

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.List410
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)

private theorem only_one_row410 {s q d} (a : InvariantListHead s q d)
    (old : 2 ≤ (visible s.core q).length) : False := by
  simp [a.only] at old

private theorem actual_child_is_variable410 {s q d} (a : InvariantListHead s q d)
    {r : Declaration} (present : r ∈ visible s.core q) {written : Pattern}
    (old : r.head = [written]) {key child} (head : normalize written = .app key [child]) :
    child = .var a.binder := by
  rw [a.only] at present
  cases List.mem_singleton.mp present
  have same := (List.cons.inj (old.symm.trans a.named)).1
  rw [same] at head
  have h : Pattern.app a.key [.var a.binder] = Pattern.app key [child] := head
  exact ((List.cons.inj (Pattern.app.inj h).2).1).symm

private theorem old_authored_entry_is_not_a_visit410 {s q d r}
    (a : InvariantListHead s q d) (entry : AuthoredUnaryEntry403 s q r) : False := by
  have child := actual_child_is_variable410 a entry.visibleRow entry.exactHead entry.dispatch
  have read := entry.literalQuery
  rw [child] at read
  change some (Expr.variable a.binder) = some entry.query at read
  have entered := entry.enters
  rw [← Option.some.inj read] at entered
  cases entered

private theorem old_completed_entry_is_not_a_visit410 {s q d r n}
    (a : InvariantListHead s q d) (entry : CompletedUnaryEntry404 s q r n) : False := by
  have child := actual_child_is_variable410 a entry.visibleRow entry.exactHead entry.dispatch
  have read := entry.exactChild
  rw [child] at read
  change some (Expr.variable a.binder) = some entry.query at read
  have entered := entry.inspecting
  rw [← Option.some.inj read] at entered
  cases entered

private theorem no_old_repeated_ambiguity410 {s q d v}
    (a : InvariantListHead s q d) (old : RepeatedOther403 s q v) : False := by
  cases old with
  | ambiguous _ count => exact only_one_row410 a count

private theorem no_old_variable_or_native_other410 {s q d v needs}
    (a : InvariantListHead s q d)
    (old : variableWithNativeK2403.other s q v needs) : False := by
  rcases old.2 with repeated|⟨_,_,entry,_⟩
  · exact no_old_repeated_ambiguity410 a repeated
  · exact old_authored_entry_is_not_a_visit410 a entry

private theorem no_old_completed_native_other410 {s q d v needs}
    (a : InvariantListHead s q d)
    (old : completedNativePrioritySource404.other s q v needs) : False := by
  rcases old with regular|⟨_,⟨visit⟩⟩
  · exact no_old_variable_or_native_other410 a regular
  · exact old_completed_entry_is_not_a_visit410 a visit.entry

private theorem no_old_completed_choice_other410 {s q d v needs}
    (a : InvariantListHead s q d)
    (old : completedChoiceSource404.other s q v needs) : False := by
  rcases old with regular|⟨_,⟨ambiguous⟩⟩
  · exact no_old_completed_native_other410 a regular
  · exact only_one_row410 a ambiguous.two

/-- The same singleton candidate produces neither of the older
candidate-local K2 branches: both would inspect a child which is
actually a plain variable. Root K2 still has its independent veto. -/
theorem invariant_list_keeps_actual_inspection_priority410 {s q d v needs}
    (a : InvariantListHead s q d) :
    ¬Named409.R1.other s q v needs := by
  rintro ⟨rule,family,old⟩
  cases family with
  | variableOnly =>
    cases old.2 with
    | ambiguous _ count => exact only_one_row410 a count
  | repeated | whereTree => exact no_old_repeated_ambiguity410 a old.2
  | nativeK2 | supported => exact no_old_variable_or_native_other410 a old
  | supportedK2 => exact no_old_completed_native_other410 a old
  | supportedAmbiguity | authoredNative => exact no_old_completed_choice_other410 a old

theorem list_rule_is_a_new_local_family410 {s q} {e : Event s q}
    (list : InvariantListRead e) {needs} : ¬Named409.R1.elected s q e needs := by
  rintro (legacy|named)
  · rcases R0_selection_uses_independent_original_rule407 e legacy with general|native
    · have inScope : e.frame.decl ∈ visible s.core q := by simp [list.test.only]
      have atHead : Pattern.app list.test.key [.var list.test.binder] ∈ e.frame.decl.head := by
        simp [list.test.named]
      obtain ⟨_,absurd,_⟩ := general.2 _ inScope _ atHead
      cases absurd
    · obtain ⟨native⟩ := native
      have h := (List.cons.inj (native.test.writtenHead.symm.trans list.test.named)).1
      change Pattern.app native.test.key [.var native.test.binder] =
        Pattern.app list.test.key [.var list.test.binder] at h
      have key := (Pattern.app.inj h).1
      have mode := native.test.table
      rw [key,list.test.table] at mode
      cases mode
  · obtain ⟨_,⟨bare⟩⟩ := named
    have h := (List.cons.inj (bare.test.named.symm.trans list.test.named)).1
    have lengths := congrArg List.length (Pattern.app.inj h).2
    cases lengths

theorem R2_raw_K2_priority410 {s q} (raw : RootCycle s q) :
    Classifies R2 s q .rejected ∧ ∀ d, ¬Classifies R2 s q (.selected d) :=
  ⟨root_k2_is_rejected_for_every_primitive_system raw,fun _ => root_k2_never_selects raw⟩

open Checker408 (Problem Result)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

theorem list_wire_exact410 (p : Problem) (r : Result) (w : ListWire)
    (yes : check p r (.listLeaf w) = true) :
    ∃ (d : Declaration) (scope : visible p.state.core p.root = [d]) (source : VerifiedList p d),
      replayListHead p d scope w = some source ∧ r = Check408.nullaryReport d := by
  simp only [check] at yes
  split at yes
  · rename_i d scope
    obtain ⟨found,matchOut⟩ := splitAnd yes
    cases replay : replayListHead p d scope w with
    | none => simp [replay] at found
    | some captured =>
      obtain ⟨sameTree,sameResult,sameWrites⟩ := Check408.matchesNoWrites_exact408.mp matchOut
      refine ⟨d,scope,captured,replay,?_⟩
      cases r
      simp only at sameTree sameResult sameWrites
      subst_vars
      rfl
  · simp at yes

/-- The output of reflection is the actual selected source event, with
the original payload retained as its lexical capture, not a second
model-dependent reconstruction. -/
theorem checked_report_retains_actual_payload410 (p : Problem) (r : Result) (w : ListWire)
    (yes : check p r (.listLeaf w) = true) :
    ∃ (d : Declaration) (original : VerifiedList p d) (event : Event p.state p.root)
      (trace : SourceTrace R2 p.state p.root r.tree (some event)),
      event.frame.input original.known.binder =
        GeneralDeclarativeWitnessDeclaredState357.point original.known.payload ∧
      CommonRoleOutermostResolver.Summarizes r.tree r.verdict ∧
      r.writes = writes trace := by
  obtain ⟨d,_,original,_,same⟩ := list_wire_exact410 p r w yes
  subst r
  obtain ⟨event,trace,capture,output⟩ := list_choice_captures_exact_report410 original
  exact ⟨d,original,event,trace,capture,.selected .nil (.selected rfl),output.symm⟩

theorem list_and_prior_witnesses_cannot_both_succeed410 (p : Problem) (r a : Result)
    (w : ListWire) (old : Named409.Witness) (yes : check p r (.listLeaf w) = true) :
    check p a (.previous old) = false := by
  obtain ⟨d,here,packet,_,_⟩ := list_wire_exact410 p r w yes
  cases success : check p a (.previous old) with
  | false => rfl
  | true =>
    have prior : Named409.check p a old = true := success
    exfalso
    cases old with
    | unsupported => simp [Named409.check] at prior
    | bareName wire =>
      obtain ⟨other,there,previous,_,_⟩ := Named409.bare_name_wire_exact409 p a wire prior
      have same := (List.cons.inj (here.symm.trans there)).1
      have sameHead := congrArg Declaration.head same
      have scans := packet.known.named.symm.trans (sameHead.trans previous.known.named)
      have h := (List.cons.inj scans).1
      have arity := congrArg List.length (Pattern.app.inj h).2
      cases arity
    | previous old =>
      have legacy : Checker408.check p a old = true := prior
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

theorem checked_results_are_unique410 (p : Problem) (r a : Result) (x y : Witness)
    (first : check p r x = true) (second : check p a y = true) : r = a := by
  cases x with
  | unsupported => simp [check] at first
  | previous old =>
    cases y with
    | unsupported => simp [check] at second
    | previous y => exact Named409.checked_results_are_unique409 p r a old y first second
    | listLeaf next =>
      rw [list_and_prior_witnesses_cannot_both_succeed410 p a r next old second] at first
      cases first
  | listLeaf next =>
    cases y with
    | unsupported => simp [check] at second
    | previous y =>
      rw [list_and_prior_witnesses_cannot_both_succeed410 p r a next y first] at second
      cases second
    | listLeaf y =>
      obtain ⟨d,firstAt,_,_,firstReport⟩ := list_wire_exact410 p r next first
      obtain ⟨e,secondAt,_,_,secondReport⟩ := list_wire_exact410 p a y second
      have exactDecl := (List.cons.inj (firstAt.symm.trans secondAt)).1
      exact firstReport.trans ((congrArg Check408.nullaryReport exactDecl).trans secondReport.symm)

end Yulang.GeneralDeclarativeI65.I72.List410
