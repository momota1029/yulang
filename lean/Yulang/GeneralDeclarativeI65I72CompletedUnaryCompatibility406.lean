import Yulang.GeneralDeclarativeI65I72CompletedUnaryPositive406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree Result Summarizes Dictionary)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- Before the new source branch is evidenced, every represented
verdict is exactly the old judgment; lack of a new witness is not
itself classified as pending or as rejected. -/
theorem no_new_preselection_reflects_old_classifies406 {s q result}
    (unavailable : ∀ (row : Declaration) (needs : List (OutputNeed s))
      (forest : SupportForest PriorSource406 s needs), ¬Nonempty (PreselectedUnary406 s q row forest)) :
    ScopedClassifies406 s q result ↔ Classifies PriorSource406 s q result := by
  constructor
  · rintro ⟨t,⟨trace⟩,summary⟩
    cases trace with
    | prior given => exact ⟨t,_,⟨given⟩,summary⟩
    | completed e => exact False.elim (unavailable e.row e.needs e.forest ⟨e.chosen⟩)
  · exact previous_classification_embeds406

theorem prior_exact_writes_unchanged_when_embedded406 {s q d} (old : Ledger s q d) :
    (ScopedLedger406.prior old).written = old.written := rfl

/-- Replacing the source of the lower fact, where both existing
rules apply, does not move the visited root to another declaration,
argument, mode or physical/logical site. This is byte-for-byte
equality of the list, not membership after a permutation. -/
theorem authored_and_completed_use_same_root_visit406 {s q row e needs forest}
    (old : AuthoredNativeSelected405 (s := s) (q := q) e)
    (selected : PreselectedUnary406 s q row (needs := needs) forest) :
    old.visits = selected.visits := by
  have input : old.test.interval = selected.gate.arg :=
    (List.cons.inj (old.test.writtenArgs.symm.trans selected.gate.exactArg)).1
  have zero := (actual_authored_native_tape_keeps_exact_source_pick405 old.origin).2
  have original := old.origin.ordinal
  rw [zero,selected.exactOrdinal] at original
  have atI : old.origin.rawOrdinal = selected.authoredOrdinal := Option.some.inj original.symm
  unfold AuthoredNativeSelected405.visits PreselectedUnary406.visits
  rw [input,atI]

/-- When the original typed center indication is literally the same,
the positive completed branch retains the old actual payload name
even with different lower proof objects. Endpoints alone do not
give the conclusion. -/
theorem same_original_center_has_compatible_native_readback406 {s q row e needs forest}
    (old : AuthoredNativeSelected405 (s := s) (q := q) e)
    {selected : PreselectedUnary406 s q row (needs := needs) forest} (payload : OriginalPayload406 selected)
    (original : old.payload.actual = payload.source) :
    (e.frame.input old.test.binder).center =
      ((originalNativeFrame406 selected payload).input selected.gate.binder).center := by
  have rowEq : e.frame.decl = row := (List.cons.inj (old.test.visibleOnly.symm.trans selected.gate.only)).1
  have head := old.test.writtenHead
  rw [congrArg Declaration.head rowEq,selected.gate.exactHead] at head
  have key : selected.gate.key = old.test.key := (Pattern.app.inj (List.cons.inj head).1).1
  have exactRead := payload.exactPath
  rw [key,← original,old.payload.literalCenter] at exactRead
  have equal : old.payload.payload.center = payload.center := by
    simpa [literalUnaryPayloadName406,unaryNominalPoint404] using exactRead
  have prior := (actual_authored_native_uses_original_payload_center405 old).1
  rw [prior,equal]
  change payload.center = (payload.names selected.gate.binder).center
  simp [OriginalPayload406.names,OriginalPayload406.interval]

/-- The entire prior C404 C405-source fragment embeds with the same
diagnostic, request, chosen original Event and ordered dependencies.
No occurrence or B6 output is searched for or reconstructed. -/
noncomputable def original_prior_trace_lift406 {s q t e}
    (trace : SourceTrace completedChoiceSource404 s q t e) : SourceTrace PriorSource406 s q t e :=
  SourceTrace.rec (R := completedChoiceSource404) (s := s)
    (motive_1 := fun q t e _ => SourceTrace PriorSource406 s q t e)
    (motive_2 := fun qs ts _ => WhereForest PriorSource406 s qs ts)
    (motive_3 := fun needs _ => SupportForest PriorSource406 s needs)
    (fun raw => .rootK2 raw)
    (fun verdict safe primitive _ forest => .other verdict safe primitive forest)
    (fun event safe witness _ _ forest children => .selected event safe (.inl witness) forest children)
    .nil (fun _ _ first later => .cons first later)
    .nil (fun _ complete typed _ first later => .cons first complete typed later)
    trace

theorem old_entered_K2_remains_actual_in_scoped_rules406 {s q} (run : GroundedK2Rejection405 s q) :
    ∃ trace : ScopedSource406 s q .rejected,
      trace = .prior (original_prior_trace_lift406 run.source) ∧
      Summarizes .rejected .rejected ∧
      ((RootCycle s q ∧ run.visits = []) ∨
      (¬RootCycle s q ∧ ∃ (row : Declaration) (need : OutputNeed s)
        (address : NativeEntryAddress405 s q row need),
      run.visits = [address.site] ∧ CurrentCycleAt s address.site.site ∧
      GeneralDeclarativeInspect321.Visit (GeneralDeclarativeGraphRows321.structural s.core.current.ordinary)
        address.entry.lowerChild address.entry.query address.site.site)) :=
  ⟨.prior (original_prior_trace_lift406 run.source),rfl,.rejected,k2_replay_visits_are_justified405 run⟩

private theorem literal_completed_candidate_cannot_enter_its_variable_child406 {s q row need}
    (gate : CompletedUnaryGate406 s q row need)
    {otherNeed : OutputNeed s} {r : Declaration} (entry : CompletedUnaryEntry404 s q r otherNeed) : False := by
  have same : r = row := by
    have here := entry.visibleRow
    rw [gate.only] at here
    exact List.mem_singleton.mp here
  have rhs := entry.exactHead
  rw [congrArg Declaration.head same,gate.exactHead] at rhs
  have sameWritten := (List.cons.inj rhs).1
  have chosen := entry.dispatch
  rw [← sameWritten] at chosen
  change Pattern.app gate.key [.var gate.binder] = Pattern.app entry.key [entry.child] at chosen
  have child : entry.child = .var gate.binder := (List.cons.inj (Pattern.app.inj chosen).2).1.symm
  have translate := entry.exactChild
  rw [child] at translate
  change some (Expr.variable gate.binder) = some entry.query at translate
  have inspects := entry.inspecting
  rw [← Option.some.inj translate] at inspects
  cases inspects

/-- A real earlier entered child rejection cannot be bypassed by a
new completed positive rule. In the covered positive shape the child
is a variable, so the two competing source frontiers are disjoint. -/
theorem entered_old_k2_cannot_be_replaced_by_new_positive406 {s q ts}
    (run : GroundedK2Rejection405 s q) (later : CompletedInvocation406 s q ts) : False := by
  cases run with
  | raw root => exact later.chosen.rootSafe root
  | entered _ _ _ _ address _ =>
    exact literal_completed_candidate_cannot_enter_its_variable_child406 later.chosen.gate address.entry

end Yulang.GeneralDeclarativeI65.I72
