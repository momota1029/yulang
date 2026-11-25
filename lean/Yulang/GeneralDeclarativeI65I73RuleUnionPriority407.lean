import Yulang.GeneralDeclarativeI65I73RuleUnionInclusions407

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeInspect321 (PatternK2)
open CommonRoleOutermostResolver (Summarizes)

private theorem all_variable_refutes_written_constructor407 {s : State} {q : Request} {row written key child}
    (all : ∀ d ∈ visible s.core q, ∀ p ∈ d.head, ∃ n, p = Pattern.var n)
    (rowAt : row ∈ visible s.core q) (literal : row.head = [written])
    (normalized : normalize written = .app key [child]) : False := by
  have declared : written ∈ row.head := by simp [literal]
  obtain ⟨n,h⟩ := all row rowAt written declared
  rw [h] at normalized
  cases normalized

private theorem fixed_family_other_contained407 {R : SourcePrimitives}
    (family : FixedEvidenceFamily407 R) {s q verdict needs}
    (competing : R.other s q verdict needs) :
    (2 ≤ (visible s.core q).length) ∨ completedChoiceSource404.other s q verdict needs := by
  cases family with
  | variableOnly =>
    cases competing.2 with
    | ambiguous _ many => exact .inl many
  | repeated | whereTree =>
    exact .inr (.inl (.inl ⟨competing.1,.inl competing.2⟩))
  | nativeK2 | supported => exact .inr (.inl (.inl competing))
  | supportedK2 => exact .inr (.inl competing)
  | supportedAmbiguity | authoredNative => exact .inr competing

private theorem old_other_needs_real_competing_root407 {s q verdict needs}
    (competing : completedChoiceSource404.other s q verdict needs) :
    (2 ≤ (visible s.core q).length) ∨
    AuthoredCandidateK2403 s q ∨ Nonempty (CompletedChildK2404 s q needs) := by
  rcases competing with earlier|fresh
  · rcases earlier with untyped|typed
    · rcases untyped.2 with several|entered
      · cases several with
        | ambiguous _ two => exact .inl two
      · exact .inr (.inl entered.2)
    · exact .inr (.inr typed.2)
  · obtain ⟨many⟩ := fresh.2
    exact .inl many.two

/-- The primitive union cannot select over a known supported entered K2
or pick a single survivor over one of the represented ambiguities.
This argument compares the complete visible head scopes, not rule
tags, homogeneous whole-result soundness, or models. -/
theorem R0_no_local_diagnostic_conflicts_with_selection407 {s q}
    (e : Event s q) {selectedNeeds diagnosticNeeds verdict}
    (chosen : R0.elected s q e selectedNeeds)
    (other : R0.other s q verdict diagnosticNeeds) : False := by
  obtain ⟨_,family,competing⟩ := other
  have alternatives := fixed_family_other_contained407 family competing
  rcases R0_selection_uses_independent_original_rule407 e chosen with ⟨only,shape⟩|⟨native⟩
  · have manyImpossible : ¬ 2 ≤ (visible s.core q).length := by simp [only]
    have all : ∀ d ∈ visible s.core q, ∀ p ∈ d.head, ∃ n, p = Pattern.var n := by
      intro d dAt p pAt
      obtain ⟨n,literal,_⟩ := shape d dAt p pAt
      exact ⟨n,literal⟩
    rcases alternatives with many|prior
    · exact manyImpossible many
    rcases old_other_needs_real_competing_root407 prior with many|authored|completed
    · exact manyImpossible many
    · obtain ⟨_,entry,_⟩ := authored
      exact all_variable_refutes_written_constructor407 (s := s) (q := q) all
        entry.visibleRow entry.exactHead entry.dispatch
    · obtain ⟨entered⟩ := completed
      exact all_variable_refutes_written_constructor407 (s := s) (q := q) all
        entered.entry.visibleRow entered.entry.exactHead entered.entry.dispatch
  · obtain ⟨native⟩ := native
    rcases alternatives with many|prior
    · simp [native.test.visibleOnly] at many
    · exact authored_unary_inherits_no_competing_local_diagnostic405 native.test prior

/-- A real completed-child raw K2 proof may be sourced by any R0 family,
not just the child-K2 family itself; its fixed row follows from the
exact support producer. Selection still cannot outrank that local
diagnostic, and raw root rejection precedes it. -/
theorem R0_exact_completed_child_uses_mixed_support407 {s q needs}
    (prior : CompletedChildK2404 s q needs)
    (support : SupportForest R0 s needs) :
    Classifies R0 s q .rejected ∧
    PatternK2 s.core.current.ordinary prior.entry.lowerChild prior.entry.query ∧
    (⟨prior.entry.input.lower,.nominal prior.entry.key [.variable prior.entry.lowerChild]⟩ :
      Equation) ∈ s.core.current.ordinary.equations ∧
    ∀ d, ¬Classifies R0 s q (.selected d) := by
  have primitive : R0.other s q .rejected needs :=
    ⟨completedNativePrioritySource404,.supportedK2,.inr ⟨rfl,⟨prior⟩⟩⟩
  have exact := completed_lower_justifies_entered_native_child404 prior.entry R0_keeps_fixed_rows407
    support prior.index prior.onList
  classical
  have reject : Classifies R0 s q .rejected := by
    by_cases raw : RootCycle s q
    · exact (R0_raw_root_priority407 raw).1
    · exact ⟨.rejected,none,⟨.other .rejected raw primitive support⟩,.rejected⟩
  refine ⟨reject,⟨_,exact.2.2,prior.cycle⟩,exact.1,?_⟩
  intro d chosen
  obtain ⟨t,_,⟨trace⟩,done⟩ := chosen
  cases trace with
  | rootK2 => cases done
  | other verdict => cases verdict <;> cases done
  | selected e _ source _ _ =>
    exact R0_no_local_diagnostic_conflicts_with_selection407 e source primitive

end Yulang.GeneralDeclarativeI65.I72
