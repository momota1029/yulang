import Yulang.GeneralDeclarativeI65I72FiniteNativeCompatibility406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open CommonRoleOutermostResolver (Dictionary Summarizes)

theorem a_literal_typed_nominal_cannot_name_different_constructors406 {s slots c p k j}
    (tree : NamedMixedTree401 s slots c p)
    (first : DeclaredHead404 k tree) (another : DeclaredHead404 j tree) : k = j := by
  cases tree with
  | declaredApp name use _ _ _ => exact first.1.symm.trans another.1
  | binder | record | variant | join | scalar | emptyRecord | exactEmpty | pair => cases first

/-- Two actually visible candidate roots at the same literal argument
ordinal. Both are real unary declarations and have variable children;
the second outer tag differs from the one read from the *same exact*
completed typed output. An unknown head is not represented as a miss. -/
structure TwoCompletedNativeRows406 (s : State) (q : Request) (first later : Declaration)
    (need : OutputNeed s) where
  originalArg : Capture
  argAt : q.demand.arguments = [originalArg]
  visibleAt : visible s.core q = [first,later]
  known : Nat
  centerBinderFirst : Nat
  other : Nat
  binderLater : Nat
  writesFirst : first.head = [authoredUnaryPattern405 known centerBinderFirst]
  writesLater : later.head = [authoredUnaryPattern405 other binderLater]
  otherDeclaration : Use s.core.current.environment other 1
  otherIsDeclared : ∃ ps, otherDeclaration.mode = .declared ps
  otherDoesNotMatch : known ≠ other
  payload : Nat
  fixesLower : need.expected.original.target = originalArg.lower
  exactTyped : TypedCovariantPoint404 known payload need.expected.rhs

/-- Scope of actual mismatch, not of whole-candidate selection:
the first root has this original source's tag, the second root has
a distinct declared tag. Both visits precede tests for variable
children (which do not inspect constructors) and preserve original
registry order. Raw root K2 uses the same ordinary graph. -/
theorem actual_completed_lower_shows_ordered_root_mismatch406 {s q first later p d original}
    (producer : FiniteNative406 s p d original) (i : Fin p.demand.outputs.length)
    (actual : TwoCompletedNativeRows406 s q first later ⟨p,d,i,original i⟩)
    (safe : ¬RootCycle s q) :
    (⟨actual.originalArg.lower,.nominal actual.known [.variable actual.payload]⟩ : Equation)
      ∈ s.core.current.ordinary.equations ∧
    DeclaredHead404 actual.known (original i).rhs ∧
    ¬ DeclaredHead404 actual.other (original i).rhs ∧
    ∃ (low high : Nat) (visits : List CandidateVisit),
      visits = [⟨low,0,[],.value,false,actual.originalArg.lower⟩,
        ⟨high,0,[],.value,false,actual.originalArg.lower⟩] ∧ low < high ∧
      (authoredRegistry s.core.current).declarations[low]? = some first ∧
      (authoredRegistry s.core.current).declarations[high]? = some later ∧
      ∀ step ∈ visits, ¬CurrentCycleAt s step.site := by
  let key := fun d : Declaration => d.role == q.demand.role
  let originalRows := (authoredRegistry s.core.current).declarations
  have a : (visible s.core q)[0]? = some first := by simp [actual.visibleAt]
  have b : (visible s.core q)[1]? = some later := by simp [actual.visibleAt]
  obtain ⟨left,whereLeft,atLeft⟩ := unfilterOrdinal395_exact key originalRows 0 a
  obtain ⟨right,whereRight,atRight⟩ := unfilterOrdinal395_exact key originalRows 1 b
  have order := unfilter_keeps_original_order405 key originalRows (by decide : 0 < 1) whereLeft whereRight
  have typed := actual_typed_point_yields_literal_declared_code404 (original i).rhs actual.exactTyped
  have retained := chosen_finite_native_output_retains_exact_nominal406 producer i actual.fixesLower typed.1 typed.2
  let firstSite : CandidateVisit := ⟨left,0,[],.value,false,actual.originalArg.lower⟩
  let laterSite : CandidateVisit := ⟨right,0,[],.value,false,actual.originalArg.lower⟩
  refine ⟨retained,typed.1,fun clash => actual.otherDoesNotMatch
    (a_literal_typed_nominal_cannot_name_different_constructors406 _ typed.1 clash),
    left,right,[firstSite,laterSite],rfl,order,atLeft,atRight,?_⟩
  intro step entered cycle
  have lower : step.site = actual.originalArg.lower := by
    rcases List.mem_cons.mp entered with h | h
    · cases h
      rfl
    · cases List.mem_singleton.mp h
      rfl
  rw [lower] at cycle
  exact safe ⟨actual.originalArg,by simp [actual.argAt],cycle⟩

private theorem scoped_selected_requires_singleton406 {s q t d}
    (source : ScopedSource406 s q t) (done : Summarizes t (.selected d)) :
    (visible s.core q).length = 1 := by
  cases source with
  | prior existing =>
    cases existing with
    | rootK2 => cases done
    | other v _ _ _ => cases v <;> cases done
    | selected _ raw chosen support _ =>
      obtain ⟨scan,_⟩ := (authored_and_variable_rules_ground_the_same_trace405 raw chosen support).byActualRule
      cases scan with
      | variableCase actual => simp [actual.sole]
      | nominal actual => simp [actual.test.visibleOnly]
  | completed e => simp [e.chosen.gate.only]

/-- This is a negative test of the current *proof coverage*, not of
the language. A structurally known rival can fail as above, but no
positive rule in the current exposed calculus assembles a selected
head when the registry still contains two live candidates to inspect. -/
theorem two_actual_visible_rows_need_a_wider_positive_rule406 {s q d}
    (two : 2 ≤ (visible s.core q).length) :
    ¬ FiniteVerdict406 s q (.selected d) := by
  intro choice
  have one : (visible s.core q).length = 1 := by
    cases choice with
    | prior trace done => exact scoped_selected_requires_singleton406 trace done
    | selected selected =>
      cases selected with
      | base source done _ => exact scoped_selected_requires_singleton406 source done
      | advance _ step _ => simp [step.head.gate.only]
  omega

end Yulang.GeneralDeclarativeI65.I72
