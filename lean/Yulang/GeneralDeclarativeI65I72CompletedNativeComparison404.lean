import Yulang.GeneralDeclarativeI65I72ClosedSupportBoundary404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (Legal names visited visitedList)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open CommonRecursiveNominalIntervals (Endpoint ContextWellFormed)
open GeneralDeclarativeHead320 (Equation)
open PresenceNormalForm (Atom)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern normalize)

abbrev coValue404 : CommonDeclaredNominalInspection.Parameter := ⟨.value,.covariant⟩

theorem original_typed_point_has_canonical_declared_mode404 {s slots c p key logical}
    (tree : NamedMixedTree401 s slots c p) (actual : TypedCovariantPoint404 key logical tree) :
    ∃ use : Use s.current.environment key 1,
      use.mode = .declared [coValue404] ∧ s.modes[key]? = some [coValue404] := by
  cases tree with
  | declaredApp name use authored table args =>
    have keyExact : name = key := actual.1
    have mode : use.mode = .declared [coValue404] := actual.2.1
    have point : singlePointName404 args = some logical := actual.2.2
    subst key
    rw [mode,names] at authored
    have exactTable := table.trans (congrArg some (Option.some.inj authored).symm)
    cases args with
    | nil => cases point
    | cons first rest =>
      cases rest with
      | nil => exact ⟨use,mode,exactTable⟩
      | cons => cases point
  | binder | record | variant | join | scalar | emptyRecord | exactEmpty | pair => exact False.elim actual

def unaryNominalPoint404 (key logical : Nat) : Endpoint Nat :=
  .nominal key [.inl (.point (.ordinary (.var logical)))]

private theorem unary_point_context_wellformed404 {s : State} {key logical : Nat}
    (mode : s.core.modes[key]? = some [coValue404]) :
    ContextWellFormed s.core.modes false (unaryNominalPoint404 key logical) :=
  .nominal mode (.cons (.valuePoint (.ordinary false (.var logical))) (.nil false))

/-- Independent positive comparison of the same source pair as the
entered-site rule, when the actual paired ordinary atom is present.
Do not fabricate a native Origin for the completed lower operand. -/
theorem completed_pair_compares_from_actual_atom404 {s q row need}
    (entry : CompletedUnaryEntry404 s q row need)
    (checked : Atom.tyLe (.var entry.lowerChild) (.var entry.upperChild) ∈
      s.core.current.ordinary.normal.ordinary) :
    Nonempty (DeclaredComparison s.core.current.environment s.core.current.ordinary s.core.modes
      false (unaryNominalPoint404 entry.key entry.lowerChild) (unaryNominalPoint404 entry.key entry.upperChild)) := by
  obtain ⟨use,mode,table⟩ := original_typed_point_has_canonical_declared_mode404 need.expected.rhs entry.lowerTerm
  have authority : Legal s.core.current.environment s.core.modes (entry.key,1) := by
    refine ⟨use,[coValue404],?_,table⟩
    change names use.mode 1 = some [coValue404]
    rw [mode]; rfl
  refine ⟨⟨?_,unary_point_context_wellformed404 table,unary_point_context_wellformed404 table,
    .nominal table (.cons (.covariantValue (.ordinary checked)) .nil)⟩⟩
  intro candidate present
  have identity : candidate = (entry.key,1) := by
    simpa [unaryNominalPoint404,visited,visitedList] using present
  exact identity ▸ authority

theorem selected_completed_lower_and_authored_upper_same_model404 {s q row needs need}
    (entry : CompletedUnaryEntry404 s q row need)
    (support : SupportForest completedChoiceSource404 s needs)
    (slot : Nat) (indexed : needs[slot]? = some need)
    (checked : Atom.tyLe (.var entry.lowerChild) (.var entry.upperChild) ∈
      s.core.current.ordinary.normal.ordinary)
    (m : Model) (fit : Fits s m) :
    (⟨entry.input.lower,.nominal entry.key [.variable entry.lowerChild]⟩ : Equation) ∈
      s.core.current.ordinary.equations ∧
    m.nativeSyntax entry.upper.slot = some (unaryNominalPoint404 entry.key entry.upperChild) ∧
    ContextWellFormed s.core.modes false (unaryNominalPoint404 entry.key entry.lowerChild) ∧
    ContextWellFormed s.core.modes false (unaryNominalPoint404 entry.key entry.upperChild) ∧
    ContextDerives s.core.modes m.assignment false (unaryNominalPoint404 entry.key entry.lowerChild)
      (unaryNominalPoint404 entry.key entry.upperChild) := by
  obtain ⟨positive⟩ := completed_pair_compares_from_actual_atom404 entry checked
  have completed := (completed_lower_justifies_entered_native_child404
    entry completed_choice_keeps_fixed_rows404 support slot indexed).1
  have upper : m.nativeSyntax entry.upper.slot = some entry.upper.endpoint := fit.2 _ entry.upperAuthored
  rw [entry.upperSyntax] at upper
  exact ⟨completed,upper,in_same_model positive m.assignment fit.1.1⟩

/-- The old modeled head interface asks for an authored lower
Origin. Its absence cannot be repaired merely by the exact
completed equation or comparison above. This is a representation
boundary, not a negative language result. -/
theorem no_authored_lower_prevents_old_mode_window404 {s : State} {a : Capture} {p : Pattern}
    (none : ∀ o : Origin, o ∈ s.core.origins → ¬ OriginRoute s.core o a.lower) :
    ¬ Nonempty (ModeWindow s.core a p) := by
  rintro ⟨window⟩
  exact none window.lower window.lowerAuthored window.lo


/-- For an actual literal declared unary pattern, every constructor
of the old positive head carrier is excluded without an authored
lower Origin: the legacy ordinary translation cannot inspect it,
the ModeWindow asks for that Origin, and a joined variant has a
different authored shape. The new comparison itself does not fail. -/
theorem completed_positive_pair_outside_old_head_carrier404 {s q row need}
    (entry : CompletedUnaryEntry404 s q row need)
    {arg : Pattern} (surface : entry.written = .app entry.key [arg])
    (noOldLower : ∀ o : Origin, o ∈ s.core.origins → ¬ OriginRoute s.core o entry.input.lower) :
    ¬ Nonempty (SourceHead s.core q row) := by
  rintro ⟨matched⟩
  cases matched with
  | ordered cap reads =>
    have compared : DeepHead s.core cap entry.input entry.written := ordered_head_at reads (i := 0)
      (by simp [entry.exactInput]) (by simp [entry.exactHead])
    cases compared with
    | ordinary prior =>
      obtain ⟨_,_,translation,_⟩ := prior
      obtain ⟨declared,mode,_⟩ :=
        original_typed_point_has_canonical_declared_mode404 need.expected.rhs entry.lowerTerm
      have impossible := declared_application_not_ordinary (s := s.core) (ps := [arg])
        (mode ▸ declared.sourced)
      rw [surface,impossible] at translation
      cases translation
    | declared native _ =>
      exact no_authored_lower_prevents_old_mode_window404 noOldLower ⟨native⟩
  | joined unified =>
    have exactWords : unified.written = entry.written :=
      List.cons.inj (unified.head.symm.trans entry.exactHead) |>.1
    have impossible := unified.normalized
    rw [exactWords,entry.dispatch] at impossible
    cases impossible

end Yulang.GeneralDeclarativeI65.I72
