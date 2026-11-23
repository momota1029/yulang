import Yulang.GeneralDeclarativeI65ActualUnaryDispatch379

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessConstructorModes357 (Environment Mode SourceMode)
open GeneralDeclarativeWitnessNativeKinds361 (tag KindTag)
open GeneralDeclarationPatterns (normalize)
open CommonDeclaredNominalInspection (Parameter Kind)

/-- The authored `declared` route occupies a specific source graph
entry. This does not claim that every arbitrary snapshot primitive/
invariant combination is coherent. -/
theorem authored_declared_mode_is_unique {e : Environment} {key : Nat} {params : List Parameter}
    (given : SourceMode e key (.declared params)) {other : Mode}
    (also : SourceMode e key other) : other = .declared params := by
  cases given with
  | declared entry _ _ =>
    cases also with
    | primitive _ absent =>
      rw [entry] at absent
      cases absent
    | invariant _ absent =>
      rw [entry] at absent
      cases absent
    | declared stored _ _ =>
      exact congrArg Mode.declared (Option.some.inj (stored.symm.trans entry))

/-- The checked unary C361 constructor and the exact early source
pre use the same declared one-value mode. A physical source
address or model value is not used to infer variance. -/
theorem actual_dispatch_uses_same_authored_value_variance
    {s : State} {q : Request} {row : GeneralDeclarations.Declaration}
    {allowed : Origin → Prop} {side : OriginalSide}
    (pre : NativeHeadPrefix s q row allowed side)
    (release : CurrentReleasedOrigin s pre.atBound.original)
    {route : GeneralDeclarativeWitnessNominalSource359.Route}
    (step : UnaryDispatch s.current.environment route release.exactWrite.code (normalize pre.pattern)) :
    ∃ variance, pre.params = [⟨.value,variance⟩] ∧
      step.ctor.mode = .declaredValue variance ∧ s.modes[pre.key]? = some [⟨.value,variance⟩] := by
  have sameKey := (authored_prefix_and_unary_dispatch_agree pre release step).1
  have ofPrefix : SourceMode s.current.environment pre.key (.declared pre.params) :=
    pre.authoredMode ▸ pre.tdecl.sourced
  have atK : SourceMode s.current.environment pre.key step.ctor.use.mode :=
    sameKey.symm ▸ step.ctor.use.sourced
  have same := authored_declared_mode_is_unique ofPrefix atK
  have result := step.ctor.exact
  rw [same] at result
  cases layout : pre.params with
  | nil => simp [layout,tag] at result
  | cons p rest =>
    obtain ⟨kind,variance⟩ := p
    cases rest with
    | cons x rest => simp [layout,tag] at result
    | nil =>
      cases kind with
      | row => simp [layout,tag] at result
      | value =>
        have mode : step.ctor.mode = .declaredValue variance := by
          simpa [layout,tag,eq_comm] using result
        exact ⟨variance,rfl,mode,by simpa [layout] using pre.laidOut⟩

/-- Once the actual unary branch has dispatched, any represented
value port on this exact parent corresponds to its sole literal
child. Its physical leaf and authored query are taken from the
dispatch, not guessed from the result of a comparison. -/
theorem dispatched_unary_value_port_targets_literal_child
    {s : State} {q : Request} {row : GeneralDeclarations.Declaration}
    {allowed : Origin → Prop} {side : OriginalSide} {inherited : Bool}
    (pre : NativeHeadPrefix s q row allowed side) (port : NativeValuePort pre inherited)
    (release : CurrentReleasedOrigin s pre.atBound.original)
    {route : GeneralDeclarativeWitnessNominalSource359.Route}
    (step : UnaryDispatch s.current.environment route release.exactWrite.code (normalize pre.pattern)) :
    port.index = 0 ∧ port.actualPattern = step.fromPattern ∧
      port.which.payload = GeneralDeclarativeWitnessNativeOrder362.node step.fromCode ∧
      ∃ variance, port.parameter = ⟨.value,variance⟩ ∧
        step.ctor.mode = .declaredValue variance := by
  obtain ⟨variance,parameters,actualMode,_⟩ := actual_dispatch_uses_same_authored_value_variance pre release step
  obtain ⟨_,written,source⟩ := authored_prefix_and_unary_dispatch_agree pre release step
  have readParam := port.declared
  rw [parameters] at readParam
  have atZero : port.index = 0 := by
    cases found : port.index with
    | zero => rfl
    | succ i => simp [found] at readParam
  rw [atZero] at readParam
  have sameParam : port.parameter = ⟨.value,variance⟩ := (Option.some.inj readParam).symm
  have gotPattern := port.written
  rw [atZero] at gotPattern
  have exactPattern := Option.some.inj (gotPattern.symm.trans written)
  have gotSource := port.sourceAt
  rw [atZero] at gotSource
  have point := Sum.inl.inj (Option.some.inj (gotSource.symm.trans source))
  have literal := endpoint_port_from_one_original port.exactReads port.present
  rw [point] at literal
  refine ⟨atZero,exactPattern,literal.trans ?_,⟨variance,sameParam,actualMode⟩⟩
  cases port.which.original <;> rfl

end Yulang.GeneralDeclarativeI65
