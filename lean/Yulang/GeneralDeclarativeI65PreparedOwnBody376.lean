import Yulang.GeneralDeclarativeI65CurrentRelease376

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Compiled)
open GeneralDeclarativeWitnessCompiler350 (Finished execute fixedBatch portNames placed)
open GeneralDeclarativeEntailment320 (Holds)

theorem prepared_owns_literal_finished_body {env frame d layout}
    (p : Prepared env frame d layout) {f : Finished}
    (ran : execute (GeneralDeclarativeWitnessNativePreparation360.context env d p.impl layout) = some f) :
    f.beforeOutputs = p.stage ∧ f.kids = p.kids ∧
      fixedBatch (GeneralDeclarativeWitnessNativePreparation360.context env d p.impl layout) p.ports =
        some f.fixed := by
  let c := GeneralDeclarativeWitnessNativePreparation360.context env d p.impl layout
  change execute c = some f at ran
  cases outputs : fixedBatch c p.ports with
  | none =>
    have no : execute c = none := by simp [execute,c,p.ranPrepare,p.ranWhere,show fixedBatch c p.ports = none from outputs]
    rw [no] at ran
    cases ran
  | some rows =>
    have exactBody : execute c = some ⟨p.stage,rows,p.kids⟩ := by
      simp [execute,c,p.ranPrepare,p.ranWhere,show fixedBatch c p.ports = some rows from outputs]
      exact ⟨rfl,rfl⟩
    have lit := Option.some.inj (exactBody.symm.trans ran)
    cases lit
    exact ⟨rfl,rfl,rfl⟩

theorem same_prepared_author_in_finished_and_typed_body {env frame d layout table wire version}
    (p : Prepared env frame d layout) {f : Finished}
    (ran : execute (GeneralDeclarativeWitnessNativePreparation360.context env d p.impl layout) = some f)
    (typed : Compiled p table wire version) :
    f.kids = p.kids ∧ f.beforeOutputs = p.stage ∧
      typed.write.address.owner.path = frame.occurrence ∧
      typed.write.address.owner.version = version ∧
      typed.write.address.declarationOrdinal = frame.sourceOrdinal ∧
      typed.write.address.outputOrdinal = wire.ordinal ∧
      typed.write.address.target = typed.supplied.requested.target :=
  ⟨(prepared_owns_literal_finished_body p ran).2.1,
    (prepared_owns_literal_finished_body p ran).1,rfl,rfl,rfl,rfl,typed.supplied.fixed.symm⟩

/-- In this represented slice both compilers use the same real preparation.
The theorem does not elect that frame or introduce its independently
supplied grant, or promise an ordinary translation for typed-only outputs. -/
theorem one_authored_preparation_keeps_ordered_and_typed_meaning
    {s : State} {q : Request} {frame layout table wire version}
    (p : Prepared s.current.environment frame q.demand layout) {f : Finished}
    (body : execute (GeneralDeclarativeWitnessNativePreparation360.context
      s.current.environment q.demand p.impl layout) = some f)
    (sourcePath : frame.occurrence = q.occurrence)
    (typed : Compiled p table wire version)
    {base : GeneralDeclarativeWitnessNativeInstall360.Board}
    {installed : GeneralDeclarativeWitnessNativeInstall360.World}
    (ran : GeneralDeclarativeWitnessNativeInstall360.install p typed base = some installed)
    {more : List GeneralDeclarativeWitnessNativeValue360.Write}
    (disjoint : ∀ row ∈ more,typed.write.address.target ≠ row.address.target)
    (gate : GeneralDeclarativeWitnessNativeRelease360.ReleaseAuthority)
    (grant : typed.write.address ∈ gate.grants)
    (atoms : f.state.normal.ordinary ⊆ s.current.ordinary.normal.ordinary)
    (intervals : f.state.normal.intervals ⊆ s.current.ordinary.normal.intervals)
    (later : List GeneralDeclarativeHead320.Equation)
    (ordinary : s.current.ordinary.equations = f.state.equations ++ later)
    (m : Model) (fit : Fits s m)
    (views : GeneralDeclarativeWitnessNativeInstall360.NativeViews)
    (observes : GeneralDeclarativeWitnessNativeInstall360.Fits
      ⟨s.current.ordinary,appendOtherWrites installed.board more⟩ m.assignment views) :
    children q f.kids = children q p.kids ∧
    typed.write.address.owner.path = q.occurrence ∧
    (∀ eq ∈ f.fixed,Holds m.assignment eq) ∧
    views typed.write.address.target = some (typed.write.code.eval m.assignment) := by
  have ordered := (prepared_owns_literal_finished_body p body).2.1
  refine ⟨congrArg (children q) ordered,sourcePath,?_⟩
  have allowed := (emitted_row_remains_exactly_openable typed ran disjoint gate).mpr grant
  cases read : GeneralDeclarativeWitnessNativeRelease360.checkExactRelease
      (appendOtherWrites installed.board more) gate typed.write with
  | none => simp [read] at allowed
  | some released =>
    have ordinaryBody : execute (GeneralDeclarativeWitnessDeclaredState357.context
        s.current q.demand p.impl layout.named layout.spans layout.keep layout.fallback layout.targets) = some f := body
    exact current_ordinary_and_native_receipts ordinaryBody atoms intervals later ordinary m fit views observes released

end Yulang.GeneralDeclarativeI65
