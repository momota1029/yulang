import Yulang.GeneralDeclarativeWitnessNativePipeline360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNativeSnapshot360
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Compiled)
open GeneralDeclarativeWitnessNativeInstall360
  (World Fits NativeViews interpreted install actual_installation other_target_unchanged)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)

def same (first last : State) : Bool :=
  decide (first.normal.ordinary = last.normal.ordinary ∧ first.normal.intervals = last.normal.intervals ∧
    first.equations = last.equations)

theorem same_exact {first last : State} : same first last = true ↔ first = last := by
  constructor
  · intro equal
    have parts := of_decide_eq_true equal
    obtain ⟨fo,fi,fe⟩ := parts
    cases first with
    | mk f fs =>
      cases last with
      | mk l ls =>
        cases f with
        | mk fa fb =>
          cases l with
          | mk la lb =>
            dsimp at fo fi fe
            subst fa
            subst fb
            subst fs
            rfl
  · rintro rfl
    simp [same]

/-- Version check alone does not imply that the body read the current
ordinary snapshot. Installation called through this gate takes the two
pieces from one explicitly supplied prior state. -/
def commit {e frame d l} (p : Prepared e frame d l) {table wire version}
    (written : Compiled p table wire version) (prior : World) : Option World :=
  if same prior.ordinary l.named then install p written prior.board else none

theorem commits_exact_snapshot {e frame d l} (p : Prepared e frame d l) {table wire version}
    (a : Compiled p table wire version) {prior final} (actual : commit p a prior = some final) :
    prior.ordinary = l.named ∧ install p a prior.board = some final := by
  unfold commit at actual
  split at actual
  · rename_i ok
    exact ⟨same_exact.mp ok,actual⟩
  · cases actual

theorem current_target_keeps_others {e frame d l} (p : Prepared e frame d l) {table wire version}
    (a : Compiled p table wire version) {prior final} (ran : commit p a prior = some final)
    (m : Assignment) (v : NativeViews) (fit : Fits final m v) :
    Models prior.ordinary m ∧ v wire.target = some (a.code.eval m) ∧
      ∀ slot,slot ≠ wire.target → v slot = interpreted prior.board m slot := by
  obtain ⟨source,ins⟩ := commits_exact_snapshot p a ran
  have exact := actual_installation p a ins m v fit
  refine ⟨source.symm ▸ exact.2.1,exact.1,?_⟩
  intro slot apart
  unfold install at ins
  split at ins
  · have equal := Option.some.inj ins
    subst final
    rw [fit.2 slot]
    unfold interpreted
    exact congrArg (Option.map (fun row => row.code.eval m)) (other_target_unchanged prior.board a.write slot apart)
  · cases ins

end Yulang.GeneralDeclarativeWitnessNativeSnapshot360
