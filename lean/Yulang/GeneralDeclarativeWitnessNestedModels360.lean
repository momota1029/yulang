import Yulang.GeneralDeclarativeWitnessNestedInstall360
import Yulang.GeneralDeclarativeWitnessNativeModel360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 56000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralDeclarativeWitnessNestedModels360
open GeneralDeclarativeWitnessNestedInstall360
  (Run native checks unchanged_two_nested_heads_install)
open GeneralDeclarativeWitnessNativeModel360 (afterWhere model fitting_ordinary_nonpoint)
open GeneralDeclarativeWitnessNativePipeline360 (valueCode)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted NativeViews fit_after_install)
open GeneralDeclarativeWitnessNativeSnapshot360 (commits_exact_snapshot)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessRecordWidthFixture359 (endpoints_ordered)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom)

def secondAtoms : List (Atom Nat) := [(67,67),(67,67),(108,65),(65,108),(109,66),(66,109),(108,67),(67,109)].map
  fun a => .tyLe (.var a.1) (.var a.2)

def stage : State := ⟨⟨afterWhere.normal.ordinary ++ secondAtoms,afterWhere.normal.intervals⟩,afterWhere.equations⟩

def verifyStage {negative} (r : Run negative) : Bool :=
  GeneralDeclarativeWitnessNativeSnapshot360.same r.prep.stage stage

theorem exact_ordinary_nested_stage (negative : Bool) : ((native negative).map verifyStage).getD false = true := by
  cases negative <;> decide +kernel

def commonModel (upper : Bool) (base : Inference.Base) : Assignment := fun x =>
  if x = 108 then model upper base 65
  else if x = 109 then model upper base 66
  else model upper base x

theorem fitting_nested (upper : Bool) (base : Inference.Base) : Models stage (commonModel upper base) := by
  have no8 : 108 ∉ stateNames afterWhere := by decide +kernel
  have no9 : 109 ∉ stateNames afterWhere := by decide +kernel
  have common (n : Nat) (used : n ∈ stateNames afterWhere) : model upper base n = commonModel upper base n := by
    have n8 : n ≠ 108 := fun eq => no8 (eq ▸ used)
    have n9 : n ≠ 109 := fun eq => no9 (eq ▸ used)
    simp [commonModel,n8,n9]
  have prior := (preserves_models afterWhere common).mp (fitting_ordinary_nonpoint upper base)
  refine ⟨⟨?_,prior.1.2⟩,prior.2⟩
  intro atom present
  have stored : atom ∈ afterWhere.normal.ordinary ∨ atom ∈ secondAtoms := List.mem_append.mp present
  rcases stored with old|added
  · exact prior.1.1 _ old
  · simp only [secondAtoms,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at added
    rcases added with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases upper <;> first | exact subtype_refl _ | exact endpoints_ordered

theorem actual_nested_has_native_model {negative} {r : Run negative} (ran : native negative = some r)
    (upper : Bool) (base : Inference.Base) :
    Fits r.final (commonModel upper base) (interpreted r.final.board (commonModel upper base)) := by
  have strict := exact_ordinary_nested_stage negative
  rw [ran] at strict
  have same : r.prep.stage = stage :=
    GeneralDeclarativeWitnessNativeSnapshot360.same_exact.mp (show verifyStage r = true from strict)
  have installed := (commits_exact_snapshot r.prep r.typed r.wrote).2
  apply fit_after_install r.prep r.typed installed
  rw [same]
  exact fitting_nested upper base

theorem authored_nested_value_in_every_fitting_model {negative} {r : Run negative}
    (ran : native negative = some r) (m : Assignment) (v : NativeViews) (fit : Fits r.final m v) :
    v 101 = some ((valueCode negative).eval m) := by
  have accepted := unchanged_two_nested_heads_install negative
  rw [ran] at accepted
  have pass : checks r = true := accepted
  have source := of_decide_eq_true
    (GeneralDeclarativeWitnessProblem349.splitAnd (GeneralDeclarativeWitnessProblem349.splitAnd pass).1).1
  have code : r.typed.code = valueCode negative := congrArg Write.code source.2.2.2
  have actual := (GeneralDeclarativeWitnessNestedInstall360.native_commit_true_in_same_model r m v fit).2
  rw [code] at actual
  exact actual

theorem actual_two_heads_compiled_and_fitted (negative : Bool) :
    ∃ r, native negative = some r ∧
      (∀ upper base,Fits r.final (commonModel upper base) (interpreted r.final.board (commonModel upper base))) ∧
      (∀ m v,Fits r.final m v → v 101 = some ((valueCode negative).eval m)) := by
  have ok := unchanged_two_nested_heads_install negative
  cases ran : native negative with
  | none => rw [ran] at ok; cases ok
  | some r => exact ⟨r,rfl,actual_nested_has_native_model ran,authored_nested_value_in_every_fitting_model ran⟩

end Yulang.GeneralDeclarativeWitnessNestedModels360
