import Yulang.GeneralDeclarativeWitnessNativePipeline360
import Yulang.GeneralDeclarativeWitnessNativeSnapshot360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 56000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralDeclarativeWitnessNestedInstall360
open GeneralDeclarativeWitnessNativePreparation360 (Prepared Layout prepare)
open GeneralDeclarativeWitnessNativePipeline360 (stamp gate authority wire valueCode authorizedAddress)
open GeneralDeclarativeWitnessNativeBodyFixture360 (whereClause childDecl)
open GeneralDeclarativeWitnessJointObservation359 (parentScope parentSpan secondSpan)
open GeneralDeclarativeWitnessNominalRecordFixture359 (current sourceDecl)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessNativeValue360 (Compiled compile)
open GeneralDeclarativeWitnessNativeSnapshot360 (commit commits_exact_snapshot)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews atTarget)
open GeneralDeclarativeWitnessNativeRelease360 (checkExactRelease)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Models)

def written (negative : Bool) : Declaration :=
  {sourceDecl negative with requirements := [whereClause], associated :=
    [⟨111,0,.app 55 [.app (if negative then 42 else 20) [.var 80]]⟩]}

def sourceEnv (negative : Bool) : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨5,2,[(0,none)]⟩,⟨6,1,[(0,none)]⟩]⟩,
    declarations := [written negative,childDecl]}

def requested : Demand := ⟨5,[parentSpan,secondSpan],[⟨0,101⟩]⟩
def layout : Layout :=
  ⟨current,[(80,parentSpan),(81,secondSpan)],[61,67,101,105],fun _ => ⟨0,0,0⟩,fun _ _ => 105⟩

structure Run (negative : Bool) where
  env : Environment
  prep : Prepared env parentScope requested layout
  typed : Compiled prep table (wire negative) 3
  final : World
  wrote : commit prep typed ⟨layout.named,gate⟩ = some final

def native (negative : Bool) : Option (Run negative) := do
  let env ← sourceEnv negative
  let prep ← prepare env parentScope requested layout
  let typed ← compile prep table (wire negative) 3
  match committed : commit prep typed ⟨layout.named,gate⟩ with
  | none => none
  | some result => some ⟨env,prep,typed,result,committed⟩

def checks {negative} (a : Run negative) : Bool :=
  decide (a.prep.impl = written negative ∧
    a.prep.whereRows = [⟨105,.variable 61⟩] ∧
    a.prep.kids.map printDemand = [(6,[(106,61,107)],[(0,105)])] ∧
    a.typed.write = ⟨authorizedAddress,valueCode negative⟩) &&
  decide (atTarget a.final.board 101 = some a.typed.write) &&
    (checkExactRelease a.final.board authority a.typed.write).isSome

theorem unchanged_two_nested_heads_install (negative : Bool) :
    ((native negative).map checks).getD false = true := by cases negative <;> decide +kernel

theorem previous_checker_was_not_a_language_refusal (negative : Bool) :
    ((sourceEnv negative).map fun e =>
      !GeneralDeclarativeWitnessCovariantDescent353.legal e.source (written negative) &&
      GeneralDeclarativeWitnessNestedDescent360.check e.source (written negative)).getD false = true := by
  cases negative <;> decide +kernel

theorem native_commit_true_in_same_model {negative} (r : Run negative)
    (m : Assignment) (views : NativeViews) (holds : Fits r.final m views) :
    Models current m ∧ views 101 = some (r.typed.code.eval m) := by
  have info := GeneralDeclarativeWitnessNativeSnapshot360.current_target_keeps_others
    r.prep r.typed r.wrote m views holds
  exact ⟨info.1,info.2.1⟩

end Yulang.GeneralDeclarativeWitnessNestedInstall360
