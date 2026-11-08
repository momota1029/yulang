import Yulang.CommonCoreDataPrefixes
import Yulang.CommonCaseCoreRecordPrefixSolved

/-! A finite source gate checks every actual subject/default/guard/body.
It strengthens the existing independent Core arm derivation without changing
pattern order, binder slots or any default environment. Unsupported source
code is rejected before solving; it is not hidden by a runtime contract. -/

namespace Yulang.CommonCaseCoreDataGate

set_option backward.isDefEq.respectTransparency false

open Core
open CommonCoreDataEvaluation (Supported supported supported_exact)
open CommonCaseCoreBoundedGeneration (Arm runtimeArm)
open CasePatterns (Pattern)
open CommonAlignedPatternTyping (RawTyping)

def defaults : Pattern F D → List D
  | .wildcard | .bind _ | .literal _ | .intRange _ _ | .recordEnd | .nil => []
  | .pair first last | .field _ first last | .cons first last | .snoc first last | .or first last =>
      defaults first ++ defaults last
  | .defaultField _ code first last => code :: (defaults first ++ defaults last)
  | .variant _ child | .nominal _ _ child | .as child _ => defaults child

/-- A syntactic property of all actual default occurrences may be carried
through the old constructor derivation, including both aligned or branches. -/
theorem strengthen_defaults (predicate : D → Prop)
    (typed : RawTyping DefaultTyped types pattern input bindings)
    (allowed : ∀ code ∈ defaults pattern, predicate code) :
    RawTyping (fun types code type => DefaultTyped types code type ∧ predicate code)
      types pattern input bindings := by
  induction typed with
  | wildcard => exact .wildcard
  | bind => exact .bind
  | literal below => exact .literal below
  | intRange below bounded => exact .intRange below bounded
  | recordEnd => exact .recordEnd
  | pair _ _ ihp ihq =>
      exact .pair (ihp (fun code member => allowed code (List.mem_append_left _ member)))
        (ihq (fun code member => allowed code (List.mem_append_right _ member)))
  | field below _ _ ihp ihr =>
      exact .field below (ihp (fun code member => allowed code (List.mem_append_left _ member)))
        (ihr (fun code member => allowed code (List.mem_append_right _ member)))
  | defaultField below fallback _ _ ihp ihr =>
      exact .defaultField below ⟨fallback, allowed _ List.mem_cons_self⟩
        (ihp (fun code member => allowed code (List.mem_cons_of_mem _ (List.mem_append_left _ member))))
        (ihr (fun code member => allowed code (List.mem_cons_of_mem _ (List.mem_append_right _ member))))
  | variant _ ih => exact .variant (ih allowed)
  | or _ _ ihp ihq =>
      exact .or (ihp (fun code member => allowed code (List.mem_append_left _ member)))
        (ihq (fun code member => allowed code (List.mem_append_right _ member)))
  | as _ ih => exact .as (ih allowed)
  | narrow below _ ih => exact .narrow below (ih allowed)

def PatternSupported (pattern : Pattern Empty Required.Term) : Prop :=
  ∀ code ∈ defaults pattern, Supported code

def GuardSupported (guard : Option Required.Term) : Prop :=
  ∀ code, guard = some code → Supported code

def ArmSupported (arm : Arm) : Prop :=
  PatternSupported arm.1 ∧ GuardSupported arm.2.1 ∧ Supported arm.2.2

def SourceSupported (subject : Required.Term) (arms : List Arm) : Prop :=
  Supported subject ∧ ∀ arm ∈ arms, ArmSupported arm

def guardCheck : Option Required.Term → Bool
  | none => true
  | some code => supported code

def armCheck (arm : Arm) : Bool :=
  (defaults arm.1).all supported && guardCheck arm.2.1 && supported arm.2.2

def check (subject : Required.Term) (arms : List Arm) : Bool :=
  supported subject && arms.all armCheck

theorem guard_check_exact (guard : Option Required.Term) : guardCheck guard = true ↔ GuardSupported guard := by
  cases guard <;> simp [guardCheck, GuardSupported, supported_exact]

theorem arm_check_exact (arm : Arm) : armCheck arm = true ↔ ArmSupported arm := by
  simp [armCheck, ArmSupported, PatternSupported, Bool.and_eq_true, List.all_eq_true,
    supported_exact, guard_check_exact, and_assoc]

theorem check_exact (subject : Required.Term) (arms : List Arm) :
    check subject arms = true ↔ SourceSupported subject arms := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, SourceSupported, supported_exact, arm_check_exact]

def DefaultTyped (cap : Common.Row) (types : CommonPatternEnvironment.NamedTypes)
    (code : Required.Term) (type : Common.Ty) : Prop :=
  CommonPatternCoreBoundedDefaults.DefaultTyped [] cap types code type ∧ Supported code

def GuardTyped (cap : Common.Row) (code : Required.Term) (types : CommonPatternEnvironment.NamedTypes) : Prop :=
  CommonCaseCoreBoundedGeneration.GuardTyped [] cap code types ∧ Supported code

def BodyTyped (cap : Common.Row) (code : Required.Term) (types : CommonPatternEnvironment.NamedTypes)
    (target : Common.Ty) : Prop :=
  CommonCaseCoreBoundedGeneration.BodyTyped [] cap code types target ∧ Supported code

theorem arm_typing (arm : Arm) (input target : Common.Ty) (cap : Common.Row)
    (within : ArmSupported arm)
    (typed : CommonCaseCoreBoundedGeneration.EnvironmentTyping [] arm.1 arm.2.1 arm.2.2 input target cap) :
    CommonCaseBoundedObservations.ArmTyping (DefaultTyped cap) (GuardTyped cap) (BodyTyped cap)
      [] (runtimeArm arm) input target := by
  cases typed with
  | arm patternTyped guardTyped bodyTyped =>
      refine .arm ⟨patternTyped.1, strengthen_defaults Supported patternTyped.2 within.1⟩ ?_ ⟨bodyTyped, within.2.2⟩
      intro code selected
      change arm.2.1 = some code at selected
      refine ⟨?_, within.2.1 code selected⟩
      simpa only [CommonCaseCoreEnvironments.GuardTyping, selected,
        CommonCaseCoreBoundedGeneration.GuardTyped] using guardTyped

end Yulang.CommonCaseCoreDataGate
