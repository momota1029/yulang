import Yulang.CommonCaseCoreSolvedEnvironments
import Yulang.CommonPatternCoreBoundedSolved
import Yulang.CommonCaseBoundedObservations

/-! Shared Core arm generation retains default, guard and body row bounds.
These independent upper-bound premises are a factor of case typing. They do
not define source coverage, presence legality or a principal case row policy. -/

namespace Yulang.CommonCaseCoreBoundedGeneration

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternAllocation (Slots ambient assignment assignment_ambient bindingSlots bindingSlots_eval
  bindingValues bindingValues_complete)
open CommonPatternSourceScope (corePrefix core_prefix_related)
open CommonPatternCoreBoundedDefaults (DefaultTyped lower covered names_lower)
open CommonCaseCoreEnvironments (GuardTyping consumer consumer_exact)
open CasePatterns (Pattern)

inductive EnvironmentTyping (environment : List (CommonSyntax.Binding Common.model))
    (pattern : Pattern Empty Required.Term) (guard : Option Required.Term) (body : Required.Term)
    (input target : Common.Ty) (cap : Common.Row) : Prop where
  | arm {bindings : NamedTypes} :
      CommonAlignedPatternTyping.Typing (DefaultTyped environment cap) [] pattern input bindings →
      GuardTyping (corePrefix bindings ++ environment) guard cap →
      CommonSyntax.Typing Common.model (corePrefix bindings ++ environment) body (target, cap) →
      EnvironmentTyping environment pattern guard body input target cap

def generateEnvironments (environment : SchemeEnv α) (pattern : Pattern Empty Required.Term)
    (guard : Option Required.Term) (body : Required.Term) (input target : TyTerm α) (cap : RowTerm α) : Formula α :=
  if PatternBindingChecks.check pattern && covered pattern then
    let lowered := lower pattern
    CommonPatternBoundedAllocation.withPattern lowered cap environment [] input
      (consumer lowered environment guard body cap ⟨target, cap⟩)
  else .bot

theorem generateEnvironments_exact (pattern : Pattern Empty Required.Term)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (guard : Option Required.Term) (body : Required.Term) (input target : TyTerm α) (cap : RowTerm α) :
    (generateEnvironments symbolic pattern guard body input target cap).Holds Common.model ρ ↔
      EnvironmentTyping environment pattern guard body (input.eval Common.model ρ)
        (target.eval Common.model ρ) (cap.eval Common.model ρ) := by
  have patternExact := CommonPatternCoreBoundedDefaults.raw_typing_exact coreRelated
    (cap.eval Common.model ρ) pattern [] (input.eval Common.model ρ)
  cases checked : PatternBindingChecks.check pattern && covered pattern with
  | false =>
      simp only [generateEnvironments, checked, Bool.false_eq_true, ↓reduceIte, Formula.Holds]
      constructor
      · exact False.elim
      · intro typed
        cases typed with
        | arm patternTyped guardTyped bodyTyped =>
            have valid := (PatternBindingChecks.check_exact pattern).mpr patternTyped.1
            have within := (patternExact _).mp patternTyped.2
            simp [valid, within.1] at checked
  | true =>
      have gate := Bool.and_eq_true_iff.mp checked
      have valid := (PatternBindingChecks.check_exact pattern).mp gate.1
      simp only [generateEnvironments, checked, ↓reduceIte,
        CommonPatternBoundedAllocation.withPattern_exact _ cap ρ symbolic semantic symbolicRelated,
        consumer_exact _ ρ symbolic environment semantic coreRelated symbolicRelated, evalTypes, List.map_nil,
        CompTerm.eval]
      constructor
      · rintro ⟨values, patternTyped, guardTyped, bodyTyped⟩
        exact .arm ⟨valid, (patternExact _).mpr ⟨gate.2, patternTyped⟩⟩ guardTyped bodyTyped
      · intro typed
        cases typed with
        | arm patternTyped guardTyped bodyTyped =>
            have raw := ((patternExact _).mp patternTyped.2).2
            obtain ⟨values, same⟩ := bindingValues_complete (lower pattern).names _
              (by simpa only [names_lower] using patternTyped.2.binding_names.symm)
            exact ⟨values, same.symm ▸ raw, same.symm ▸ guardTyped, same.symm ▸ bodyTyped⟩

open CommonPatternGenerationProvenance

theorem safe_generateEnvironments (environment : SchemeEnv α) (good : SafeEnvironment environment)
    (pattern : Pattern Empty Required.Term) (guard : Option Required.Term) (body : Required.Term)
    (input : TyTerm α) (inputGood : Input input) (target : TyTerm α) (targetGood : BinderType target)
    (cap : RowTerm α) (capGood : PresenceSourceConstraintSupport.simpleRow cap = true) :
    SafeFormula (generateEnvironments environment pattern guard body input target cap) := by
  unfold generateEnvironments
  split
  · apply safe_close
    exact .and (CommonPatternBoundedProvenance.safe_constraints _ cap capGood environment good []
      (by intro binding member; cases member) input inputGood)
      (CommonCaseCoreSolvedEnvironments.safe_consumer _ environment good guard body cap capGood
        ⟨target, cap⟩ targetGood capGood)
  · exact .bot

abbrev Arm := CommonCaseCoreSolvedEnvironments.Arm

def runtimeArm (arm : Arm) : CaseEvaluation.Arm Empty Required.Term Required.Term Required.Term :=
  ⟨arm.1, arm.2.1, arm.2.2⟩

def GuardTyped (environment : List (CommonSyntax.Binding Common.model)) (cap : Common.Row)
    (code : Required.Term) (bindings : NamedTypes) : Prop :=
  CommonSyntax.Typing Common.model (corePrefix bindings ++ environment) code (.base .bool, cap)

def BodyTyped (environment : List (CommonSyntax.Binding Common.model)) (cap : Common.Row)
    (code : Required.Term) (bindings : NamedTypes) (target : Common.Ty) : Prop :=
  CommonSyntax.Typing Common.model (corePrefix bindings ++ environment) code (target, cap)

theorem environment_arm_exact (environment : List (CommonSyntax.Binding Common.model)) (arm : Arm)
    (input target : Common.Ty) (cap : Common.Row) :
    EnvironmentTyping environment arm.1 arm.2.1 arm.2.2 input target cap ↔
      CommonCaseBoundedObservations.ArmTyping (DefaultTyped environment cap) (GuardTyped environment cap)
        (BodyTyped environment cap) [] (runtimeArm arm) input target := by
  constructor
  · intro typed
    cases typed with
    | arm patternTyped guardTyped bodyTyped =>
        apply CommonCaseBoundedObservations.ArmTyping.arm patternTyped _ bodyTyped
        intro code selected
        change arm.2.1 = some code at selected
        simpa only [GuardTyping, selected, GuardTyped] using guardTyped
  · intro typed
    cases typed with
    | arm patternTyped guardTyped bodyTyped =>
        refine .arm patternTyped ?_ bodyTyped
        cases selected : arm.2.1 with
        | none => exact fun _ impossible => False.elim impossible
        | some code => exact guardTyped code selected

def generateAll (environment : SchemeEnv α) (input target : TyTerm α) (cap : RowTerm α) : List Arm → Formula α
  | [] => .top
  | (pattern, guard, body) :: rest => .and (generateEnvironments environment pattern guard body input target cap)
      (generateAll environment input target cap rest)

theorem generateAll_exact (arms : List Arm) (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic) (input target : TyTerm α) (cap : RowTerm α) :
    (generateAll symbolic input target cap arms).Holds Common.model ρ ↔
      ∀ arm ∈ arms, EnvironmentTyping environment arm.1 arm.2.1 arm.2.2 (input.eval Common.model ρ)
        (target.eval Common.model ρ) (cap.eval Common.model ρ) := by
  induction arms with
  | nil => simp [generateAll, Formula.Holds]
  | cons arm rest ih =>
      rcases arm with ⟨pattern, guard, body⟩
      simp only [generateAll, Formula.Holds,
        generateEnvironments_exact pattern ρ symbolic environment semantic coreRelated symbolicRelated, ih,
        List.mem_cons, forall_eq_or_imp]

theorem safe_generateAll (arms : List Arm) (environment : SchemeEnv α) (good : SafeEnvironment environment)
    (input : TyTerm α) (inputGood : Input input) (target : TyTerm α) (targetGood : BinderType target)
    (cap : RowTerm α) (capGood : PresenceSourceConstraintSupport.simpleRow cap = true) :
    SafeFormula (generateAll environment input target cap arms) := by
  induction arms with
  | nil => exact .top
  | cons arm rest ih =>
      rcases arm with ⟨pattern, guard, body⟩
      exact .and (safe_generateEnvironments environment good pattern guard body input inputGood target targetGood cap capGood) ih

end Yulang.CommonCaseCoreBoundedGeneration
