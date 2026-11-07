import Yulang.CommonCaseFinitePrefixes
import Yulang.CommonPatternCoreBoundedSolved

/-! The exact missing source-computation interface, with no total finite
callback assumption. Boolean guards are read from the same value evaluator;
the invalid-value branch is proved unreachable under its typing contract.
No general Core evaluator or full runtime value carrier is defined here. -/

namespace Yulang.CommonPatternCorePrefixBridge

open Core
open PresenceGeneration
open CommonPatternFinitePrefixes (Computation Safe ops logic)
open CommonPatternEnvironment (NamedTypes)
open CommonPatternSourceScope (corePrefix)
open CommonPatternTyping (valueAt bindingTypes)
open CommonPatternCoreBoundedDefaults (DefaultTyped)
open CaseValues (Bindings BindingsHold)

/-- B3/B5 must provide a source-prefix producer satisfying this contract.
Every represented finite observation is checked, without demanding a return.
Completeness against actual source prefixes is a separate adequacy claim. -/
def EvaluationSound (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model))
    (evaluate : Bindings Empty → Required.Term → Computation E R CommonData.Value) : Prop :=
  ∀ types code result, CommonSyntax.Typing Common.model (corePrefix types ++ environment) code result →
    ∀ actual, BindingsHold (bindingTypes types) actual →
      Safe source failure (evaluate actual code) (valueAt result.1) result.2

theorem default_sound (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model))
    (evaluate : Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate) (cap : Common.Row) :
    CommonPatternComputationSafety.DefaultSound (logic source failure) cap (DefaultTyped environment cap) evaluate := by
  intro types code type typed actual valid
  obtain ⟨row, typed, below⟩ := typed
  exact CommonCaseFinitePrefixes.row_mono source failure _ _ row cap
    (sound types code (type, row) typed actual valid) below

def asBool : CommonData.Value → Option Bool
  | .literal (.bool value) => some value
  | _ => none

theorem boolean_readout (value : CommonData.Value) (typed : valueAt (.base .bool) value) :
    ∃ boolean, value = .literal (.bool boolean) ∧ asBool value = some boolean := by
  obtain ⟨literal, rfl, kind⟩ := CommonPatternLookup.literal_of_base typed .bool (Common.subtype_refl _)
  cases literal with
  | bool value => exact ⟨value, rfl, rfl⟩
  | int | str | unit => cases kind
  | float impossible => cases impossible

def guardOf (evaluate : Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (invalid : Computation E R Bool) (code : Required.Term) (actual : Bindings Empty) : Computation E R Bool :=
  (ops E R).bind (evaluate actual code) fun value =>
    match asBool value with
    | some boolean => (ops E R).ret boolean
    | none => invalid

/-- The invalid runtime readout is not assumed safe. Typing excludes that
branch internally, so any concrete source error implementation may fill it. -/
theorem guard_sound (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model))
    (evaluate : Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate) (invalid : Computation E R Bool)
    (cap : Common.Row) (types : NamedTypes) (code : Required.Term)
    (typed : CommonSyntax.Typing Common.model (corePrefix types ++ environment) code (.base .bool, cap))
    (actual : Bindings Empty) (valid : BindingsHold (bindingTypes types) actual) :
    Safe source failure (guardOf evaluate invalid code actual) (fun _ => True) cap := by
  apply CommonPatternFinitePrefixes.bind_safe source failure _ _ (valueAt (.base .bool)) _ cap
    (sound types code _ typed actual valid)
  intro value valueTyped
  obtain ⟨boolean, same, decoded⟩ := boolean_readout value valueTyped
  simp only [decoded]
  exact CommonPatternFinitePrefixes.ret_safe source failure boolean _ cap True.intro

theorem model_pattern_prefixes (pattern : CasePatterns.Pattern Empty Required.Term) (cap : RowTerm α)
    (ρ : α → PresenceGeneration.Comp Common.model) (symbolic : PresenceGeneration.SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (PresenceGeneration.Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : PresenceGeneration.EnvRel Common.model ρ symbolic semantic)
    (prior : CommonPatternEnvironment.NamedTerms α) (input : TyTerm α)
    (model : (CommonPatternCoreBoundedDefaults.generatePattern cap symbolic prior pattern input).Holds Common.model ρ)
    (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate)
    (actual : Bindings Empty) (valid : BindingsHold (bindingTypes (CommonPatternEnvironment.evalTypes ρ prior)) actual)
    (floatCheck : Empty → Empty → Bool) (subject : CommonData.Value) (within : valueAt (input.eval Common.model ρ) subject) :
    ∃ bindings, CommonAlignedPatternTyping.Typing (DefaultTyped environment (cap.eval Common.model ρ))
        (CommonPatternEnvironment.evalTypes ρ prior) pattern (input.eval Common.model ρ) bindings ∧
      Safe source failure (CommonPatternComputations.run (ops E R) floatCheck evaluate actual pattern subject)
        (CommonPatternComputationSafety.OptionHolds bindings) (cap.eval Common.model ρ) := by
  obtain ⟨bindings, typed⟩ := (CommonPatternCoreBoundedDefaults.generatePattern_exact pattern cap ρ symbolic
    environment semantic coreRelated symbolicRelated prior input).mp model
  exact ⟨bindings, typed, CommonPatternFinitePrefixes.typing_finite_prefixes source failure _ floatCheck evaluate
    (default_sound source failure environment evaluate sound _) typed actual valid subject within⟩

end Yulang.CommonPatternCorePrefixBridge
