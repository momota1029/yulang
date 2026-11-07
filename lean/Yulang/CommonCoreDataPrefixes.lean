import Yulang.CommonCoreDataEvaluation
import Yulang.CommonPatternCorePrefixBridge

/-! All finite event prefixes of the actual indexed Core data evaluator.
Pending observations are exactly prefixes of its real trace; a completed
observation retains the whole trace and exact result. Unsupported errors
remain errors. Safety below requires the finite source gate and derives
successful evaluation from independent constructor typing. -/

namespace Yulang.CommonCoreDataPrefixes

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp)
open CommonPatternFinitePrefixes (Computation Observation Safe)
open CommonCoreDataEvaluation (Supported EnvironmentHolds eval)
open CommonPatternTyping (valueAt bindingTypes)
open CommonPatternSourceScope (corePrefix)
open CommonPatternEnvironment (NamedTypes)
open EvaluationTrace (Logged)

def ofLogged (computation : Logged (CaseEvaluation.Event E) R A) : Computation E R A := fun observed =>
  (observed.result = none ∧ observed.trace.IsPrefix computation.trace) ∨
    observed = ⟨computation.trace, some computation.result⟩

theorem pending_exact (computation : Logged (CaseEvaluation.Event E) R A) (trace : List (CaseEvaluation.Event E)) :
    ofLogged computation ⟨trace, none⟩ ↔ trace.IsPrefix computation.trace := by
  simp [ofLogged]

theorem completed_exact (computation : Logged (CaseEvaluation.Event E) R A)
    (trace : List (CaseEvaluation.Event E)) (result : Except R A) :
    ofLogged computation ⟨trace, some result⟩ ↔ trace = computation.trace ∧ result = computation.result := by
  simp [ofLogged, Observation.mk.injEq]

def evaluate (actual : CaseValues.Bindings Empty) (code : Required.Term) :
    Computation Required.Term CommonCoreDataEvaluation.Error CommonData.Value := ofLogged (eval actual code)

theorem prefix_environment (types : NamedTypes) (actual : CaseValues.Bindings Empty)
    (valid : CaseValues.BindingsHold (bindingTypes types) actual) : EnvironmentHolds (corePrefix types) actual := by
  induction types generalizing actual with
  | nil =>
      cases valid
      intro index result typed
      rcases typed with ⟨binding, found, _⟩
      simp [corePrefix] at found
  | cons binding rest ih =>
      rcases binding with ⟨name, type⟩
      cases valid with
      | cons head tail =>
          intro index result typed
          cases index with
          | zero =>
              rcases typed with ⟨binding, found, typed⟩
              have same : binding = .mono (Comp.pure Common.model type) := by
                simpa [corePrefix] using found.symm
              subst binding
              exact ⟨name, _, rfl, CommonPatternLookup.typing_change_result head result
                ((CommonSyntax.mono_iff _ _).mp typed).1⟩
          | succ index =>
              obtain ⟨label, value, found, safe⟩ := ih _ tail index result
                (by simpa [corePrefix, CommonSyntax.Lookup] using typed)
              exact ⟨label, value, found, safe⟩

theorem pure_trace (trace : List (CaseEvaluation.Event E)) :
    CommonCaseEffectPaths.traceRow (fun _ => Common.rowEmpty) trace = Common.rowEmpty := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp only [CommonCaseEffectPaths.traceRow, CommonCaseEffectPaths.eventRow, ih]
      all_goals funext occurrence; simp only [Common.rowJoin, Common.rowEmpty, or_self]

/-- Every actual finite event prefix is safe. The interpreter is fixed,
failure rows are arbitrary, and successful completion is derived internally.
No abstract EvaluationSound contract occurs in this statement. -/
theorem typing_prefixes (within : Supported code)
    (environment : List (CommonSyntax.Binding Common.model)) (actual : CaseValues.Bindings Empty)
    (result : Comp Common.model) (valid : EnvironmentHolds environment actual)
    (typed : CommonSyntax.Typing Common.model environment code result)
    (failure : CommonCoreDataEvaluation.Error → Common.Row) :
    Safe (fun _ => Common.rowEmpty) failure (evaluate actual code) (valueAt result.1) result.2 := by
  obtain ⟨value, evaluated, safe⟩ := CommonCoreDataEvaluation.typing_evaluates within environment actual result valid typed
  have valueTyped : valueAt result.1 value :=
    CommonPatternLookup.typing_change_result safe _ (Common.subtype_refl _)
  intro observed present
  rcases present with ⟨pending, _⟩ | rfl
  · constructor
    · simp only [CommonPatternFinitePrefixes.observationRow, pure_trace,
        pending, CommonPatternFinitePrefixes.resultRow]
      intro occurrence impossible
      exact impossible.elim False.elim False.elim
    · intro returned impossible
      rw [pending] at impossible
      cases impossible
  · constructor
    · simp only [CommonPatternFinitePrefixes.observationRow, pure_trace,
        evaluated, CommonPatternFinitePrefixes.resultRow]
      intro occurrence impossible
      exact impossible.elim False.elim False.elim
    · intro returned same
      simp only [evaluated, Option.some.injEq, Except.ok.injEq] at same
      subst returned
      exact valueTyped

theorem binding_prefixes (types : NamedTypes) (actual : CaseValues.Bindings Empty)
    (valid : CaseValues.BindingsHold (bindingTypes types) actual)
    (code : Required.Term) (within : Supported code) (result : Comp Common.model)
    (typed : CommonSyntax.Typing Common.model (corePrefix types) code result)
    (failure : CommonCoreDataEvaluation.Error → Common.Row) :
    Safe (fun _ => Common.rowEmpty) failure (evaluate actual code) (valueAt result.1) result.2 :=
  typing_prefixes within _ actual result (prefix_environment types actual valid) typed failure

end Yulang.CommonCoreDataPrefixes
