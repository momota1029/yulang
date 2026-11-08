import Yulang.CommonCaseCoreDataGate

/-! A real finite Core record family with its source evaluator supplied.
The finite gate covers all actual leaf code, so every unrestricted returned
parameter uses proved source-prefix safety. No EvaluationSound, successful
default, selected arm or residual model is a caller premise.

This is the pure finite Core data fragment and the stated record-coverage /
environment / row-upper-bound factor. Full source presence, principal case
rows, functions, effects and nested cases remain separate. -/

namespace Yulang.CommonCaseCoreDataPrefixSolved

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonCaseCoreBoundedGeneration (Arm runtimeArm)
open CommonCaseRecordReadout (Specification shapes)
open CommonCaseCoreDataGate (SourceSupported DefaultTyped GuardTyped BodyTyped)
open CommonCoreDataPrefixes (evaluate binding_prefixes)
open CommonCoreDataEvaluation (Error)
open CommonPatternFinitePrefixes (Computation Safe ops logic)
open CommonPatternCorePrefixBridge (guardOf)
open CommonPatternGenerationProvenance (SafeFormula)
open CommonPatternTyping (valueAt bindingTypes)
open CommonCasePrefixCoverage (SuccessfulResult)

def Premises (specification : Specification) (subject : Required.Term) (arms : List Arm)
    (input target : Common.Ty) (cap : Common.Row) : Prop :=
  CommonCaseCoreRecordPrefixSolved.Premises [] Empty.elim specification subject arms input target cap ∧
    SourceSupported subject arms

def principal (specification : Specification) (subject : Required.Term) (arms : List Arm) : Formula (Fin 3) :=
  if CommonCaseCoreDataGate.check subject arms then
    CommonCaseCoreRecordPrefixSolved.principal Empty.elim specification subject arms
  else .bot

theorem principal_exact (specification : Specification) (subject : Required.Term) (arms : List Arm)
    (assignment : Fin 3 → Comp Common.model) :
    (principal specification subject arms).Holds Common.model assignment ↔
      Premises specification subject arms (assignment 0).1 (assignment 1).1 (assignment 2).2 := by
  cases checked : CommonCaseCoreDataGate.check subject arms with
  | false =>
      have outside : ¬ SourceSupported subject arms := by
        intro within
        have accepted := (CommonCaseCoreDataGate.check_exact subject arms).mpr within
        rw [checked] at accepted
        cases accepted
      simp [principal, checked, Formula.Holds, Premises, outside]
  | true =>
      have within := (CommonCaseCoreDataGate.check_exact subject arms).mp checked
      simp only [principal, checked, ↓reduceIte,
        CommonCaseCoreRecordPrefixSolved.principal_exact, Premises, within, and_true]

theorem principal_safe (specification : Specification) (subject : Required.Term) (arms : List Arm) :
    SafeFormula (principal specification subject arms) := by
  unfold principal
  split
  · exact CommonCaseCoreRecordPrefixSolved.principal_safe Empty.elim specification subject arms
  · exact .bot

def solvePremises (specification : Specification) (subject : Required.Term) (arms : List Arm) :
    List (CommonPatternFiniteSchemes.Scheme 3) := CommonPatternFiniteSchemes.infer (principal specification subject arms)

theorem all_parameter_premises (specification : Specification) (subject : Required.Term) (arms : List Arm)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (member : scheme ∈ solvePremises specification subject arms)
    (parameters : scheme.Parameters) :
    Premises specification subject arms (scheme.instantiate parameters 0).1
      (scheme.instantiate parameters 1).1 (scheme.instantiate parameters 2).2 :=
  (principal_exact specification subject arms _).mp
    (CommonPatternFiniteSchemes.all_parameter_holds _ scheme member parameters)

theorem premises_instances_exact (specification : Specification) (subject : Required.Term) (arms : List Arm)
    (assignment : Fin 3 → Comp Common.model) :
    Premises specification subject arms (assignment 0).1 (assignment 1).1 (assignment 2).2 ↔
      ∃ scheme ∈ solvePremises specification subject arms, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment :=
  (principal_exact specification subject arms assignment).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe specification subject arms) assignment)

theorem no_premises_exact (specification : Specification) (subject : Required.Term) (arms : List Arm) :
    solvePremises specification subject arms = [] ↔
      ¬ ∃ assignment : Fin 3 → Comp Common.model,
        Premises specification subject arms (assignment 0).1 (assignment 1).1 (assignment 2).2 := by
  rw [solvePremises, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe specification subject arms)]
  exact not_congr (exists_congr (principal_exact specification subject arms))

def invalidBool : Computation Required.Term Error Bool :=
  CommonCoreDataPrefixes.ofLogged (EvaluationTrace.Logged.ofResult (.error (.data .expectedBool)))

def guardEval := guardOf evaluate invalidBool

def run (subject : Required.Term) (arms : List Arm) : Computation Required.Term Error (Option CommonData.Value) :=
  CommonCaseComputations.eval (ops Required.Term Error) (CommonCaseFinitePrefixes.visits Required.Term Error)
    Empty.elim evaluate [] guardEval (fun code actual => evaluate actual code)
    (evaluate [] subject) (arms.map runtimeArm)

theorem defaults_sound (failure : Error → Common.Row) (cap : Common.Row) :
    CommonPatternComputationSafety.DefaultSound (logic (fun _ => Common.rowEmpty) failure)
      cap (DefaultTyped cap) evaluate := by
  intro types code type typed actual valid
  obtain ⟨⟨row, typed, below⟩, within⟩ := typed
  apply CommonCaseFinitePrefixes.row_mono (fun _ => Common.rowEmpty) failure _ _ row cap _ below
  exact binding_prefixes types actual valid code within (type, row)
    (by simpa only [List.append_nil] using typed) failure

theorem guards_sound (failure : Error → Common.Row) (cap : Common.Row) :
    CommonCaseComputationSafety.GuardSound (logic (fun _ => Common.rowEmpty) failure)
      cap (GuardTyped cap) guardEval := by
  intro code types typed actual valid
  have first := binding_prefixes types actual valid code typed.2 (.base .bool, cap)
    (by simpa only [CommonCaseCoreBoundedGeneration.GuardTyped, List.append_nil] using typed.1) failure
  apply CommonPatternFinitePrefixes.bind_safe (fun _ => Common.rowEmpty) failure _ _
    (valueAt (.base .bool)) _ cap first
  intro value valueTyped
  obtain ⟨boolean, _, decoded⟩ := CommonPatternCorePrefixBridge.boolean_readout value valueTyped
  simp only [decoded]
  exact CommonPatternFinitePrefixes.ret_safe (fun _ => Common.rowEmpty) failure boolean _ cap True.intro

theorem bodies_sound (failure : Error → Common.Row) (cap : Common.Row) :
    CommonCaseComputationSafety.BodySound (logic (fun _ => Common.rowEmpty) failure)
      cap (BodyTyped cap) (fun code actual => evaluate actual code) := by
  intro code types target typed actual valid
  exact binding_prefixes types actual valid code typed.2 (target, cap)
    (by simpa only [CommonCaseCoreBoundedGeneration.BodyTyped, List.append_nil] using typed.1) failure

/-- All actual prefixes of the original ordered case, with the fixed source
evaluator and Bool readout. Coverage and record input shape are obtained from
the same premises; successful callbacks are derived, not hypothesised. -/
theorem case_prefixes (specification : Specification) (subject : Required.Term) (arms : List Arm)
    (input target : Common.Ty) (cap : Common.Row)
    (premises : Premises specification subject arms input target cap) (failure : Error → Common.Row) :
    Safe (fun _ => Common.rowEmpty) failure (run subject arms) (SuccessfulResult target) cap := by
  have subjectSafe := binding_prefixes [] [] .nil subject premises.2.1 (input, cap) premises.1.1.1 failure
  apply CommonCasePrefixCoverage.safe_selected_result (fun _ => Common.rowEmpty) failure _ target cap
  · apply CommonCaseFinitePrefixes.eval_finite_prefixes (types := []) (fun _ => Common.rowEmpty) failure cap
      Empty.elim evaluate (defaults_sound failure cap) [] .nil guardEval (guards_sound failure cap)
      (fun code actual => evaluate actual code) (bodies_sound failure cap) _ subjectSafe
    intro arm member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact CommonCaseCoreDataGate.arm_typing original input target cap
      (premises.2.2 original originalMember) (premises.1.1.2 original originalMember)
  · apply CommonCasePrefixCoverage.eval_noMiss Empty.elim evaluate [] guardEval
      (fun code actual => evaluate actual code) (shapes specification) (arms.map runtimeArm)
      ((CommonCaseCoreRecordPrefixSolved.coverage_exact Empty.elim specification arms).mpr premises.1.2.2)
    rintro value ⟨trace, present⟩
    have typed := (subjectSafe ⟨trace, some (.ok value)⟩ present).2 value rfl
    exact CommonCaseRecordReadout.readout specification value (Comp.pure Common.model input) typed premises.1.2.1

/-- Every actual returned scheme and every unrestricted parameter uses the
proved evaluator, with source support checked inside the finite generator.
There is no EvaluationSound or post-solver admissibility premise. -/
theorem all_parameter_case_prefixes (specification : Specification) (subject : Required.Term) (arms : List Arm)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (member : scheme ∈ solvePremises specification subject arms)
    (parameters : scheme.Parameters) (failure : Error → Common.Row) :
    Safe (fun _ => Common.rowEmpty) failure (run subject arms)
      (SuccessfulResult (scheme.instantiate parameters 1).1) (scheme.instantiate parameters 2).2 :=
  case_prefixes specification subject arms _ _ _
    (all_parameter_premises specification subject arms scheme member parameters) failure

end Yulang.CommonCaseCoreDataPrefixSolved
