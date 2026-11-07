import Yulang.CommonCaseCoreDataPrefixSolved
import Yulang.CommonCasePrefixCompletion

/-! Successful completion of the fixed original Core data case evaluator.
The source gate and independent typing derive all leaf completions. The
unchanged finite traversal constructs a return, then the same record coverage
premise excludes a completed miss. General effectful code is not made total. -/

namespace Yulang.CommonCaseCoreDataCompletion

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp)
open CommonPatternPrefixNoMiss (Returns returns_bind returns_ret)
open CommonCasePrefixCompletion (Completes logic)
open CommonCaseCoreDataGate (DefaultTyped GuardTyped BodyTyped)
open CommonCaseCoreDataPrefixSolved (Premises run guardEval)
open CommonCaseCoreBoundedGeneration (Arm runtimeArm)
open CommonCoreDataEvaluation (Error Supported)
open CommonCoreDataPrefixes (evaluate)
open CommonPatternTyping (valueAt bindingTypes)
open CommonPatternEnvironment (NamedTypes)
open CommonPatternSourceScope (corePrefix)
open CaseValues (Bindings BindingsHold)

theorem source_completes (types : NamedTypes) (actual : Bindings Empty)
    (valid : BindingsHold (bindingTypes types) actual) (code : Required.Term)
    (within : Supported code) (result : Comp Common.model)
    (typed : CommonSyntax.Typing Common.model (corePrefix types) code result) :
    Completes (evaluate actual code) (valueAt result.1) := by
  obtain ⟨value, returned, safe⟩ := CommonCoreDataEvaluation.typing_evaluates within _ actual result
    (CommonCoreDataPrefixes.prefix_environment types actual valid) typed
  refine ⟨value, ⟨(CommonCoreDataEvaluation.eval actual code).trace, ?_⟩,
    CommonPatternLookup.typing_change_result safe _ (Common.subtype_refl _)⟩
  exact (CommonCoreDataPrefixes.completed_exact _ _ (.ok value)).mpr ⟨rfl, returned.symm⟩

theorem defaults_complete (cap : Common.Row) :
    CommonPatternComputationSafety.DefaultSound (logic Required.Term Error) Common.rowEmpty
      (DefaultTyped cap) evaluate := by
  intro types code type typed actual valid
  obtain ⟨⟨row, typed, _⟩, within⟩ := typed
  exact source_completes types actual valid code within (type, row)
    (by simpa only [List.append_nil] using typed)

theorem guards_complete (cap : Common.Row) :
    CommonCaseComputationSafety.GuardSound (logic Required.Term Error) Common.rowEmpty
      (GuardTyped cap) guardEval := by
  intro code types typed actual valid
  obtain ⟨value, returned, safe⟩ := source_completes types actual valid code typed.2 (.base .bool, cap)
    (by simpa only [CommonCaseCoreBoundedGeneration.GuardTyped, List.append_nil] using typed.1)
  obtain ⟨boolean, _, decoded⟩ := CommonPatternCorePrefixBridge.boolean_readout value safe
  refine ⟨boolean, (returns_bind _ _ boolean).mpr ⟨value, returned, ?_⟩, True.intro⟩
  simp only [decoded]
  exact (returns_ret boolean boolean).mpr rfl

theorem bodies_complete (cap : Common.Row) :
    CommonCaseComputationSafety.BodySound (logic Required.Term Error) Common.rowEmpty
      (BodyTyped cap) (fun code actual => evaluate actual code) := by
  intro code types target typed actual valid
  exact source_completes types actual valid code typed.2 (target, cap)
    (by simpa only [CommonCaseCoreBoundedGeneration.BodyTyped, List.append_nil] using typed.1)

/-- Every supported, independently typed original finite Core record case
has a completed successful trace with a selected typed value. Neither an
interpreter contract nor successful leaves nor a selected arm is assumed. -/
theorem case_returns (specification : CommonCaseRecordReadout.Specification)
    (subject : Required.Term) (arms : List Arm) (input target : Common.Ty) (cap : Common.Row)
    (premises : Premises specification subject arms input target cap) :
    ∃ value, Returns (run subject arms) (some value) ∧ valueAt target value := by
  have subjectComplete := source_completes [] [] .nil subject premises.2.1 (input, cap) premises.1.1.1
  have completed : Completes (run subject arms) (CommonCaseComputationSafety.ResultHolds target) := by
    apply CommonCasePrefixCompletion.eval_completes (types := []) Empty.elim evaluate
      (defaults_complete cap) [] .nil guardEval (guards_complete cap)
      (fun code actual => evaluate actual code) (bodies_complete cap) _ subjectComplete
    intro arm member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact CommonCaseCoreDataGate.arm_typing original input target cap
      (premises.2.2 original originalMember) (premises.1.1.2 original originalMember)
  obtain ⟨option, ⟨trace, present⟩, _⟩ := completed
  have selected := (CommonCaseCoreDataPrefixSolved.case_prefixes specification subject arms input target cap
    premises (fun _ => Common.rowEmpty) ⟨trace, some (.ok option)⟩ present).2 option rfl
  cases option with
  | none => exact False.elim selected
  | some value => exact ⟨value, ⟨trace, present⟩, selected⟩

/-- Every scheme actually returned by the unchanged finite solver and every
unrestricted parameter produce an actual completed successful observation,
with its typed selected result and row bound. Source support, leaf success,
coverage and input readout are all discharged inside this theorem. -/
theorem all_parameter_returns (specification : CommonCaseRecordReadout.Specification)
    (subject : Required.Term) (arms : List Arm) (scheme : CommonPatternFiniteSchemes.Scheme 3)
    (member : scheme ∈ CommonCaseCoreDataPrefixSolved.solvePremises specification subject arms)
    (parameters : scheme.Parameters) (failure : Error → Common.Row) :
    ∃ trace value,
      run subject arms ⟨trace, some (.ok (some value))⟩ ∧
        valueAt (scheme.instantiate parameters 1).1 value ∧
        Common.rowLe
          (CommonPatternFinitePrefixes.observationRow (fun _ => Common.rowEmpty) failure
            ⟨trace, some (.ok (some value))⟩)
          (scheme.instantiate parameters 2).2 := by
  obtain ⟨value, ⟨trace, present⟩, typed⟩ := case_returns specification subject arms _ _ _
    (CommonCaseCoreDataPrefixSolved.all_parameter_premises specification subject arms scheme member parameters)
  refine ⟨trace, value, present, typed, ?_⟩
  exact (CommonCaseCoreDataPrefixSolved.all_parameter_case_prefixes specification subject arms scheme member
    parameters failure ⟨trace, some (.ok (some value))⟩ present).1

end Yulang.CommonCaseCoreDataCompletion
