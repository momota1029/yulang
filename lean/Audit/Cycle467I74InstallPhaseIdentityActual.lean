import Yulang.GeneralDeclarativeI65I74InstallPhaseIdentity467
import Yulang.GeneralDeclarativeWitnessNativeModel360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralDeclarativeI65.I72.InstallPhaseIdentity467.Actual
open Yulang.GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open GeneralDeclarativeWitnessNativePipeline360
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessNativeModel360 (model final_inhabited)
open GeneralDeclarativeWitnessNativeInstall360 (World)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

private def actualRun : Run false := (run false).get (by decide +kernel)

private theorem run_actual : run false = some actualRun := by
  have yes : (run false).isSome = true := by decide +kernel
  cases h : run false with
  | none => simp [h] at yes
  | some actual =>
    unfold actualRun
    simp [h]

private def literal : Origin := originalOfWrite actualRun.output.write

private def good : GeneralDeclarativeI65.State :=
  ⟨⟨actualRun.env,actualRun.current.ordinary,[]⟩,table,[literal],[⟨107,101,[5]⟩]⟩

private def repeated : Equation := ⟨999,.variable 999⟩

private def differentOrdinary : GeneralDeclarativeHead320.State :=
  { actualRun.current.ordinary with equations := actualRun.current.ordinary.equations ++ [repeated] }

private def other : GeneralDeclarativeI65.State :=
  { good with current := { good.current with ordinary := differentOrdinary } }

private def givenBoardOnly : World := ⟨other.current.ordinary,actualRun.current.board⟩

private def sameModel : Model := ⟨model false .int,fun _ => none,
  fun n => if n = literal.slot then some literal.endpoint else none⟩

theorem actual_install_phase_not_identified_by_all_ordinary_models :
    good.current.ordinary ≠ other.current.ordinary ∧
      ∀ m, Models good.current.ordinary m ↔ Models other.current.ordinary m := by
  constructor
  · intro eq
    have len := congrArg (fun s : GeneralDeclarativeHead320.State => s.equations.length) eq
    change actualRun.current.ordinary.equations.length =
      (actualRun.current.ordinary.equations ++ [repeated]).length at len
    simp at len
  · intro m; constructor
    · intro prior
      refine ⟨prior.1,?_⟩
      intro row mem
      change row ∈ actualRun.current.ordinary.equations ++ [repeated] at mem
      cases List.mem_append.mp mem with
      | inl priorRow => exact prior.2 _ priorRow
      | inr inserted =>
        rcases List.mem_singleton.mp inserted with rfl
        exact eqv_refl _
    · intro post
      exact ⟨post.1,fun row mem => post.2 row (List.mem_append.mpr (Or.inl mem))⟩

theorem both_actual_inputs_have_one_concrete_same_core_fit :
    GeneralDeclarativeI65.Fits good sameModel ∧ GeneralDeclarativeI65.Fits other sameModel := by
  have truePhase := (final_inhabited run_actual false .int).1
  have here (s : GeneralDeclarativeI65.State) (ordinary : Models s.current.ordinary sameModel.assignment)
      (empty : s.current.visible = []) (source : s.origins = [literal]) :
      GeneralDeclarativeI65.Fits s sameModel := by
    refine ⟨⟨ordinary,?_⟩,?_⟩
    · intro row membership
      simp [empty] at membership
    · intro origin member
      rw [source] at member
      rcases List.mem_singleton.mp member with rfl
      simp [sameModel]
  exact ⟨here good truePhase rfl rfl,
    here other ((actual_install_phase_not_identified_by_all_ordinary_models.2 _).mp truePhase) rfl rfl⟩

private theorem originRouted : OriginRoute other literal 107 := by
  apply OriginRoute.authored
  exact List.mem_cons_self

theorem legacy_original_is_authorized_even_when_actual_install_phase_differs :
    Nonempty (AuthorizedEndpoint other (fun o => Nonempty (CurrentReleasedOrigin other o)) 107) := by
  have realGrant : actualRun.output.write.address ∈ authority.grants := by decide +kernel
  exact original_from_installed_and_retained_author actualRun.output actualRun.installed
    (later := []) (fun _ gone => False.elim (List.not_mem_nil gone)) authority realGrant List.mem_cons_self originRouted

theorem exact_issued_board_read_is_not_an_actual_compiler_phase_read :
    checkProducedOrigin (s := good) actualRun.prepared gate authority (wire false) 3 107 0 = true ∧
    checkPhaseOrigin (s := other) ⟨givenBoardOnly,rfl,authority⟩ actualRun.output.write 107 0 = true ∧
    ∀ w version logical ordinal,
        checkProducedOrigin (s := other) actualRun.prepared gate authority w version logical ordinal = false := by
  have differs : actualRun.prepared.stage ≠ other.current.ordinary :=
    fun eq => actual_install_phase_not_identified_by_all_ordinary_models.1
      ((GeneralDeclarativeWitnessNativeInstall360.no_ordinary_override
        actualRun.prepared actualRun.output actualRun.installed).trans eq)
  exact ⟨by decide +kernel,by decide +kernel,
    every_data_wire_declines_a_different_actual_compiler_phase (s := other) actualRun.prepared differs gate authority⟩

#print axioms actual_install_phase_not_identified_by_all_ordinary_models
#print axioms both_actual_inputs_have_one_concrete_same_core_fit
#print axioms legacy_original_is_authorized_even_when_actual_install_phase_differs
#print axioms exact_issued_board_read_is_not_an_actual_compiler_phase_read

end Yulang.GeneralDeclarativeI65.I72.InstallPhaseIdentity467.Actual
