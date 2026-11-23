import Yulang.GeneralDeclarativeWitnessNativePipeline360
import Yulang.GeneralDeclarativeWitnessNominalPolarity359

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 56000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralDeclarativeWitnessNativeModel360
open GeneralDeclarativeWitnessNativePipeline360 (Run run confirm gate authority valueCode)
open GeneralDeclarativeWitnessNativeValue360 (Value Code)
open GeneralDeclarativeWitnessNativeInstall360
  (World Fits NativeViews interpreted fit_after_install actual_installation)
open GeneralDeclarativeWitnessNominalRecordFixture359
  (current common_source_model genuine)
open GeneralDeclarativeWitnessRecordWidthFixture359 (lowTy highTy endpoints_ordered)
open GeneralDeclarativeWitnessNominalPolarity359 (high_is_not_subtype_of_low)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom)

def actualAtoms : List (Atom Nat) := [(61,61),(61,61),(106,60),(60,106),
  (107,62),(62,107),(106,61),(61,107)].map fun pair => .tyLe (.var pair.1) (.var pair.2)

def afterWhere : State :=
  ⟨⟨actualAtoms,current.normal.intervals⟩,current.equations ++ [⟨105,.variable 61⟩]⟩

def checks {negative} (r : Run negative) : Bool :=
  decide (r.prepared.stage.normal.ordinary = afterWhere.normal.ordinary ∧
    r.prepared.stage.normal.intervals = afterWhere.normal.intervals ∧
    r.prepared.stage.equations = afterWhere.equations)

theorem running_real_stage (negative : Bool) : ((run negative).map checks).getD false = true := by
  cases negative <;> decide +kernel

theorem exact_stage {negative} {r : Run negative} (ran : run negative = some r) :
    r.prepared.stage = afterWhere := by
  have pass := running_real_stage negative
  rw [ran] at pass
  have reflects : checks r = true := pass
  have tested := of_decide_eq_true reflects
  have a := tested.1
  have b := tested.2.1
  have c := tested.2.2
  generalize r.prepared.stage = actual at a b c ⊢
  cases actual with
  | mk normal equations =>
    cases normal with
    | mk ordinary intervals =>
      dsimp at a b c
      rw [a,b,c]

def model (upper : Bool) (base : Inference.Base) : Assignment := fun n =>
  match n with
  | 101 => (.base base,Common.rowEmpty)
  | 105 => genuine upper false 61
  | 106 => genuine upper false 60
  | 107 => genuine upper false 62
  | n => genuine upper false n

private theorem unmentioned {n : Nat} (h : n ∈ stateNames current) :
    n ≠ 101 ∧ n ≠ 105 ∧ n ≠ 106 ∧ n ≠ 107 := by
  have t0 : 101 ∉ stateNames current := by decide +kernel
  have t1 : 105 ∉ stateNames current := by decide +kernel
  have t2 : 106 ∉ stateNames current := by decide +kernel
  have t3 : 107 ∉ stateNames current := by decide +kernel
  exact ⟨fun e => t0 (e ▸ h),fun e => t1 (e ▸ h),fun e => t2 (e ▸ h),fun e => t3 (e ▸ h)⟩

theorem fitting_ordinary_nonpoint (upper : Bool) (base : Inference.Base) : Models afterWhere (model upper base) := by
  have unchanged (n : Nat) (atState : n ∈ stateNames current) :
      genuine upper false n = model upper base n := by
    have diff := unmentioned atState
    simp [model,diff.1,diff.2.1,diff.2.2.1,diff.2.2.2]
  have original := (preserves_models current unchanged).mp (common_source_model upper false)
  refine ⟨⟨?_,original.1.2⟩,?_⟩
  · intro atom present
    simp only [afterWhere,actualAtoms,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases upper <;> first | exact subtype_refl _ | exact endpoints_ordered
  · intro eq appears
    have either : eq ∈ current.equations ∨ eq = (⟨105,.variable 61⟩ : Equation) := by
      simpa only [afterWhere,List.mem_append,List.mem_singleton] using appears
    rcases either with old|rfl
    · exact original.2 _ old
    · exact eqv_refl _

theorem checked_target_in_every_native_model {negative} {r : Run negative}
    (ran : run negative = some r) (m : Assignment) (views : NativeViews) (fit : Fits r.current m views) :
    views 101 = some ((valueCode negative).eval m) ∧
    Models current m ∧
    ∀ row ∈ r.prepared.whereRows,GeneralDeclarativeEntailment320.Holds m row := by
  have yes := GeneralDeclarativeWitnessNativePipeline360.actual_compiler_write_and_child negative
  rw [ran] at yes
  have exact : confirm r = true := yes
  have joined := GeneralDeclarativeWitnessProblem349.splitAnd
    (GeneralDeclarativeWitnessProblem349.splitAnd exact).1
  have codeEq : r.output.code = valueCode negative := congrArg GeneralDeclarativeWitnessNativeValue360.Write.code (of_decide_eq_true (GeneralDeclarativeWitnessProblem349.splitAnd joined.1).2)
  have discovered := actual_installation r.prepared r.output r.installed m views fit
  have seen := discovered.1
  change views 101 = some (r.output.code.eval m) at seen
  rw [codeEq] at seen
  exact ⟨seen,discovered.2⟩

theorem final_inhabited {negative} {r : Run negative}
    (ran : run negative = some r) (upper : Bool) (base : Inference.Base) :
    Fits r.current (model upper base) (interpreted r.current.board (model upper base)) := by
  apply fit_after_install r.prepared r.output r.installed
  rw [exact_stage ran]
  exact fitting_ordinary_nonpoint upper base

theorem native_does_not_guess_ordinary_target {negative} {r : Run negative}
    (ran : run negative = some r) (upper : Bool) :
    let ma := model upper .int
    let mb := model upper .bool
    Fits r.current ma (interpreted r.current.board ma) ∧
    Fits r.current mb (interpreted r.current.board mb) ∧
    interpreted r.current.board ma 101 = interpreted r.current.board mb 101 ∧
    (ma 101).1 ≠ (mb 101).1 := by
  dsimp
  have left := final_inhabited ran upper .int
  have right := final_inhabited ran upper .bool
  have lv := (checked_target_in_every_native_model ran _ _ left).1
  have rv := (checked_target_in_every_native_model ran _ _ right).1
  refine ⟨left,right,lv.trans ?_,?_⟩
  · rw [rv]
    rfl
  · intro contrary
    change (CommonNominalSyntax.Layer.base .int : CommonNominalFullCarrier.Ty) = .base .bool at contrary
    cases contrary

theorem native_view_tracks_actual_center {negative} {r : Run negative}
    (ran : run negative = some r) :
    let ma := model false .int
    let mb := model true .int
    Fits r.current ma (interpreted r.current.board ma) ∧
    Fits r.current mb (interpreted r.current.board mb) ∧
    interpreted r.current.board ma 101 ≠ interpreted r.current.board mb 101 := by
  dsimp
  have left := final_inhabited ran false .int
  have right := final_inhabited ran true .int
  refine ⟨left,right,?_⟩
  rw [(checked_target_in_every_native_model ran _ _ left).1,
    (checked_target_in_every_native_model ran _ _ right).1]
  intro same
  have outer := Value.unary.inj (Option.some.inj same)
  have inner := Value.unary.inj outer.2
  have payload : lowTy = highTy := Value.leaf.inj inner.2
  exact high_is_not_subtype_of_low (payload ▸ subtype_refl lowTy)

end Yulang.GeneralDeclarativeWitnessNativeModel360
