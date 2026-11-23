import Yulang.GeneralDeclarativeWitnessNativeInvariantCut362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 68000
set_option maxHeartbeats 70000000
namespace Yulang.GeneralDeclarativeWitnessNativeWindowWitness362
open GeneralDeclarativeWitnessThreeNative362 (Run run)
open GeneralDeclarativeWitnessNativeInvariantCut362 (Contrast contrast checked)
open GeneralDeclarativeWitnessNativeOrder362 (low center high)
open GeneralDeclarativeWitnessNativeThreeModel362 (model snapshot exact_snapshot model_transfer fits_after)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)

theorem inhabited_exact_comparison (contra : Bool) :
    ∃ (r : Run contra) (x : Contrast r),
      run contra = some r ∧ contrast r = some x ∧
      ∀ upper : Bool, Fits r.final (model contra upper) (interpreted r.final.board (model contra upper)) := by
  have started := GeneralDeclarativeWitnessNativeInvariantCut362.inherited_context_demands_reverse_bound contra
  have state := exact_snapshot contra
  cases made : run contra with
  | none => rw [made] at started; cases started
  | some r =>
    rw [made] at started state
    change ((contrast r).map checked).getD false = true at started
    cases cmp : contrast r with
    | none => rw [cmp] at started; cases started
    | some x =>
      exact ⟨r,x,rfl,cmp,fun upper =>
        ⟨(model_transfer r state _).mpr (fits_after contra upper),fun _ => rfl⟩⟩

theorem actual_source_window_inhabited_and_ordered (contra : Bool) :
    ∃ (r : Run contra) (x : Contrast r),
      run contra = some r ∧ contrast r = some x ∧
      ∀ upper : Bool,
        let m := model contra upper
        Fits r.final m (interpreted r.final.board m) ∧
        ContextDerives table m false (low r) (center r) ∧ ContextDerives table m false (center r) (high r) := by
  obtain ⟨r,x,candidate,ran,fit⟩ := inhabited_exact_comparison contra
  refine ⟨r,x,candidate,ran,?_⟩
  intro u
  have relation := GeneralDeclarativeWitnessNativeOrder362.release_and_order_in_every_fit candidate x.chainRan _ _ (fit u)
  exact ⟨fit u,relation.2.1,relation.2.2.1⟩

theorem same_snapshot_does_not_choose_center {contra} {r : Run contra} {x : Contrast r}
    (candidate : run contra = some r)
    (uFit : ∀ a,Fits r.final (model contra a) (interpreted r.final.board (model contra a))) :
    interpreted r.final.board (model contra false) 202 ≠
      interpreted r.final.board (model contra true) 202 := by
  have a := GeneralDeclarativeWitnessOrderedNativeRelease362.source_code_in_every_fit
    candidate x.native.releases _ _ (uFit false)
  have b := GeneralDeclarativeWitnessOrderedNativeRelease362.source_code_in_every_fit
    candidate x.native.releases _ _ (uFit true)
  intro alike
  rw [a.2.1,b.2.1] at alike
  have inner := (GeneralDeclarativeWitnessNativeValue360.Value.unary.inj (Option.some.inj alike)).2
  have vals := GeneralDeclarativeWitnessNativeValue360.Value.leaf.inj inner
  have same : GeneralDeclarativeWitnessRecordWidthFixture359.lowTy = GeneralDeclarativeWitnessRecordWidthFixture359.highTy := vals
  apply GeneralDeclarativeWitnessNativeInvariantCut362.proper_record_interval
  rw [← same]
  exact CommonNominalFullCarrier.subtype_refl _

end Yulang.GeneralDeclarativeWitnessNativeWindowWitness362
