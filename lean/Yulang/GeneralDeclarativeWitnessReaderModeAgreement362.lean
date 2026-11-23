import Yulang.GeneralDeclarativeWitnessModeScope362
import Yulang.GeneralDeclarativeWitnessScopedNativeWindows362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 71000
set_option maxHeartbeats 80000000
namespace Yulang.GeneralDeclarativeWitnessReaderModeAgreement362
open GeneralDeclarativeWitnessThreeNative362 (Run run ctor)
open GeneralDeclarativeWitnessScopedNativeWindows362 (Closed close)
open GeneralDeclarativeWitnessNativeOrder362 (low center high)
open GeneralDeclarativeWitnessInheritedEnvelope362 (interval)
open GeneralDeclarativeWitnessNativeInvariantCut362 (wrap)
open GeneralDeclarativeWitnessModeScope362 (one_authorized_table_cannot_change_comparison_rows)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralNominalCommonBridge (Assignment)

structure Certified {contra : Bool} {r : Run contra} (c : Closed r) where
  lower : Compiled c.emitted.environment table false (low r) (center r)
  upper : Compiled c.emitted.environment table false (center r) (high r)
  contextual : Compiled c.emitted.environment table false
    (wrap (interval (ctor contra) c.projected.a c.projected.b))
    (wrap (interval (ctor contra) c.projected.b c.projected.c))

/-- Read the actual later source environment independently. It must
endorse the one exact producer table at all sites, including beneath
the invariant context. Merely observing the same obligations is not a guard. -/
def agree {contra} {r : Run contra} (c : Closed r) : Option (Certified c) := do
  let a ← GeneralDeclarativeWitnessSparseIntervals357.compile c.emitted.environment table false (low r) (center r)
  let b ← GeneralDeclarativeWitnessSparseIntervals357.compile c.emitted.environment table false (center r) (high r)
  let inherited ← GeneralDeclarativeWitnessSparseIntervals357.compile c.emitted.environment table false
    (wrap (interval (ctor contra) c.projected.a c.projected.b))
    (wrap (interval (ctor contra) c.projected.b c.projected.c))
  pure ⟨a,b,inherited⟩

theorem consumer_real_source_endorses_inherited_table (contra : Bool) :
    ((run contra).bind fun r => (close r).map fun c => (agree c).isSome).getD false = true := by
  cases contra <;> decide +kernel

theorem one_table_same_rows_in_actual_consumer {contra} {r : Run contra} {c : Closed r}
    (audited : Certified c) :
    audited.lower.rows = c.ordering.left.rows ∧
    audited.upper.rows = c.ordering.right.rows ∧
    audited.contextual.rows = c.projected.ordered.rows :=
  ⟨one_authorized_table_cannot_change_comparison_rows c.ordering.left audited.lower,
    one_authorized_table_cannot_change_comparison_rows c.ordering.right audited.upper,
    one_authorized_table_cannot_change_comparison_rows c.projected.ordered audited.contextual⟩

theorem same_model_matches_every_verified_reader_row {contra} {r : Run contra} {c : Closed r}
    (start : run contra = some r) (audited : Certified c) (m : Assignment) (v : NativeViews)
    (fit : Fits c.received.world m v) :
    (∀ a ∈ audited.lower.rows,a.Holds CommonNominalFullCarrier.model m) ∧
    (∀ a ∈ audited.upper.rows,a.Holds CommonNominalFullCarrier.model m) ∧
    (∀ a ∈ audited.contextual.rows,a.Holds CommonNominalFullCarrier.model m) := by
  have upstream :=
    (GeneralDeclarativeWitnessNonpointReceiver362.returned_body_retains_prior_fit c.received m v fit).2
  have direct := GeneralDeclarativeWitnessNativeOrder362.release_and_order_in_every_fit start c.ordered m v upstream
  have envelope := GeneralDeclarativeWitnessInheritedEnvelope362.overlaps_at_the_separately_authored_center start c.chosen m v upstream
  have exactOne {e mode a b}
      (compiled : Compiled e table mode a b)
      (first : CommonRecursiveNominalIntervals.ContextWellFormed table mode a)
      (last : CommonRecursiveNominalIntervals.ContextWellFormed table mode b)
      (valid : ContextDerives table m mode a b) :
      ∀ row ∈ compiled.rows,row.Holds CommonNominalFullCarrier.model m := by
    have h := (GeneralDeclarativeWitnessFullIntervals357.compiled_full_exact table m mode a b).mpr ⟨first,last,valid⟩
    rw [compiled.exact,CommonRecursiveNominalIntervals.result_some] at h
    exact h
  exact ⟨exactOne audited.lower direct.1.1 direct.1.2.1 direct.2.1,
    exactOne audited.upper direct.1.2.1 direct.1.2.2 direct.2.2.1,
    exactOne audited.contextual envelope.2.2.2.1 envelope.2.2.2.2.1 envelope.2.2.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessReaderModeAgreement362
