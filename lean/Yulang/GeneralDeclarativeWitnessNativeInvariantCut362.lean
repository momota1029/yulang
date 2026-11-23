import Yulang.GeneralDeclarativeWitnessNativeOrder362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 68000
set_option maxHeartbeats 70000000
namespace Yulang.GeneralDeclarativeWitnessNativeInvariantCut362
open GeneralDeclarativeWitnessThreeNative362 (Run run)
open GeneralDeclarativeWitnessNativeOrder362 (Chain chain low high atom)
open GeneralDeclarativeWitnessNativeThreeModel362 (model snapshot exact_snapshot model_transfer fits_after)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open GeneralDeclarativeWitnessRecordWidthFixture359 (lowTy highTy lowRest highRest)
open CommonRecursiveNominalIntervals (Endpoint Bounds ContextWellFormed result_some)
open CommonNominalFullCarrier (Subtype)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom)

def wrap (t : Endpoint Nat) : Endpoint Nat := .nominal 55 [.inl (.point t)]

structure Contrast {contra : Bool} (r : Run contra) where
  native : Chain r
  chainRan : chain r = some native
  reversed : Compiled r.environment table false (high r) (low r)
  inherited : Compiled r.environment table true (low r) (high r)
  wrapped : Compiled r.environment table false (wrap (low r)) (wrap (high r))

def contrast {contra} (r : Run contra) : Option (Contrast r) :=
  match ran : chain r with
  | none => none
  | some ordered => do
    let back ← GeneralDeclarativeWitnessSparseIntervals357.compile r.environment table false (high r) (low r)
    let inherited ← GeneralDeclarativeWitnessSparseIntervals357.compile r.environment table true (low r) (high r)
    let wrapped ← GeneralDeclarativeWitnessSparseIntervals357.compile r.environment table false (wrap (low r)) (wrap (high r))
    pure ⟨ordered,ran,back,inherited,wrapped⟩

def checked {contra r} (p : @Contrast contra r) : Bool :=
  decide (atom 62 60 ∈ p.reversed.rows ∧ atom 62 60 ∈ p.inherited.rows ∧ atom 62 60 ∈ p.wrapped.rows)

theorem inherited_context_demands_reverse_bound (contra : Bool) :
    ((run contra).bind fun r => (contrast r).map checked).getD false = true := by cases contra <;> decide +kernel

theorem proper_record_interval : ¬Subtype highTy lowTy := by
  intro wrong
  apply GeneralDeclarativeWitnessRecordWindowFixture358.strict_original_payload_bounds
  exact GeneralNominalStructuralProjectionLaws.record_payload 7 _ _ _ _ wrong

theorem bad_in_this_fit (contra pickUpper : Bool) :
    ¬(atom 62 60).Holds CommonNominalFullCarrier.model (model contra pickUpper) := by
  exact proper_record_interval

theorem emitted_bad_row_obstructs_derivation {e context lo hi} (run : Compiled e table context lo hi)
    (m : Assignment) {bad : Atom Nat} (requested : bad ∈ run.rows)
    (fails : ¬bad.Holds CommonNominalFullCarrier.model m) :
    ¬(ContextWellFormed table context lo ∧ ContextWellFormed table context hi ∧ ContextDerives table m context lo hi) := by
  intro possible
  have sat := (compiled_full_exact table m context lo hi).mpr possible
  rw [run.exact,result_some] at sat
  exact fails (sat _ requested)

theorem same_model_contrasts_directions {contra} {r : Run contra} {x : Contrast r}
    (emitted : run contra = some r) (ran : contrast r = some x) (u : Bool) :
    ¬(ContextWellFormed table false (high r) ∧ ContextWellFormed table false (low r) ∧
      ContextDerives table (model contra u) false (high r) (low r)) ∧
    ¬(ContextWellFormed table true (low r) ∧ ContextWellFormed table true (high r) ∧
      ContextDerives table (model contra u) true (low r) (high r)) ∧
    ¬(ContextWellFormed table false (wrap (low r)) ∧ ContextWellFormed table false (wrap (high r)) ∧
      ContextDerives table (model contra u) false (wrap (low r)) (wrap (high r))) := by
  have h := inherited_context_demands_reverse_bound contra
  rw [emitted] at h
  change ((contrast r).map checked).getD false = true at h
  rw [ran] at h
  have needs := of_decide_eq_true (show checked x = true from h)
  exact ⟨emitted_bad_row_obstructs_derivation x.reversed _ needs.1 (bad_in_this_fit contra u),
    emitted_bad_row_obstructs_derivation x.inherited _ needs.2.1 (bad_in_this_fit contra u),
    emitted_bad_row_obstructs_derivation x.wrapped _ needs.2.2 (bad_in_this_fit contra u)⟩

end Yulang.GeneralDeclarativeWitnessNativeInvariantCut362
