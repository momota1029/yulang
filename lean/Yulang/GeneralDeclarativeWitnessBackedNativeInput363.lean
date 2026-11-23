import Yulang.GeneralDeclarativeWitnessCrossOwnerModel362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 75000
set_option maxHeartbeats 90000000
namespace Yulang.GeneralDeclarativeWitnessBackedNativeInput363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessSeparateAuthorOrder362 (Compared compare lo mid hi)
open GeneralDeclarativeWitnessCrossOwnerReceiver362 (native asked)
open GeneralDeclarativeWitnessNonpointPort362 (env ordinary)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralDeclarativeWitnessRecordWidthFixture359 (authored receipt)
open GeneralDeclarativeWitnessRecordResidual359 (Read check check_exact)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State)
open GeneralNominalCommonBridge (Assignment)

def hasNativeHead : Code → Bool
  | .leaf _ => false
  | _ => true

/-- Each physical position is authenticated independently before looking
at any consuming declaration. The later source's mode table is checked
against all visited names, not inferred from identical emitted rows. -/
structure Backed {contra : Bool} (x : Ordered contra) (e : Environment) where
  nativeInput : Compared x
  sourceCheck : compare x = some nativeInput
  loAddress : x.before.native.write.address.target = native.lower
  midAddress : x.center.native.write.address.target = native.center
  hiAddress : x.after.native.write.address.target = native.upper
  sourceHead : hasNativeHead x.before.native.write.code = true
  left : Compiled e table false (lo x) (mid x)
  right : Compiled e table false (mid x) (hi x)
  recordInput : Read authored x.after.final.ordinary receipt

def verify {contra} (x : Ordered contra) (e : Environment) : Option (Backed x e) :=
  match r : compare x with
  | none => none
  | some api => do
    if targets : x.before.native.write.address.target = native.lower ∧
        x.center.native.write.address.target = native.center ∧
        x.after.native.write.address.target = native.upper then
      if known : hasNativeHead x.before.native.write.code then
        if ordinary : check authored x.after.final.ordinary receipt then
          let left ← GeneralDeclarativeWitnessSparseIntervals357.compile e table false (lo x) (mid x)
          let right ← GeneralDeclarativeWitnessSparseIntervals357.compile e table false (mid x) (hi x)
          pure ⟨api,r,targets.1,targets.2.1,targets.2.2,known,left,right,check_exact.mp ordinary⟩
        else none
      else none
    else none

def accepted {contra} (x : Ordered contra) : Bool :=
  (env.map fun e => (verify x e).isSome).getD false

theorem two_lanes_authenticate_before_choosing_body (contra : Bool) :
    ((run contra).map accepted).getD false = true := by cases contra <;> decide +kernel

theorem source_evidence_agrees_in_every_model {contra} {x : Ordered contra} {e : Environment}
    (start : run contra = some x) (a : Backed x e) (m : Assignment) (v : NativeViews)
    (fit : Fits x.after.final m v) :
    ContextDerives table m false (lo x) (mid x) ∧ ContextDerives table m false (mid x) (hi x) ∧
    a.left.rows = a.nativeInput.left.rows ∧ a.right.rows = a.nativeInput.right.rows ∧
    (∃ low middle high, v native.lower = some low ∧ v native.center = some middle ∧ v native.upper = some high) := by
  have precise := GeneralDeclarativeWitnessSeparateAuthorOrder362.all_claims_one_final_fit start a.sourceCheck m v fit
  exact ⟨precise.1,precise.2.1,
    GeneralDeclarativeWitnessModeScope362.one_authorized_table_cannot_change_comparison_rows a.nativeInput.left a.left,
    GeneralDeclarativeWitnessModeScope362.one_authorized_table_cannot_change_comparison_rows a.nativeInput.right a.right,
    ⟨_,_,_,precise.2.2.1,precise.2.2.2.1,precise.2.2.2.2⟩⟩

end Yulang.GeneralDeclarativeWitnessBackedNativeInput363
