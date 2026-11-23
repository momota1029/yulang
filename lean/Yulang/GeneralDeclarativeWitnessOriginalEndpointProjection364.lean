import Yulang.GeneralDeclarativeWitnessActualCrossOwnerDictionary363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 82000
set_option maxHeartbeats 105000000
namespace Yulang.GeneralDeclarativeWitnessOriginalEndpointProjection364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessSeparateAuthorOrder362 (lo mid hi all_claims_one_final_fit)
open GeneralDeclarativeWitnessSelectedNonpointRoot363 (Root emit)
open GeneralDeclarativeWitnessSelectedNonpointChild363 (backedOccurrence)
open GeneralDeclarativeWitnessNativeRelease360 (ExactRelease checked_exact_written_value)
open GeneralDeclarativeWitnessNativeValue360 (Code Value)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralDeclarativeWitnessCompiler350 (trip)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)

structure Spine (c : Code) where
  head : Nat
  payload : Nat
  exact : c = .unary head (.leaf payload)

def spine (c : Code) : Option (Spine c) :=
  match c with
  | .unary h (.leaf a) => some ⟨h,a,rfl⟩
  | _ => none

structure Projection {contra : Bool} {x : Ordered contra} {e : Environment} (r : Root x e) where
  a : Spine x.before.native.write.code
  b : Spine x.after.native.write.code
  same : a.head = b.head
  locator : trip r.span = (310,302,311)
  lowerDistinct : x.before.native.write.address.owner ≠ x.after.native.write.address.owner
  lowerCurrent : x.before.native.write.address.target = 301
  upperCurrent : x.after.native.write.address.target = 303
  declaredBetween : Compiled e table false (lo x) (hi x)

def project {contra} {x : Ordered contra} {e : Environment} (r : Root x e) : Option (Projection r) := do
  let _ ← backedOccurrence r
  let a ← spine x.before.native.write.code
  let b ← spine x.after.native.write.code
  if h : a.head = b.head ∧ trip r.span = (310,302,311) ∧
      x.before.native.write.address.owner ≠ x.after.native.write.address.owner ∧
      x.before.native.write.address.target = 301 ∧ x.after.native.write.address.target = 303 then
    let checked ← GeneralDeclarativeWitnessSparseIntervals357.compile e table false (lo x) (hi x)
    pure ⟨a,b,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,checked⟩
  else none

theorem exact_endpoint_provenance {contra} {x : Ordered contra} {e : Environment} {r : Root x e}
    (p : Projection r) (made : run contra = some x) (m : Assignment) (v : NativeViews)
    (fit : Fits r.world m v) :
    v 301 = some (.unary p.a.head (.leaf (m p.a.payload).1)) ∧
    v 303 = some (.unary p.a.head (.leaf (m p.b.payload).1)) ∧
    ContextDerives table m false (lo x) (mid x) ∧
    ContextDerives table m false (mid x) (hi x) := by
  have origin : Fits x.after.final m v :=
    ⟨(GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared r.body m fit.1).1,fit.2⟩
  have a := checked_exact_written_value (w := x.after.final) r.ready.nativeInput.openedLow m v origin
  have b := checked_exact_written_value (w := x.after.final) r.ready.nativeInput.openedHigh m v origin
  have h := all_claims_one_final_fit made r.ready.sourceCheck m v origin
  rw [p.lowerCurrent,p.a.exact] at a
  rw [p.upperCurrent,p.b.exact,← p.same] at b
  exact ⟨a,b,h.1,h.2.1⟩

def sanity {contra x e r} (p : @Projection contra x e r) : Bool :=
  decide (p.a.head = GeneralDeclarativeWitnessThreeNative362.ctor contra ∧
    p.a.payload = GeneralDeclarativeWitnessThreeNative362.first contra ∧
    p.b.payload = GeneralDeclarativeWitnessThreeNative362.last contra)

theorem actual_projection_uses_two_authored_rows (contra : Bool) :
   ((run contra).bind fun x =>
      GeneralDeclarativeWitnessNonpointPort362.env.bind fun e =>
      (emit x e).bind fun r => (project r).map sanity).getD false = true := by
  cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessOriginalEndpointProjection364
