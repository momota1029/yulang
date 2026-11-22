import Yulang.GeneralDeclarativeWitnessExactRest349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessExactProjection349
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessExactRest349 (Wire)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessEquation349 (in_every_model)
open GeneralDeclarativeWitnessReceipt349 (checks each)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactOverlay337 (Holds ModelsExact)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeEndpointRecord336 (interp)
open GeneralDeclarativeRecordPayloads330 (visible has_field)
open GeneralDeclarativeRecordIntervals330 (projected_below)
open GeneralDeclarativeRecordConsumption330 (lookup_iff)
open CommonRoleCanonicalRows (lookup)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)

/-- The actual center shape is checked by ordinary derivation only.
Source readiness must still be checked on independently backed endpoints. -/
def check (s : State) (e : Entry) (w : Wire) : Bool :=
  match e.1 with
  | .rest .. => GeneralDeclarativeWitnessExactRest349.check s e w
  | .field a key lo hi =>
    match lookup key w.centerRows with
    | none => false
    | some payload =>
      (GeneralDeclarativeWitnessEquation349.check s (.variable a.center)
        (withTail w.centerRows w.endExpr) w.centerShape &&
       GeneralDeclarativeWitnessEquation349.check s (.variable e.2.lower) lo w.lower) &&
      (GeneralDeclarativeWitnessEquation349.check s (.variable e.2.center) payload w.middle &&
       GeneralDeclarativeWitnessEquation349.check s (.variable e.2.upper) hi w.upper)

theorem sound {s : State} {e : Entry} {w : Wire} (ok : check s e w = true)
    (m : Assignment) (fit : Models s m) : Holds m e := by
  rcases e with ⟨p,names⟩
  cases p with
  | rest arg keys lo hi =>
    exact GeneralDeclarativeWitnessExactRest349.sound (s := s) (entry := (.rest arg keys lo hi,names)) (w := w) ok m fit
  | field arg key lo hi =>
    change (match lookup key w.centerRows with
      | none => false
      | some payload =>
        (GeneralDeclarativeWitnessEquation349.check s (.variable arg.center)
          (withTail w.centerRows w.endExpr) w.centerShape &&
         GeneralDeclarativeWitnessEquation349.check s (.variable names.lower) lo w.lower) &&
        (GeneralDeclarativeWitnessEquation349.check s (.variable names.center) payload w.middle &&
         GeneralDeclarativeWitnessEquation349.check s (.variable names.upper) hi w.upper)) = true at ok
    cases checked : lookup key w.centerRows with
    | none =>
      rw [checked] at ok
      cases ok
    | some payload =>
      rw [checked] at ok
      have first := splitAnd (splitAnd ok).1
      have second := splitAnd (splitAnd ok).2
      have center := in_every_model first.1 m fit
      have l := in_every_model first.2 m fit
      have c := in_every_model second.1 m fit
      have h := in_every_model second.2 m fit
      have sample := visible (lookup_iff.mpr checked) w.endExpr m
      obtain ⟨actual,loaded⟩ := has_field sample center.1
      have observeEq : CommonNominalFullCarrier.Equivalent (interp m payload) actual :=
        ⟨projected_below key false sample loaded center.2,projected_below key false loaded sample center.1⟩
      refine ⟨(interp m lo,actual,interp m hi),?_,l,eqv_trans c observeEq,h⟩
      change (GeneralDeclarativeRecordChannel330.project key false [] (m arg.center).1).map
        (fun mid => (interp m lo,mid,interp m hi)) = some (interp m lo,actual,interp m hi)
      change GeneralDeclarativeRecordChannel330.project key false [] (m arg.center).1 = some actual at loaded
      simp [loaded]

def checkedList (s : State) (entries : List Entry) (w : List Wire) : Bool := checks (check s) entries w

/-- Reflect both field and standalone residual sidecar entries using
evidence from the fixed current state; no extra coordinates are
allocated and the same assignment is used for every accepted entry. -/
theorem fixed_models {s : State} {es : List Entry} {w : List Wire}
    (ok : checkedList s es w = true) (m : Assignment) (fit : Models s m) : ModelsExact s es m := by
  refine ⟨fit,?_⟩
  intro e got
  obtain ⟨cw,_,verified⟩ := each ok e got
  exact sound verified m fit

end Yulang.GeneralDeclarativeWitnessExactProjection349
