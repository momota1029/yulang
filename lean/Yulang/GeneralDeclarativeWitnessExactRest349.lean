import Yulang.GeneralDeclarativeWitnessProjection349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessExactRest349
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessEquation349 (Code)
open GeneralDeclarativeWitnessManifest349 (terminal)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessReceipt349 (checks each)
open GeneralDeclarativeEndpointOverlay336 (Entry Agreement)
open GeneralDeclarativeExactOverlay337 (ModelsExact Holds eval)
open GeneralDeclarativeEndpointBatch336 (atSlots)
open GeneralDeclarativeEndpointRecord336 (interp)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeExactDelete337 (subtract congruent)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row residual normalize)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

/-- Ordinary evidence, not source readiness. This checker can use a
truthful but withheld center equation to verify *output* coordinates;
it never puts that row into a supported input slice. -/
structure Wire where
  centerRows : Row Expr
  endExpr : Expr
  centerShape : Code
  lower : Code
  middle : Code
  upper : Code

def check (s : State) (entry : Entry) (w : Wire) : Bool :=
  match entry.1 with
  | .field .. => false
  | .rest arg keys lo hi =>
    ((terminal w.endExpr).isSome &&
      GeneralDeclarativeWitnessEquation349.check s (.variable arg.center)
        (withTail w.centerRows w.endExpr) w.centerShape) &&
    ((GeneralDeclarativeWitnessEquation349.check s (.variable entry.2.lower) lo w.lower &&
      GeneralDeclarativeWitnessEquation349.check s (.variable entry.2.center)
        (withTail (residual keys (normalize w.centerRows)) w.endExpr) w.middle) &&
      GeneralDeclarativeWitnessEquation349.check s (.variable entry.2.upper) hi w.upper)

theorem sound {s : State} {entry : Entry} {w : Wire} (ok : check s entry w = true)
    (m : Assignment) (fit : Models s m) : Holds m entry := by
  rcases entry with ⟨project,slot⟩
  cases project with
  | field => cases ok
  | rest arg keys lo hi =>
    have first := splitAnd (splitAnd ok).1
    have second := splitAnd (splitAnd ok).2
    have low := GeneralDeclarativeWitnessEquation349.in_every_model (splitAnd second.1).1 m fit
    have mid := GeneralDeclarativeWitnessEquation349.in_every_model (splitAnd second.1).2 m fit
    have high := GeneralDeclarativeWitnessEquation349.in_every_model second.2 m fit
    have actual := GeneralDeclarativeWitnessEquation349.in_every_model first.2 m fit
    rcases term : terminal w.endExpr with _ | ended
    · simp [term] at first
    · let actualResidual := subtract keys (m arg.center).1
      refine ⟨(interp m lo,actualResidual,interp m hi),rfl,low,?_,high⟩
      have projected := GeneralDeclarativeExactDeleteAuth337.canonical keys m w.centerRows ended.property
      have shape : CommonNominalFullCarrier.Equivalent (m arg.center).1 (interp m (withTail w.centerRows w.endExpr)) := actual
      exact eqv_trans mid (eqv_symm (eqv_trans (congruent keys shape) projected))

def checkList (s : State) (entries : List Entry) (code : List Wire) : Bool :=
  checks (check s) entries code

/-- Already-current named residual coordinates, in the same model.
Variable names and record meaning are not repaired by extension. This
covers residual entries, not field entries or the whole tagged checker. -/
theorem same_model {s : State} {entries : List Entry} {code : List Wire}
    (ok : checkList s entries code = true) (m : Assignment) (fit : Models s m) :
    ModelsExact s entries m := by
  refine ⟨fit,?_⟩
  intro entry stored
  obtain ⟨w,_,checksOut⟩ := each ok entry stored
  exact sound checksOut m fit

end Yulang.GeneralDeclarativeWitnessExactRest349
