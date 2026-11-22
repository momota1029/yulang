import Yulang.GeneralDeclarativeWitnessOriginPosition352
import Yulang.GeneralDeclarativeWitnessMixedReleaseFixture352

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 22000000
namespace Yulang.GeneralDeclarativeWitnessOriginControls352
open GeneralDeclarativeWitnessMixedReleaseFixture352 (solution problem out key stamp)
open GeneralDeclarativeWitnessMixedFixture352 (answer)
open GeneralDeclarativeWitnessOriginPosition352 (Location location)
open GeneralDeclarativeWitnessTagSources351 (offer)
open GeneralDeclarativeWitnessIdentity351 (Key Owned)

def witnessAt (ordinal : Nat) : Option Location := do
  let (s,w) ← solution
  let a ← GeneralDeclarativeWitnessMixedRelease352.decode (problem s [key]) [stamp] w answer
  pure (← location (problem s [key]).publisher.authored a.prior.owned [key] ordinal)

def alongNamedArm : Option (Nat × GeneralNominalCenteredHeadMatExpressions.Expr) := do
  let (s,w) ← solution
  let a ← GeneralDeclarativeWitnessMixedRelease352.decode (problem s [key]) [stamp] w answer
  let hit ← offer a.consumer.global.live 9 ⟨5,.same⟩
  pure (hit.owner,hit.rhs)

theorem released_not_authored : witnessAt 5 = some (.published ⟨key,out⟩) := by decide +kernel

def reportsArm : Bool :=
  (alongNamedArm.map (fun x => decide (x.1 = 9) &&
    GeneralDeclarativeWitnessLiteral349.eqExpr x.2 out.right)).getD false

theorem accepts_exact_ref : reportsArm = true := by decide +kernel

theorem actual_ref_ordinal : alongNamedArm = some (9,out.right) := by
  have yes := accepts_exact_ref
  unfold reportsArm at yes
  cases h : alongNamedArm with
  | none => simp [h] at yes
  | some x =>
    obtain ⟨n,e⟩ := x
    have checked : (decide (n = 9) && GeneralDeclarativeWitnessLiteral349.eqExpr e out.right) = true := by
      simpa only [h,Option.map_some,Option.getD_some] using yes
    have parts := GeneralDeclarativeWitnessProblem349.splitAnd checked
    rw [of_decide_eq_true parts.1,(GeneralDeclarativeWitnessLiteral349.eq_expr ..).mp parts.2]

/-- An exactly equal original row and later licensed publication remain
different certificate coordinates. -/
theorem independent_copies :
    location [out] [⟨key,out⟩] [key] 0 = some (.authored out) ∧
    location [out] [⟨key,out⟩] [key] 1 = some (.published ⟨key,out⟩) ∧
    location [out] [⟨key,out⟩] [] 1 = none := by decide +kernel

end Yulang.GeneralDeclarativeWitnessOriginControls352
