import Yulang.GeneralDeclarativeExactDelete337
import Yulang.GeneralDeclarativeEndpointRecord336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExactDeleteAuth337
open GeneralDeclarativeExactDelete337 (subtract recordShell monotone congruent)
open GeneralDeclarativeEndpointRecord336 (Read interp interval)
open GeneralDeclarativeRecordSpine330 (Terminal ends)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeVisibleRecord326 (visible_spine)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeWhere319 (InInterval)
open CommonRoleCanonicalRows (Row normalize residual)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralNominalCommonBridge (Assignment)

private theorem keeps_shell (m : Assignment) (r : Row Expr) (terminal : Terminal e) :
    recordShell (interp m (withTail r e)) = interp m (withTail r e) := by
  cases r with
  | nil => cases terminal <;> rfl
  | cons one _ => cases one; rfl

theorem literal (keys : List Nat) (m : Assignment) (r : Row Expr) (terminal : Terminal e) :
    subtract keys (interp m (withTail r e)) = interp m (withTail (residual keys r) e) := by
  induction r with
  | nil => cases terminal <;> rfl
  | cons row rest ih =>
    obtain ⟨key,payload⟩ := row
    by_cases found : key ∈ keys
    · have dropped : residual keys ((key,payload)::rest) = residual keys rest := by simp [residual,found]
      rw [dropped]
      change (if key ∈ keys then recordShell (subtract keys (interp m (withTail rest e))) else _) = _
      rw [ite_eq_left found,ih,keeps_shell m _ terminal]
    · have kept : residual keys ((key,payload)::rest) = (key,payload)::residual keys rest := by simp [residual,found]
      rw [kept]
      change (if key ∈ keys then recordShell (subtract keys (interp m (withTail rest e))) else
        CommonNominalFullCarrier.record key (interp m payload) (subtract keys (interp m (withTail rest e)))) =
          CommonNominalFullCarrier.record key (interp m payload) (interp m (withTail (residual keys rest) e))
      rw [ite_eq_right found,ih]

/-- First-field-wins normalization preserves standalone deletion. -/
theorem canonical (keys : List Nat) (m : Assignment) (r : Row Expr) (terminal : Terminal e) :
    Equivalent (subtract keys (interp m (withTail r e)))
      (interp m (withTail (residual keys (normalize r)) e)) := by
  have keep := congruent keys (visible_spine m r e)
  change Equivalent (subtract keys (interp m (withTail r e))) (subtract keys (interp m (withTail (normalize r) e))) at keep
  rwa [literal keys m (normalize r) terminal] at keep

/-- Both standalone residual endpoints are obtained from their
authored, authorized terminal. The actual value uses the model of the
actual input, which need not have a backed center equation. -/
theorem supported {s : State} {p : Supported s done}
    (r : Read p arg keys ls us first last le ue) (m) (fit : Models s m) :
    InInterval (interp m (withTail (residual keys (normalize ls)) le))
      (interp m (withTail (residual keys (normalize us)) ue))
      (subtract keys (m arg.center).1) := by
  have fromLo := canonical keys m ls (ends r.lo)
  have fromHi := canonical keys m us (ends r.hi)
  have valid := interval r m fit
  exact ⟨CommonNominalFullCarrier.subtype_trans fromLo.2 (monotone keys valid.1),
    CommonNominalFullCarrier.subtype_trans (monotone keys valid.2) fromHi.1⟩

end Yulang.GeneralDeclarativeExactDeleteAuth337
