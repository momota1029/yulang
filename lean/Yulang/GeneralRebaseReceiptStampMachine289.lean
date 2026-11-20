import Yulang.GeneralRebaseReceiptTypedStamp289

/-! A saved typed stamp is never used as unconditional publication
permission. Recompute the current stamp and then re-run the old finite
guards. A change only in a typed endpoint can invalidate it. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptStampMachine289
open GeneralRebaseReceiptTypedStamp289 (Stamp)
open GeneralRebaseReceiptMachine289 (Stop)
abbrev Old := GeneralRebaseReceiptMachine289.Phase
open GeneralRebaseReceiptWire289 (Wire Decision check Offer)

inductive Phase where
  | scan
  | held (stamp : Stamp)
  | sent (stamp : Stamp)
  | stopped (reason : Stop)
  deriving Repr, DecidableEq

def erase : Phase → Old
  | .scan => .scan
  | .held s => .received s.offer
  | .sent s => .published s.offer
  | .stopped reason => .stopped reason

def lift (now : Stamp) : Old → Phase
  | .scan => .scan
  | .received ask => .held { now with offer := ask }
  | .published ask => .sent { now with offer := ask }
  | .stopped reason => .stopped reason

def Valid (now : Stamp) : Phase → Prop
  | .held saved | .sent saved => saved = now
  | .scan | .stopped _ => True

theorem erase_lift (now : Stamp) (phase : Old) : erase (lift now phase) = phase := by cases phase <;> rfl

theorem lift_erase (now : Stamp) (phase : Phase) (valid : Valid now phase) :
    lift now (erase phase) = phase := by
  cases phase with
  | scan => rfl
  | stopped => rfl
  | held saved | sent saved => change saved = now at valid; subst saved; rfl

theorem lift_valid (now : Stamp) (phase : Old)
    (stamped : (∀ key, phase = .received key → key = now.offer) ∧
      ∀ key, phase = .published key → key = now.offer) :
    Valid now (lift now phase) := by
  cases phase with
  | scan => trivial
  | stopped => trivial
  | received key => rw [stamped.1 key rfl]; rfl
  | published key => rw [stamped.2 key rfl]; rfl

def step (now : Stamp) (baseTick : Old → Option Old) : Phase → Option Phase
  | .held saved =>
      if saved = now then (baseTick (.received saved.offer)).map (lift now)
      else some (.stopped .stale)
  | other => (baseTick (erase other)).map (lift now)

theorem stale_exact (now old : Stamp) (baseTick : Old → Option Old) (different : old ≠ now) :
    step now baseTick (.held old) = some (.stopped .stale) := by
  simp [step,different]

theorem stable_tick (now : Stamp) (baseTick : Old → Option Old) (before : Phase)
    (valid : Valid now before) :
    step now baseTick before = (baseTick (erase before)).map (lift now) := by
  cases before with
  | held saved => exact ite_eq_left (show saved = now from valid)
  | scan | sent | stopped => rfl

theorem erases_tick (now : Stamp) (baseTick : Old → Option Old) (before : Phase)
    (valid : Valid now before) :
    (step now baseTick before).map erase = baseTick (erase before) := by
  rw [stable_tick now baseTick before valid]
  cases baseTick (erase before) <;> simp [erase_lift]

end Yulang.GeneralRebaseReceiptStampMachine289
