import Yulang.CommonNominalFullFiniteConstructors
import Yulang.CommonNominalFullModel

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
namespace Yulang.GeneralDeclarativeOpaqueChannel328
open CommonNominalFullCarrier (Ty Row observeTy)
open CommonNominalSyntax (graph observe Layer)
open CommonNominalFullDemand (Observation Environment ProbeAt ProbeStep MaskedProbeStep)

def union : Option Ty → Option Ty → Option Ty
  | some a,some b => some (.union a b)
  | _,_ => none

def meet : Option Ty → Option Ty → Option Ty
  | some a,some b => some (.inter a b)
  | some a,none => some a
  | none,b => b

/-- Project the actual observer channel, not a lower/upper stand-in.
An absent channel rejects even the trivial *payload* observation;
it is not the type top, which still admits that observation. -/
def project (last : Bool) : Ty → Option Ty
  | .pair a b => some (graph Row (if last then b else a))
  | .union a b => union (project last a) (project last b)
  | .inter a b => meet (project last a) (project last b)
  | .mask _ t => project last t
  | .bottom => some .bottom
  | _ => none

def channel (last : Bool) (o : Observation Row) : Observation Row :=
  if last then .pairLast o else .pairFirst o

def tests (d : Nat) (env : Environment Row)
    (order : CommonNominalFullDemand.Ty Row → CommonNominalFullDemand.Ty Row → Prop)
    (o : Observation Row) : Option Ty → Prop
  | none => False
  | some a => MaskedProbeStep Common.rowLe env order [] (observeTy d a) o

theorem tests_union (d : Nat) (env) (order) (o) (a b) :
    tests d env order o (union a b) ↔ tests d env order o a ∧ tests d env order o b := by
  cases a <;> cases b <;> cases o <;>
    simp [tests,union,observeTy,Layer.evalAt,MaskedProbeStep]

theorem tests_meet (d : Nat) (env) (order) (o) (a b) :
    tests d env order o (meet a b) ↔ tests d env order o a ∨ tests d env order o b := by
  cases a <;> cases b <;> cases o <;>
    simp [tests,meet,observeTy,Layer.evalAt,MaskedProbeStep]

/-- Exact per-channel observation at every finite slice of the regular
carrier. The shift is the actual marker step consumed by a pair. -/
theorem probe_step (last : Bool) (d : Nat) (env) (order) (o) (shape : Ty) (hidden : List Nat) :
    MaskedProbeStep Common.rowLe env order hidden (observeTy (d+1) shape) (channel last o) ↔
      tests d env order o (project last shape) := by
  induction shape generalizing hidden with
  | union a b ih jh =>
    rw [project,tests_union]
    cases last <;> simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep] using
      and_congr (ih hidden) (jh hidden)
  | inter a b ih jh =>
    rw [project,tests_meet]
    cases last <;> simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep] using
      or_congr (ih hidden) (jh hidden)
  | mask extra t ih =>
    cases last <;> simpa [channel,project,observeTy,Layer.evalAt,MaskedProbeStep] using ih (hidden ++ extra)
  | pair a b =>
    cases last <;> rfl
  | recordDefault label known fallback =>
    cases last <;> rfl
  | bottom =>
    cases last <;> cases o <;>
      simp [channel,project,tests,observeTy,Layer.evalAt,MaskedProbeStep]
  | base | float | top | emptyRecord | exactEmpty | record | variant | arrow | nominal =>
    cases last <;> rfl

end Yulang.GeneralDeclarativeOpaqueChannel328
