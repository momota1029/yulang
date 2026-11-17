import Yulang.GeneralDictionaryLooseIterationStage240
import Yulang.GeneralDictionaryLooseIterationRound240
set_option backward.isDefEq.respectTransparency false
/-! All-index actual reachable stages, with future upper-patch witnesses
preserved through each genuine guarded install/refresh/reobserve round. -/
namespace Yulang.GeneralDictionaryLooseIterationIteration240
open GeneralDictionaryLooseLoopSource240
open GeneralDictionaryLooseIterationStage240
open GeneralDictionaryLooseFamilyNovel240 (bad)
open GeneralDictionaryLooseIterationRound240
open GeneralNominalVersionedJournal232

noncomputable def successor (stage : Stage n) : Stage (n+1) where
 state := next stage.shape
 shape := next_shape stage.shape
 reachable := B4TargetV5.reachable_steps _ stage.reachable
   (path stage.shape stage.valid stage.recorded (novel stage))
 recorded := next_recorded stage.shape stage.recorded
 valid := models stage.shape stage.recorded stage.valid
 future := by
   intro index later
   exact models_general stage.shape stage.recorded (bad index)
     (stage.future index (by omega))
     (GeneralDictionaryLooseIterationPatched240.packet_holds n index (by omega))

noncomputable def stages : (n : Nat) → Stage n
 | 0 => zero
 | n+1 => successor (stages n)
noncomputable abbrev state (n : Nat) := (stages n).state

theorem reachable (n : Nat) : B4TargetV8.Reachable
 (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root (state n) :=
 (stages n).reachable

theorem inhabited (n : Nat) : Models (state n) model := (stages n).valid

theorem round (n : Nat) : B4Target.Steps (GeneralNominalPointKernel240.Step registry root)
 (state n) (state (n+1)) := path (stages n).shape (stages n).valid (stages n).recorded (novel (stages n))

theorem slots (n : Nat) : (state n).core.erased.current.context.state.base.slots = n+5 := by
 rw [(stages n).shape.current]

theorem distinct {a b : Nat} (different : a ≠ b) : state a ≠ state b := by
 intro same
 have sizes := congrArg (fun s : State roles => s.core.erased.current.context.state.base.slots) same
 rw [slots,slots] at sizes
 omega
end Yulang.GeneralDictionaryLooseIterationIteration240
