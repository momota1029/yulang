import Yulang.GeneralDeclarativeGrowth327

namespace Yulang.GeneralStoppedPlacement335
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (All₂)

/-- Logical-name comparison is mode-by-mode. A center alias never
silently upgrades an endpoint, and an associated output target is
not replaced by a term with the same denotation. -/
structure SameCapture (s : State) (raw compiled : Capture) : Prop where
  lower : Alias s raw.lower compiled.lower
  center : Alias s raw.center compiled.center
  upper : Alias s raw.upper compiled.upper

structure SameDemand (s : State) (raw compiled : Demand) : Prop where
  role : raw.role = compiled.role
  arguments : All₂ (SameCapture s) raw.arguments compiled.arguments
  outputs : raw.outputs = compiled.outputs

def Meaning (m : GeneralNominalCommonBridge.Assignment) (a b : Capture) : Prop :=
  Equivalent (m a.lower).1 (m b.lower).1 ∧
  Equivalent (m a.center).1 (m b.center).1 ∧ Equivalent (m a.upper).1 (m b.upper).1

theorem capture_models {s : State} (fit : Models s m) (given : SameCapture s a b) : Meaning m a b :=
  ⟨alias_sound given.lower m fit,alias_sound given.center m fit,alias_sound given.upper m fit⟩

theorem demands_models {s : State} (fit : Models s m) (given : SameDemand s a b) :
    a.role = b.role ∧ a.outputs = b.outputs ∧ All₂ (Meaning m) a.arguments b.arguments := by
  refine ⟨given.role,given.outputs,?_⟩
  have check {xs ys : List Capture} (h : All₂ (SameCapture s) xs ys) :
      All₂ (Meaning m) xs ys := by
    induction h with
    | nil => exact .nil
    | cons first _ ih => exact .cons (capture_models fit first) ih
  exact check given.arguments

end Yulang.GeneralStoppedPlacement335
