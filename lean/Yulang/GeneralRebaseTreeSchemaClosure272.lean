import Yulang.GeneralRebaseTreeSchemaProgress272

namespace Yulang.GeneralRebaseTreeSchemaClosure272
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseTreeInterpreter272 (Source Certified)
open GeneralRebaseTreeSchema272 (rounds runPlans rounds_sound)
open GeneralRebaseTreeSchemaProgress272 (missing strict)
open GeneralRebaseFiniteTree272 (Tree)

def Stable (state : State roles) (src : Source) : Prop := runPlans src state.plans = src

theorem rounds_stable_identity (state : State roles) (src : Source) (fixed : Stable state src) (n : Nat) :
 rounds state n src = src := by
 induction n with
 | zero => rfl
 | succ n ih =>
   change rounds state n (runPlans src state.plans) = src
   rw [fixed]
   exact ih

theorem rounds_stable (state : State roles) (n : Nat) (src : Source)
 (enough : (missing state.plans src).length ≤ n) : Stable state (rounds state n src) := by
 induction n generalizing src with
 | zero =>
   by_cases quiet : Stable state src
   · exact quiet
   · have counter := strict state.plans src quiet
     omega
 | succ n ih =>
   by_cases quiet : Stable state src
   · rw [rounds_stable_identity state src quiet]
     exact quiet
   · have smaller := strict state.plans src quiet
     apply ih
     omega

/-- Finite closure under the given plans' supported emitted equations.
The bound counts remaining target occurrences, not witness-tree height. -/
def close (state : State roles) (src : Source) : Source :=
 rounds state (missing state.plans src).length src

theorem close_stable (state : State roles) (src : Source) : Stable state (close state src) :=
 rounds_stable state _ src (Nat.le_refl _)

theorem close_sound (state : State roles) (m : Assignment) (valid : Models state m)
 (src : Source) (checked : Certified m src) : Certified m (close state src) :=
 rounds_sound state m valid _ src checked

theorem close_twice (state : State roles) (src : Source) :
 close state (close state src) = close state src :=
 rounds_stable_identity state _ (close_stable state src) _

theorem preserves (state : State roles) (n : Nat) (src : Source) (id : Nat) (t : Tree)
 (before : src id = some t) : rounds state n src id = some t := by
 induction n generalizing src with
 | zero => exact before
 | succ n ih => exact ih _ (GeneralRebaseTreeSchemaProgress272.next_known state.plans src id t before)

theorem preserved_by_close (state : State roles) (src : Source) (id : Nat) (t : Tree)
 (before : src id = some t) : close state src id = some t :=
 preserves state _ src id t before

end Yulang.GeneralRebaseTreeSchemaClosure272
