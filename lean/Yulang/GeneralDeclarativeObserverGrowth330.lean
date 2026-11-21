import Yulang.GeneralDeclarativeRecordFieldRead330
import Yulang.GeneralDeclarativeArityCompiler330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeObserverGrowth330
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeGrowth327 (Extends aliases fits)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeRecordFieldRead330 (Fields)
open GeneralDeclarativeStableTrace329 (Located)
open GeneralDeclarativeAritySource330 (Source)
open GeneralDeclarativeEndpointProbe321 (Matches)
open CommonRoleOutermostResolver (All₂)

/-- Carry exactly the old origin predicates. Ordinary growth is not
license to mark a new equation as available for a source trace. -/
def preserve {s t : State} (p : Supported s done) (grown : Extends s t) : Supported t done :=
  ⟨p.derivesFrom,fun h => grown.equations (p.ordinary h)⟩

theorem backed_same {s t : State} (p : Supported s done) (grown : Extends s t) (eq : Equation) :
    eq ∈ (restriction (preserve p grown)).equations ↔ eq ∈ (restriction p).equations := by
  rw [backed_iff,backed_iff]
  rfl

theorem sources_grow {s t : State} (p : Supported s done) (grown : Extends s t) :
    Extends (restriction p) (restriction (preserve p grown)) :=
  ⟨grown.constraints,grown.intervals,fun q h => (backed_same p grown q).mpr h⟩

theorem trace {s t : State} (grown : Extends s t) (seen : Trace s mode n code uses) :
    Trace t mode n code uses :=
  Trace.rec
    (motive_1 := fun mode n code links _ => Trace t mode n code links)
    (motive_2 := fun mode ns codes links _ => TraceArgs t mode ns codes links)
    (by intro _ _ _; exact .capture)
    (by intro _ _ _ _ _ _ _ equal stored _ ih; exact .primitive (aliases grown equal) (grown.equations stored) ih)
    (by intro _ _ _ _ _ _ _ equal stored _ ih; exact .nominal (aliases grown equal) (grown.equations stored) ih)
    (by intro _ _ _ _ _ _ _ _ _ _ equal stored _ _ ih jh
        exact .record (aliases grown equal) (grown.equations stored) ih jh)
    (by intro _ _ _ _ _ _ _ equal stored _ ih; exact .variant (aliases grown equal) (grown.equations stored) ih)
    (by intro _ _ _ _ _ _ _ _ _ equal stored _ _ ih jh
        exact .join (aliases grown equal) (grown.equations stored) ih jh)
    (by intro _; exact .nil)
    (by intro _ _ _ _ _ _ _ _ _ ih jh; exact .cons ih jh)
    seen

theorem spine {s t : State} (grown : Extends s t) (seen : Spine s n fields terminal) :
    Spine t n fields terminal := by
  induction seen with
  | width a b => exact .width (aliases grown a) (grown.equations b)
  | exactEnd a b => exact .exactEnd (aliases grown a) (grown.equations b)
  | cons a b _ rest => exact .cons (aliases grown a) (grown.equations b) rest

theorem located {s t : State} (grown : Extends s t) (uses : All₂ (Located s) a b) :
    All₂ (Located t) a b := by
  induction uses with
  | nil => exact .nil
  | cons h _ next => exact .cons ⟨h.1,h.2.1,fits grown h.2.2⟩ next

theorem fields {s t : State} {p : Supported s done} (grown : Extends s t) (seen : Fields p a b caps) :
    Fields (preserve p grown) a b caps := by
  induction seen with
  | nil => exact .nil
  | cons independent positions _ next =>
    exact .cons (trace (sources_grow p grown) independent) (located grown positions) next

theorem endpoints {s t : State} (grown : Extends s t) (seen : Matches s c i a pat) :
    Matches t c i a pat := by
  obtain ⟨known,code,lower,upper,printed,lo,hi⟩ := seen
  exact ⟨fits grown known,code,lower,upper,printed,trace grown lo,trace grown hi⟩

end Yulang.GeneralDeclarativeObserverGrowth330
