import Yulang.GeneralDeclarativeTraceTransfer325
import Yulang.GeneralDeclarativeEqualities322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOrdinaryIncrease325
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeLowerKnown321 (Alias alias_mono)
open GeneralDeclarativeCongruence322 (Congruent Arguments)
open GeneralDeclarativeEqualities322 (Derives Forest)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeTraceTransfer325 (lift_trace)
open GeneralDeclarativeEntailment320 (appendFacts)

structure Extends (s t : State) : Prop where
  normal : s.normal = t.normal
  equations : s.equations ⊆ t.equations

theorem append (s : State) (rows) : Extends s (appendFacts s rows) := ⟨rfl,fun _ h => List.mem_append_left _ h⟩

theorem bounds {s t : State} (extendsOrdinary : Extends s t) (old : Bounds s cap) : Bounds t cap := by
  unfold Bounds at *
  simpa only [extendsOrdinary.normal] using old

theorem alias {s t : State} (extendsOrdinary : Extends s t) (old : Alias s a b) : Alias t a b :=
  alias_mono extendsOrdinary.normal extendsOrdinary.equations old

theorem congruent {s t : State} (extendsOrdinary : Extends s t) (old : Congruent s a b) : Congruent t a b :=
  Congruent.rec
    (motive_1 := fun a b _ => Congruent t a b)
    (motive_2 := fun as bs _ => Arguments t as bs)
    (fun h => .variable (alias extendsOrdinary h))
    (fun _ ih => .primitive ih)
    (fun _ ih => .nominal ih)
    (fun _ _ ih jh => .record ih jh)
    (fun _ ih => .variant ih)
    (fun _ _ ih jh => .join ih jh)
    .nil
    (fun _ _ ih jh => .cons ih jh)
    old

theorem derives {s t : State} (extendsOrdinary : Extends s t) (old : Derives s a b) : Derives t a b :=
  Derives.rec
    (motive_1 := fun a b _ => Derives t a b)
    (motive_2 := fun as bs _ => Forest t as bs)
    (fun h => .row (extendsOrdinary.equations h))
    (fun h => .congruent (congruent extendsOrdinary h))
    (fun e => .refl e)
    (fun _ ih => .symm ih)
    (fun _ _ ih jh => .trans ih jh)
    (fun _ ih => .primitive ih)
    (fun _ ih => .nominal ih)
    (fun _ ih => .pairFirst ih)
    (fun _ ih => .pairSecond ih)
    (fun _ _ ih jh => .record ih jh)
    (fun _ ih => .variant ih)
    (fun _ _ ih jh => .join ih jh)
    .nil
    (fun _ _ ih jh => .cons ih jh)
    old

/-- Authorized observation growth is separate from ordinary strengthening.
An unapplied origin or unfinished output is not thereby available. -/
theorem supported_trace {s t : State} {one : Supported s prior} {two : Supported t current}
    (extendsOrdinary : Extends s t)
    (extendsSupport : (restriction one).equations ⊆ (restriction two).equations)
    (old : Trace (restriction one) mode n code uses) : Trace (restriction two) mode n code uses :=
  lift_trace (s := restriction one) (t := restriction two) extendsOrdinary.normal extendsSupport old

end Yulang.GeneralDeclarativeOrdinaryIncrease325
