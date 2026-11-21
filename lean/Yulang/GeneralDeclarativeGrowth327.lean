import Yulang.GeneralDeclarativeOrdinaryIncrease325
import Yulang.GeneralDeclarativeAggregate324
import Yulang.GeneralDeclarativeWhereIntervals325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeGrowth327
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeCongruence322 (Congruent Arguments)
open GeneralDeclarativeEqualities322 (Derives Forest)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeCaptureClosure320 (withOrdinary)
open GeneralDeclarativeWhereIntervals325 (withInterval)

/-- Ordinary weakening across additions. It says nothing about
decision results, persistence of noncycles, or new authorized origins. -/
structure Extends (s t : State) : Prop where
  constraints : s.normal.ordinary ⊆ t.normal.ordinary
  intervals : s.normal.intervals ⊆ t.normal.intervals
  equations : s.equations ⊆ t.equations

theorem trans {a b c : State} (before : Extends a b) (after : Extends b c) : Extends a c :=
  ⟨fun _ h => after.constraints (before.constraints h),
    fun _ h => after.intervals (before.intervals h),
    fun _ h => after.equations (before.equations h)⟩

theorem facts (s : State) (rows) : Extends s (appendFacts s rows) :=
  ⟨fun _ h => h,fun _ h => h,fun _ h => List.mem_append_left _ h⟩

theorem ordinary (s : State) (rows) : Extends s (withOrdinary s rows) :=
  ⟨fun _ h => List.mem_append_left _ h,fun _ h => h,fun _ h => h⟩

theorem span (s : State) (capture) : Extends s (withInterval s capture) :=
  ⟨fun _ h => h,fun _ h => List.mem_append_left _ h,fun _ h => h⟩

theorem boundsOne {s t : State} (h : Extends s t) (proof : Bound s.normal a b) : Bound t.normal a b := by
  induction proof with
  | constraint stored => exact .constraint (h.constraints stored)
  | interval stored => exact .interval (h.intervals stored)
  | refl => exact .refl _
  | trans _ _ l r => exact .trans l r

theorem fits {s t : State} (h : Extends s t) (b : Bounds s a) : Bounds t a :=
  ⟨boundsOne h b.1,boundsOne h b.2⟩

theorem aliases {s t : State} (h : Extends s t) (route : Alias s a b) : Alias t a b := by
  induction route with
  | bounds x y => exact .bounds (boundsOne h x) (boundsOne h y)
  | forward x => exact .forward (h.equations x)
  | backward y => exact .backward (h.equations y)
  | trans _ _ l r => exact .trans l r

theorem congruent {s t : State} (h : Extends s t) (old : Congruent s a b) : Congruent t a b :=
  Congruent.rec
    (motive_1 := fun a b _ => Congruent t a b)
    (motive_2 := fun as bs _ => Arguments t as bs)
    (fun used => .variable (aliases h used))
    (fun _ ih => .primitive ih)
    (fun _ ih => .nominal ih)
    (fun _ _ ih jh => .record ih jh)
    (fun _ ih => .variant ih)
    (fun _ _ ih jh => .join ih jh)
    .nil
    (fun _ _ ih jh => .cons ih jh)
    old

theorem derives {s t : State} (h : Extends s t) (old : Derives s a b) : Derives t a b :=
  Derives.rec
    (motive_1 := fun a b _ => Derives t a b)
    (motive_2 := fun as bs _ => Forest t as bs)
    (fun row => .row (h.equations row))
    (fun used => .congruent (congruent h used))
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

theorem restrict {s t : State} (h : Extends s t) (m) (valid : Models t m) : Models s m :=
  ⟨⟨fun _ a => valid.1.1 _ (h.constraints a),fun _ a => valid.1.2 _ (h.intervals a)⟩,
    fun _ eq => valid.2 _ (h.equations eq)⟩

end Yulang.GeneralDeclarativeGrowth327
