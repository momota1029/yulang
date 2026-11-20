import Yulang.GeneralRebaseReceiptRank289

/-! Labelled trace counts for the actual two-fixture product. The only
scheduling freedom is one optional pre-install auxiliary check. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 19500000
namespace Yulang.GeneralRebaseReceiptCounted289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptRawProduct289 (Config Next initial)
open GeneralRebaseReceiptScopedTrace289 (finalPhase initial_tick endpoint_scan endpoint_received)
open GeneralRebaseReceiptMachine289 (Phase tick)
open GeneralRebaseReceiptFixture289 (wire request)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)

inductive Trace (choice : Bool) : Config → Nat → Nat → Prop
  | start : Trace choice initial 0 0
  | raw (s t : State roles) (phase : Phase) :
      Trace choice ⟨s,phase⟩ r a → Step (registry choice) root s t →
      Trace choice ⟨t,.scan⟩ (r + 1) a
  | side (s : State roles) (p q : Phase) :
      Trace choice ⟨s,p⟩ r a → tick (wire choice s) (request choice) p = some q →
      Trace choice ⟨s,q⟩ r (a + 1)

inductive Counts (choice : Bool) : Config → Nat → Nat → Prop
  | start : Counts choice initial 0 0
  | earlyDenied : Counts choice ⟨before,.stopped (.denied .missingProducer)⟩ 0 1
  | afterScan (early : Nat) : early ≤ 1 → Counts choice ⟨after choice,.scan⟩ 1 early
  | received (early : Nat) : early ≤ 1 → choice = true →
      Counts choice ⟨after choice,.received (request choice)⟩ 1 (early + 1)
  | published (early : Nat) : early ≤ 1 → choice = true →
      Counts choice ⟨after choice,.published (request choice)⟩ 1 (early + 2)
  | pending (early : Nat) : early ≤ 1 → choice = false →
      Counts choice ⟨after choice,.stopped (.denied .unfinished)⟩ 1 (early + 1)

theorem counts {choice : Bool} {x : Config} {r a}
    (path : Trace choice x r a) : Counts choice x r a := by
  induction path with
  | start => exact .start
  | raw s t phase pathSoFar old ih =>
    cases ih with
    | start =>
      rw [GeneralRebaseRowActualPaths287.only_before choice t old]
      exact .afterScan 0 (by decide)
    | earlyDenied =>
      rw [GeneralRebaseRowActualPaths287.only_before choice t old]
      exact .afterScan 1 (by decide)
    | afterScan _ _ => exact (GeneralRebaseRowClosure287.no_step choice t old).elim
    | received _ _ _ => exact (GeneralRebaseRowClosure287.no_step choice t old).elim
    | published _ _ _ => exact (GeneralRebaseRowClosure287.no_step choice t old).elim
    | pending _ _ _ => exact (GeneralRebaseRowClosure287.no_step choice t old).elim
  | side s p q pathSoFar advance ih =>
    cases ih with
    | start =>
      rw [initial_tick] at advance
      cases Option.some.inj advance
      exact .earlyDenied
    | earlyDenied => cases advance
    | afterScan early bound =>
      rw [endpoint_scan] at advance
      cases Option.some.inj advance
      cases choice
      · exact .pending _ bound rfl
      · exact .received _ bound rfl
    | received early bound pos =>
      rw [endpoint_received choice pos] at advance
      cases Option.some.inj advance
      exact .published early bound pos
    | published _ _ _ => cases advance
    | pending _ _ _ => cases advance

theorem path_erases {choice : Bool} {x : Config} {r a} (path : Trace choice x r a) :
    B4Target.Steps (Next choice) initial x := by
  induction path with
  | start => exact .refl
  | raw s t p _ old ih => exact .tail ih (.raw s t p old)
  | side s p q _ edge ih => exact .tail ih (.side s p q edge)

theorem path_counts (choice : Bool) {x : Config} (path : B4Target.Steps (Next choice) initial x) :
    ∃ r a, Trace choice x r a := by
  induction path with
  | refl => exact ⟨0,0,.start⟩
  | tail _ edge ih =>
    obtain ⟨r,a,cert⟩ := ih
    cases edge with
    | raw s t p old => exact ⟨r+1,a,.raw s t p cert old⟩
    | side s p q next => exact ⟨r,a+1,.side s p q cert next⟩

theorem final_counts (choice : Bool) (r a : Nat)
    (trace : Trace choice ⟨after choice,finalPhase choice⟩ r a) :
    r = 1 ∧ ∃ early ≤ 1, a = early + (if choice then 2 else 1) := by
  have fact := counts trace
  cases choice
  · cases fact with
    | pending early bound _ => exact ⟨rfl,early,bound,rfl⟩
  · cases fact with
    | published early bound _ => exact ⟨rfl,early,bound,rfl⟩

theorem scan_with_exact_early (choice : Bool) (early : Nat) (bound : early ≤ 1) :
    Trace choice ⟨after choice,.scan⟩ 1 early := by
  have old := GeneralRebaseRowParentStep287.actual_step choice
  have cases : early = 0 ∨ early = 1 := by omega
  rcases cases with rfl | rfl
  · exact .raw before (after choice) .scan .start old
  · exact .raw before (after choice) _ (.side before .scan _ .start (initial_tick choice)) old

theorem every_final_count (choice : Bool) (early : Nat) (bound : early ≤ 1) :
    Trace choice ⟨after choice,finalPhase choice⟩ 1 (early + (if choice then 2 else 1)) := by
  have raw := scan_with_exact_early choice early bound
  cases choice
  · exact .side (after false) .scan _ raw (endpoint_scan false)
  · have first := Trace.side (after true) .scan _ raw (endpoint_scan true)
    exact .side (after true) (.received (request true)) _ first (endpoint_received true rfl)

theorem maximal_trace_counts (choice : Bool) (r a : Nat) :
    (∃ x, Trace choice x r a ∧ ∀ y, ¬ Next choice x y) ↔
      r = 1 ∧ ∃ early ≤ 1, a = early + (if choice then 2 else 1) := by
  constructor
  · rintro ⟨x,trace,halt⟩
    have final := (GeneralRebaseReceiptScopedTrace289.terminal_config choice x).mp ⟨path_erases trace,halt⟩
    exact final_counts choice r a (final ▸ trace)
  · rintro ⟨rfl,early,bound,rfl⟩
    refine ⟨⟨after choice,finalPhase choice⟩,every_final_count choice early bound,?_⟩
    exact ((GeneralRebaseReceiptScopedTrace289.terminal_config choice _).mpr rfl).2

end Yulang.GeneralRebaseReceiptCounted289
