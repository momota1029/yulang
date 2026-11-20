import Yulang.GeneralRebaseReceiptRawProduct289

/-! Exactly the reachable product stages for the real pair of source
fixtures. The raw component is always one of its old reachable states. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseReceiptScopedTrace289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptWire289
open GeneralRebaseReceiptFixture289 (wire request initial_no_producer endpoint_decision)
open GeneralRebaseReceiptMachine289 (Phase tick run)
open GeneralRebaseReceiptRawProduct289 (Config Next initial aux)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)

inductive Family (choice : Bool) : Config → Prop
  | start : Family choice initial
  | earlyDenied : Family choice ⟨before,.stopped (.denied .missingProducer)⟩
  | afterScan : Family choice ⟨after choice,.scan⟩
  | received : choice = true → Family choice ⟨after choice,.received (request choice)⟩
  | published : choice = true → Family choice ⟨after choice,.published (request choice)⟩
  | stillPending : choice = false → Family choice ⟨after choice,.stopped (.denied .unfinished)⟩

theorem initial_tick (choice : Bool) : tick (wire choice before) (request choice) .scan =
    some (.stopped (.denied .missingProducer)) := by
  simp [tick,initial_no_producer]

theorem endpoint_scan (choice : Bool) : tick (wire choice (after choice)) (request choice) .scan =
    some (if choice then .received (request choice) else .stopped (.denied .unfinished)) := by
  cases choice <;> simp [tick,endpoint_decision]

theorem endpoint_received (choice : Bool) (positive : choice = true) :
    tick (wire choice (after choice)) (request choice) (.received (request choice)) =
    some (.published (request choice)) := by
  subst choice
  simp [tick,endpoint_decision]

theorem scanned (choice : Bool) : Next choice initial ⟨after choice,.scan⟩ :=
  .raw before (after choice) .scan (GeneralRebaseRowParentStep287.actual_step choice)

theorem side_closed (choice : Bool) {s : State roles} {p q : Phase}
    (prior : Family choice ⟨s,p⟩)
    (edge : tick (wire choice s) (request choice) p = some q) : Family choice ⟨s,q⟩ := by
  cases prior with
  | start =>
    rw [initial_tick] at edge
    cases Option.some.inj edge
    exact .earlyDenied
  | earlyDenied => cases edge
  | afterScan =>
    rw [endpoint_scan] at edge
    cases Option.some.inj edge
    cases choice
    · exact .stillPending rfl
    · exact .received rfl
  | received positive =>
    rw [endpoint_received choice positive] at edge
    cases Option.some.inj edge
    exact .published positive
  | published _ => cases edge
  | stillPending _ => cases edge

theorem raw_closed (choice : Bool) {s t : State roles} {p : Phase}
    (prior : Family choice ⟨s,p⟩)
    (edge : Step (registry choice) root s t) : Family choice ⟨t,.scan⟩ := by
  cases prior with
  | start =>
    rw [GeneralRebaseRowActualPaths287.only_before choice t edge]
    exact .afterScan
  | earlyDenied =>
    rw [GeneralRebaseRowActualPaths287.only_before choice t edge]
    exact .afterScan
  | afterScan => exact (GeneralRebaseRowClosure287.no_step choice t edge).elim
  | received _ => exact (GeneralRebaseRowClosure287.no_step choice t edge).elim
  | published _ => exact (GeneralRebaseRowClosure287.no_step choice t edge).elim
  | stillPending _ => exact (GeneralRebaseRowClosure287.no_step choice t edge).elim

theorem closed (choice : Bool) {x y : Config} (prior : Family choice x) (edge : Next choice x y) :
    Family choice y := by
  cases edge with
  | raw _ _ _ old => exact raw_closed choice prior old
  | side _ _ _ one => exact side_closed choice prior one

theorem family_iff (choice : Bool) (s : Config) :
    B4Target.Steps (Next choice) initial s ↔ Family choice s := by
  constructor
  · intro path
    induction path with
    | refl => exact .start
    | tail _ edge ih => exact closed choice ih edge
  · intro term
    have raw : B4Target.Steps (Next choice) initial ⟨after choice,.scan⟩ := .tail .refl (scanned choice)
    cases term with
    | start => exact .refl
    | earlyDenied => exact .tail .refl (.side before .scan _ (initial_tick choice))
    | afterScan => exact raw
    | received positive =>
      have h := endpoint_scan choice
      rw [positive] at h raw ⊢
      exact .tail raw (.side (after true) .scan _ h)
    | published positive =>
      have h := endpoint_scan choice
      rw [positive] at h raw ⊢
      exact .tail (.tail raw (.side (after true) .scan _ h))
        (.side (after true) _ _ (endpoint_received true rfl))
    | stillPending negative =>
      have h := endpoint_scan choice
      rw [negative] at h raw ⊢
      exact .tail raw (.side (after false) .scan _ h)

def finalPhase (choice : Bool) : Phase :=
  if choice then .published (request choice) else .stopped (.denied .unfinished)

theorem terminal_config (choice : Bool) (s : Config) :
    (B4Target.Steps (Next choice) initial s ∧ (∀ t, ¬ Next choice s t)) ↔
    s = ⟨after choice,finalPhase choice⟩ := by
  constructor
  · rintro ⟨path,halt⟩
    have h := (family_iff choice s).mp path
    cases h with
    | start => exact (halt _ (scanned choice)).elim
    | earlyDenied =>
      exact (halt _ (.raw before (after choice) _ (GeneralRebaseRowParentStep287.actual_step choice))).elim
    | afterScan => exact (halt _ (.side (after choice) .scan _ (endpoint_scan choice))).elim
    | received pos => exact (halt _ (.side (after choice) _ _ (endpoint_received choice pos))).elim
    | published pos => simp [finalPhase,pos]
    | stillPending neg => simp [finalPhase,neg]
  · rintro rfl
    refine ⟨(family_iff choice _).mpr ?_,?_⟩
    · cases choice
      · exact .stillPending rfl
      · exact .published rfl
    · apply (GeneralRebaseReceiptRawProduct289.terminal_iff choice _).mpr
      refine ⟨GeneralRebaseRowClosure287.no_step choice,?_⟩
      cases choice <;> rfl

end Yulang.GeneralRebaseReceiptScopedTrace289
