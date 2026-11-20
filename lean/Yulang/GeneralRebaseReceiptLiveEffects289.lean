import Yulang.GeneralRebaseReceiptGuardedProduct289

/-! An alias-borne output prevents a new or replayed receipt from being
marked. Live class requests, unlike the sidecar stamp, are actual journal
data and are monotone along old raw Steps. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptLiveEffects289
open GeneralRebaseReceiptWire289 (Offer check)
open GeneralRebaseReceiptExtract289 (extract effectSummary)
open GeneralRebaseReceiptExtractLaws289 (Accepted no_effective_requests)
open GeneralRebaseReceiptMachine289 (Phase tick)
open GeneralRebaseReceiptCatalogue289 (boundedWire guarded agreement)
open GeneralRebaseReceiptGuardedProduct289 (guardedTick)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenteredHeadOutputs (requests)

variable {r : Registry} {s : State roles} {focus : Occurrence roles} {ask : Offer}

theorem filtered_accepts (taken : guarded r s focus ask = .ready) :
    Accepted r s focus ask := by
  let keys := GeneralRebaseReceiptCatalogue289.constructorKeys s.core.erased.current.context.state
  let restrict : GeneralRebaseReceiptWire289.Wire := { extract r s focus with
    producers := (s.effects.filter fun e : Effect roles =>
      agreement keys r.constructors e.registry.constructors).map effectSummary }
  have catalogNice : agreement keys r.constructors s.core.erased.current.context.state.constructors = true :=
    (GeneralRebaseReceiptCatalogue289.agreement_exact ..).mpr
      (GeneralRebaseReceiptCatalogue289.guarded_provenance taken).1
  have packed : boundedWire r s focus = some restrict := by
    unfold boundedWire
    exact ite_eq_left catalogNice
  unfold guarded at taken
  rw [packed] at taken
  have fields := (GeneralRebaseReceiptWire289.check_ready ..).mp taken
  apply (GeneralRebaseReceiptWire289.check_ready ..).mpr
  refine ⟨fields.1,?_,fields.2.2⟩
  obtain ⟨p,present,keysMatch⟩ := fields.2.1
  change p ∈ (s.effects.filter _).map effectSummary at present
  obtain ⟨e,seen,equal⟩ := List.mem_map.mp present
  exact ⟨p,List.mem_map.mpr ⟨e,(List.mem_filter.mp seen).1,equal⟩,keysMatch⟩

theorem bounded_pub_implies_guard (p : Phase) (stamp : Offer)
    (published : guardedTick r s focus ask p = some (.published stamp)) :
    stamp = ask ∧ guarded r s focus ask = .ready := by
  unfold guardedTick at published
  cases reads : boundedWire r s focus with
  | none =>
    rw [reads] at published
    cases p <;> cases published
  | some w =>
    rw [reads] at published
    have h := (GeneralRebaseReceiptMachine289.published_exact w ask stamp p).mp published
    exact ⟨h.2.1,by unfold guarded; rw [reads]; exact h.2.2⟩

theorem actual_request_excludes_guard (out : GeneralSourceState.Output)
    (live : out ∈ requests s.core focus) : guarded r s focus ask ≠ .ready := by
  intro accepted
  rw [no_effective_requests (filtered_accepts accepted)] at live
  cases live

theorem cannot_publish_effectful (p : Phase) (stamp : Offer)
    (out : GeneralSourceState.Output) (live : out ∈ requests s.core focus) :
    guardedTick r s focus ask p ≠ some (.published stamp) :=
  fun published => actual_request_excludes_guard out live (bounded_pub_implies_guard p stamp published).2

theorem cannot_publish_after_any_raw_growth {last : State roles} {root : Occurrence roles} {registry : Registry}
    (trace : B4Target.Steps (Step registry root) s last)
    (out : GeneralSourceState.Output) (live : out ∈ requests s.core focus)
    (p : Phase) (stamp : Offer) :
    guardedTick r last focus ask p ≠ some (.published stamp) :=
  cannot_publish_effectful p stamp out ((GeneralRebaseSourceRequests264.steps_growth trace).requests focus out live)

end Yulang.GeneralRebaseReceiptLiveEffects289
