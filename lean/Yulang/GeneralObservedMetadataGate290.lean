import Yulang.GeneralObservedMetadataClosure290

/-! A preflight for the old, exact-anchored receipt checker. Failure at the
finite metadata gate is distinct from pending type inspection. The gate
does not replace candidate preparation or fabricate a Frame. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralObservedMetadataGate290
open GeneralDeclarations (Registry Declaration)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCandidates (Context)
open GeneralNominalInspection (Interpretation Bounds)
open GeneralNominalVersionedJournal232 (State)
open GeneralObservedMetadataScope290 (coverage certify good_exact accepted_report)
open GeneralObservedMetadataReport290 (reportFrom report_actual)
open GeneralRebaseReceiptExtract289 (candidates)
open GeneralRebaseReceiptWire289 (Offer Decision)
open GeneralRebaseReceiptExactLink289 (Anchored boundedDecision accept_has_actual_anchor)

def context (s : State roles) : Context := s.core.erased.current.context

def footprint (r : Registry) (s : State roles) (focus : Occurrence roles) : List Nat :=
  coverage (context s).state (candidates r focus)

def preflight (r : Registry) (s : State roles) (focus : Occurrence roles) (candidate : Interpretation) :
    GeneralObservedMetadataScope290.Result :=
  let current := context s
  certify (footprint r s focus) current.state.constructors current.interpretation r.constructors candidate

inductive Outcome where
  | metadata (failure : GeneralObservedMetadataScope290.Result)
  | receipt (original : Decision)
  deriving DecidableEq, Repr

def gate (r : Registry) (s : State roles) (up down : Occurrence roles) (ask : Offer)
    (candidate : Interpretation) : Outcome :=
  match preflight r s down candidate with
  | .good => .receipt (boundedDecision r s up down ask)
  | issue => .metadata issue

theorem receipt_exact (r : Registry) (s : State roles) (up down : Occurrence roles) (ask : Offer)
    (candidate : Interpretation) (result : Decision) :
    gate r s up down ask candidate = .receipt result ↔
      preflight r s down candidate = .good ∧ boundedDecision r s up down ask = result := by
  unfold gate
  cases test : preflight r s down candidate <;> simp

theorem verified_report {r : Registry} {s : State roles} {down : Occurrence roles}
    {candidate : Interpretation} (good : preflight r s down candidate = .good)
    (d : Declaration) (visible : d ∈ r.declarations) (role : d.role = down.demand.role)
    (bounds : List (Bounds (context s).state)) :
    reportFrom (context s).state r.constructors candidate d bounds =
      GeneralNominalRecursiveCandidates.report (context s) d bounds := by
  have member : d ∈ candidates r down := by
    unfold candidates
    exact List.mem_filter.mpr ⟨visible,by simp [role]⟩
  rw [← report_actual]
  exact (accepted_report _ _ _ _ _ _ good d member bounds).symm

theorem ready_has_provenance {r : Registry} {s : State roles} {up down : Occurrence roles}
    {ask : Offer} {candidate : Interpretation} (ready : gate r s up down ask candidate = .receipt .ready) :
    Anchored r s up down ask ∧
      (∀ d ∈ r.declarations, d.role = down.demand.role →
      ∀ bounds : List (Bounds (context s).state),
      reportFrom (context s).state r.constructors candidate d bounds =
        GeneralNominalRecursiveCandidates.report (context s) d bounds) := by
  have separated := (receipt_exact _ _ _ _ _ _ _).mp ready
  exact ⟨accept_has_actual_anchor separated.2,
    fun d visible scope bounds => verified_report separated.1 d visible scope bounds⟩

end Yulang.GeneralObservedMetadataGate290
