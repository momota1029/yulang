import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466
import Yulang.GeneralDeclarativeI65I74NativeProducerPhaseOrigin465
import Yulang.GeneralDeclarativeI65I74ProjectionBatchInput464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466WrittenBinderCoordinates
open GeneralDeclarativeI65
open GeneralDeclarativeI65.I72.PreparedDeclarations463
open GeneralDeclarativeI65.I72.Checker408 (Problem)
open GeneralDeclarativeI65.I72.NamedProjection464 (exactOrdinaryState exact_ordinary_snapshot_iff)
open GeneralDeclarativeI65.I72.NativeProducer465
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeNestedView332 (Sources)
open CommonRecursiveNominalIntervals (Endpoint)
open Core.PresenceGeneration (TyTerm)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeOrder362 (node)
open GeneralDeclarativeWitnessNativeInstall360 (interpreted)
open GeneralDeclarativeI65.I72 (FitsFull)

structure SuppliedNativePlacement where
  value : Endpoint Nat
  write : Write
  originOrdinal : Nat

/-- Compare *independently supplied* native phase/value/full write with an
ordinary output receipt. A successful check uses existing release and origin
records; it never creates them or claims a connection merely from a term's
denotation. Use the soundness theorem only with an authentic receipt. -/
def checkCapturePlacement {s : State} (active : CheckedPhase s)
    (r : OldCaptureReceipt) (held : SuppliedNativePlacement) : Bool :=
  exactOrdinaryState r.after s.current.ordinary &&
    decide (r.target = held.write.address.target) &&
    matchesNode held.write.code held.value &&
    checkPhaseOrigin active held.write r.target held.originOrdinal

def ExactSuppliedCapturePlacement {s : State} (active : CheckedPhase s)
    (r : OldCaptureReceipt) (held : SuppliedNativePlacement) : Prop :=
  r.after = s.current.ordinary ∧ r.target = held.write.address.target ∧
    node held.write.code = held.value ∧ PhaseOriginAt active held.write r.target held.originOrdinal

theorem comparison_with_the_existing_issued_phase_is_exact
    {s : State} (active : CheckedPhase s) (r : OldCaptureReceipt) (held : SuppliedNativePlacement) :
    checkCapturePlacement active r held = true ↔ ExactSuppliedCapturePlacement active r held := by
  simp only [checkCapturePlacement,ExactSuppliedCapturePlacement,Bool.and_eq_true,
    exact_ordinary_snapshot_iff,decide_eq_true_eq,checked_compiler_node_recovers_exact_endpoint,
    finite_phase_origin_check_iff_literal_placed_active_row]
  constructor
  · rintro ⟨⟨⟨s,t⟩,n⟩,p⟩
    exact ⟨s,t,n,p⟩
  · rintro ⟨s,t,n,p⟩
    exact ⟨⟨⟨s,t⟩,n⟩,p⟩

/-- The old compile and the separately supplied phase refer to the same
post ordinary state and the same actual physical target in every *post*
fit. There is no transport of all source models through a fresh-slot
extension. The payload spelling remains separately supplied. -/
theorem an_authentic_capture_and_existing_placement_share_the_same_post_model
    (p : Problem) (tab : CheckedTable p.state.core.current)
    {done : Nat → Prop} {old : Supported (ordinary p) done}
    (idx : Sources (restriction old)) (addr : HeadAddress) (keep : List Nat) (job : Nat)
    (r : CheckedCaptureHead p tab)
    (receipt : readCaptureFromReadyHead p tab idx addr keep job = some r)
    {post : GeneralDeclarativeI65.I72.FullState} (active : CheckedPhase post.base.core)
    (placement : SuppliedNativePlacement)
    (check : checkCapturePlacement active r.allocated placement = true)
    (m : Model) (fit : FitsFull post m) :
    post.base.core.current.ordinary.equations[r.allocated.rawOrdinal]? =
      some ⟨r.allocated.target,r.allocated.captured.term⟩ ∧
    post.base.core.origins[placement.originOrdinal]? = some (originalOfWrite placement.write) ∧
    OriginRoute post.base.core (originalOfWrite placement.write) r.allocated.target ∧
    m.nativeSyntax r.allocated.target = some placement.value ∧
    interpreted active.world.board m.assignment r.allocated.target =
      some (placement.write.code.eval m.assignment) := by
  obtain ⟨raw,target,spelled,atPhase⟩ := (comparison_with_the_existing_issued_phase_is_exact ..).mp check
  have place := ready_head_receipt_preserves_actual_source_identity_and_physical_coordinate
    p tab idx addr keep job r receipt
  have semantics := actual_phase_origin_ordinal_and_native_view_hold_in_every_same_fit
    ((finite_phase_origin_check_iff_literal_placed_active_row ..).mpr atPhase) m fit.1
  refine ⟨raw ▸ place.2.2.1,atPhase.1,atPhase.2.1,?_,?_⟩
  · rw [target,←spelled]
    exact semantics.1
  · rw [target]
    exact semantics.2

theorem no_existing_native360_placement_has_a_nonvariable_ordinary_payload
    {s : State} (active : CheckedPhase s) (r : OldCaptureReceipt) (held : SuppliedNativePlacement)
    (term : TyTerm Nat) (nonvariable : ∀ j, term ≠ .var j)
    (literal : held.value = .ordinary term) :
    checkCapturePlacement active r held = false := by
  cases found : checkCapturePlacement active r held with
  | false => rfl
  | true =>
    have bad := (comparison_with_the_existing_issued_phase_is_exact ..).mp found
    exact False.elim (concrete_nonvariable_ordinary_source_is_never_native360_emission
      held.write.code term nonvariable (bad.2.2.1.trans literal))

end Yulang.C466WrittenBinderCoordinates
