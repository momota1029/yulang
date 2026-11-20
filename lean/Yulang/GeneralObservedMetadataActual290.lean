import Yulang.GeneralObservedMetadataGate290
import Yulang.GeneralObservedMetadataControls290

/-! The refined check agrees with the old strict check on the actual old
raw paths. Only a synthetic metadata proposal is changed in the controls. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralObservedMetadataActual290
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseReceiptFixture289 (wire request initial_no_producer endpoint_decision)
open GeneralRebaseReceiptWitness289 (ActualPath)
open GeneralObservedMetadataGate290 (context preflight gate receipt_exact footprint)
open GeneralObservedMetadataScope290 (good_exact)
open GeneralObservedMetadataControls290 (primitiveOutside removeInvariant)
open GeneralNominalCandidates (Metadata Context)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseReceiptExactLink289 (boundedDecision)

theorem actual_tables (choice : Bool) {s : State roles} (path : ActualPath choice s) :
    (context s).state.constructors = (registry choice).constructors ∧
      (context s).interpretation = interp := by
  rcases GeneralRebaseRowActualPaths287.one_or_zero choice s path with rfl | rfl
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩

theorem actual_metadata (choice : Bool) {s : State roles} (path : ActualPath choice s) :
    Metadata (registry choice) (context s) := by
  obtain ⟨ctors,interpretation⟩ := actual_tables choice path
  refine ⟨ctors.symm,?_⟩
  rw [interpretation]
  intro key p h
  cases h

theorem preflight_good (choice : Bool) {s : State roles} (path : ActualPath choice s) :
    preflight (registry choice) s (child choice) interp = .good := by
  obtain ⟨ctors,interpretation⟩ := actual_tables choice path
  refine (good_exact ..).mpr ⟨fun key _ => ⟨congrFun ctors key,?_,?_⟩,?_⟩
  · rw [interpretation]
  · rw [interpretation]
  · intro key _ p conflict
    cases conflict

theorem strict_path_agrees (choice : Bool) {s : State roles} (path : ActualPath choice s) :
    gate (registry choice) s root (child choice) (request choice) interp =
      .receipt (GeneralRebaseReceiptWire289.check (wire choice s) (request choice)) := by
  refine (receipt_exact ..).mpr ⟨preflight_good choice path,?_⟩
  unfold boundedDecision
  rcases GeneralRebaseRowActualPaths287.one_or_zero choice s path with rfl | rfl
  · rw [GeneralRebaseReceiptAnchorFixture289.before_anchor_wire]
  · rw [GeneralRebaseReceiptAnchorFixture289.after_anchor_wire]

theorem exact_install_diagnostics (choice : Bool) :
    gate (registry choice) (after choice) root (child choice) (request choice) interp =
      .receipt (if choice then .ready else .unfinished) := by
  rw [strict_path_agrees choice (GeneralRebaseReceiptWitness289.after_reachable choice),
    endpoint_decision]

theorem exact_initial_diagnostic (choice : Bool) :
    gate (registry choice) before root (child choice) (request choice) interp = .receipt .missingProducer := by
  rw [strict_path_agrees choice .refl,initial_no_producer]

theorem observed_proposed_primitives_rejected :
    gate (registry true) (after true) root (child true) (request true)
      (GeneralObservedMetadataControls290.insertPrimitive interp 0 .pair) = .metadata .disagreement := by
  decide +kernel

theorem unobserved_wrong_proposed_primitive_does_not_block :
    gate (registry true) (after true) root (child true) (request true) primitiveOutside = .receipt .ready ∧
      ¬ Metadata (registry true) ⟨(context (after true)).state,primitiveOutside⟩ := by
  constructor
  · decide +kernel
  · intro assumption
    exact GeneralObservedMetadataControls290.equal_local_incompatible_outside.2 assumption

end Yulang.GeneralObservedMetadataActual290
