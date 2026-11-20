import Yulang.GeneralRebaseRowActualPaths287

/-! EvidenceAt remains an implication over an already supplied child
certificate. It can hold for a raw-stable node whose child is pending and
which therefore has no complete dictionary. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 15200000
namespace Yulang.GeneralRebaseRowEvidenceAt287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowParentStep287 (actual_step generated)
open GeneralRebaseRowClosure287 (scope stable)
open GeneralRebaseRowLocal287 (selected_parent selected_child)
open GeneralRebaseRowAfterSafety287 (blocked_local)
open GeneralRebaseRowParentEvidence287 (instance_root)
open GeneralNominalVersionedMixedBoundary234 (boundary Local)

theorem evidence_at (choice : Bool) : B4SkeletonV8.EvidenceAt (boundary roles) (registry choice) (after choice) root := by
  intro m valid focus key children dictionaries reached _ _ selected supplied
  have visible := reached.elim Or.inl (scope choice)
  rcases visible with rfl|rfl
  · have same := B4TargetV8.local_functional selected (selected_parent choice)
    cases same
    exact GeneralNominalVersionedEvidence231.evidence_node (instance_root choice m valid) supplied
  · cases choice with
    | false =>
      have impossible := B4TargetV8.local_functional selected blocked_local
      cases impossible
    | true =>
      have same := B4TargetV8.local_functional selected selected_child
      cases same
      cases supplied
      exact GeneralRebaseRowWholeChild287.evidence m valid

theorem actual_children (choice : Bool) :
    ∀ focus key children,
      GeneralNominalSaturationState.Generated (after choice).core.erased.current root focus →
      Local (registry choice) (after choice) focus (.selected key children) →
      ∀ goal ∈ children, GeneralNominalSaturationState.Generated (after choice).core.erased.current root goal := by
  intro focus key children reached selected goal member
  rcases scope choice reached with rfl|rfl
  · cases B4TargetV8.local_functional selected (selected_parent choice)
    cases List.mem_singleton.mp member
    exact generated choice
  · cases choice with
    | false => cases B4TargetV8.local_functional selected blocked_local
    | true =>
      cases B4TargetV8.local_functional selected selected_child
      cases member

theorem stable_pending_without_dictionary :
    (boundary roles).Step (registry false) root before (after false) ∧
    (boundary roles).Stable (registry false) (after false) root ∧
    (boundary roles).Stable (registry false) (after false) (child false) ∧
    Local (registry false) (after false) (child false) .pending ∧
    B4SkeletonV8.EvidenceAt (boundary roles) (registry false) (after false) root ∧
    ∀ m, (boundary roles).Models (after false) m → ∀ p, ¬ (boundary roles).Evidence (registry false) (after false) m root p :=
  ⟨actual_step false,(stable false).1,(stable false).2,blocked_local,evidence_at false,
    GeneralRebaseRowPayloadExact287.blocked_root⟩

end Yulang.GeneralRebaseRowEvidenceAt287
