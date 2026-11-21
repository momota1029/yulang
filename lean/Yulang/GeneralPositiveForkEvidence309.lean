import Yulang.GeneralPositiveForkLeafFrame309
import Yulang.GeneralNominalVersionedInstalledEvidence233

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 13500000
namespace Yulang.GeneralPositiveForkEvidence309
open GeneralPositiveForkSource309 (root compiled registry checked parent)
open GeneralPositiveForkPlan309 (loSite hiSite kids ordered_children)
open GeneralPositiveForkInstall309 (after reachable inhabited)
open GeneralPositiveForkLeaf309 (Side site decl no_children)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence Instance)
open GeneralNominalVersionedInstallation231 (replayPlan replay_children)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)

abbrev parentPlan := replayPlan GeneralPositiveForkPlan309.plan

theorem parent_frame : Frame compiled after.core root parent.id parentPlan :=
  GeneralNominalVersionedInstalledEvidence233.frame rfl inhabited

theorem parent_children : GeneralNominalVersionedFrame231.children parentPlan.packet = kids :=
  (replay_children _).trans ordered_children

theorem parent_ready : GeneralNominalCenteredHeadMatEffects.Ready after.core root parentPlan :=
  GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reachable parent_frame

theorem parent_certificate (m : Assignment) (valid : Models after m) :
    Certificate compiled after.core m root parent.id kids parentPlan :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics parent_frame parent_children.symm
    (GeneralNominalVersionedInstalledEvidence233.replay_holds valid) parent_ready
    (GeneralNominalVersionedInstalledEvidence233.class_effects valid)

theorem output (m : Assignment) (valid : Models after m) :
    GeneralDictionaryDefaultEvidence204.OutputWitness parentPlan m ⟨0,1⟩ :=
  (parent_certificate m valid).outputs _ (List.mem_singleton_self _)

theorem alias_identity {a b : Nat} (alias : GeneralNominalSaturationState.Alias after.core.erased.current a b) :
    a = b := by
  induction alias with
  | refl => rfl
  | edge h => cases h
  | symm h ih => exact ih.symm
  | trans h k ih ih' => exact ih.trans ih'

theorem side_requests (side : Side) :
    GeneralNominalCenteredHeadOutputs.requests after.core (site side).occurrence = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro out valid
  obtain ⟨s,seen,alias,member⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp valid
  rw [GeneralPositiveForkInstall309.raw_sites] at seen
  simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with rfl|rfl|rfl
  · exact GeneralPositiveForkLeafFrame309.invocations side (alias_identity alias)
  · cases member
  · cases member

theorem leaf_ready (side : Side) : GeneralNominalCenteredHeadMatEffects.Ready after.core (site side).occurrence
    (GeneralPositiveForkLeaf309.plan side) :=
  GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reachable
    (GeneralPositiveForkLeafFrame309.frame side _ inhabited)

theorem leaf_certificate (side : Side) (m : Assignment) (valid : Models after m) :
    Certificate compiled after.core m (site side).occurrence (decl side).id [] (GeneralPositiveForkLeaf309.plan side) :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics
    (GeneralPositiveForkLeafFrame309.frame side m valid) (no_children side).symm
    (GeneralPositiveForkLeaf309.holds side m valid) (leaf_ready side)
    (GeneralRebaseDisplayFrame276.classes_empty (side_requests side) _ m)

theorem leaf_evidence (side : Side) (m : Assignment) (valid : Models after m) :
    Evidence compiled after.core m (site side).occurrence (.node (decl side).id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,leaf_certificate side m valid⟩

abbrev payload : Payload := .node 1 [.node 2 [],.node 3 []]

theorem root_evidence (m : Assignment) (valid : Models after m) :
    (boundary roles).Evidence registry after m root payload :=
  GeneralNominalVersionedEvidence231.evidence_node ⟨_,parent_certificate m valid⟩
    (.cons (leaf_evidence .low m valid) (.cons (leaf_evidence .high m valid) .nil))

theorem both_same_model (m : Assignment) (valid : Models after m) :
    GeneralDictionaryDefaultEvidence204.OutputWitness parentPlan m ⟨0,1⟩ ∧
    (boundary roles).Evidence registry after m loSite.occurrence (.node 2 []) ∧
    (boundary roles).Evidence registry after m hiSite.occurrence (.node 3 []) ∧
    (boundary roles).Evidence registry after m root payload :=
  ⟨output m valid,leaf_evidence .low m valid,leaf_evidence .high m valid,root_evidence m valid⟩

end Yulang.GeneralPositiveForkEvidence309
