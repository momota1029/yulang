import Yulang.GeneralSharedNamedLeafFrame310
import Yulang.GeneralNominalVersionedInstalledEvidence233
import Yulang.GeneralVersionedOutputHandoff310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 13500000
namespace Yulang.GeneralSharedNamedEvidence310
open GeneralSharedNamedSource310 (root compiled registry checked impl leafBody associated)
open GeneralSharedNamedPlan310 (loSite hiSite kids ordered_children z)
open GeneralSharedNamedInstall310 (after reachable inhabited)
open GeneralSharedNamedLeaf310 (Side site decl no_children named_requests sharing_scalar)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence Instance)
open GeneralNominalVersionedInstallation231 (replayPlan replay_children)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonNominalFullCarrier (Equivalent subtype_refl)

abbrev parentPlan := replayPlan GeneralSharedNamedPlan310.plan

theorem parent_frame : Frame compiled after.core root impl.id parentPlan :=
  GeneralNominalVersionedInstalledEvidence233.frame rfl inhabited

theorem parent_children : GeneralNominalVersionedFrame231.children parentPlan.packet = kids :=
  (replay_children _).trans ordered_children

theorem parent_ready : GeneralNominalCenteredHeadMatEffects.Ready after.core root parentPlan :=
  GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reachable parent_frame

theorem parent_certificate (m : Assignment) (valid : Models after m) :
    Certificate compiled after.core m root impl.id kids parentPlan :=
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

theorem siblings_different : loSite.occurrence.identity ≠ hiSite.occurrence.identity := by
  decide +kernel

theorem side_request (side : Side) (out : GeneralSourceState.Output)
    (seen : out ∈ GeneralNominalCenteredHeadOutputs.requests after.core (site side).occurrence) :
    out = ⟨1,z⟩ := by
  obtain ⟨s,present,alias,member⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp seen
  rw [GeneralSharedNamedInstall310.raw_sites] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · exact False.elim (GeneralSharedNamedLeafFrame310.invocations side (alias_identity alias))
  · change out ∈ loSite.occurrence.demand.outputs at member
    exact List.mem_singleton.mp (named_requests .low ▸ member)
  · change out ∈ hiSite.occurrence.demand.outputs at member
    exact List.mem_singleton.mp (named_requests .high ▸ member)

theorem classes (side : Side) (m : Assignment) (valid : Models after m) :
    GeneralNominalVersionedEffects231.ClassEffects after.core (site side).occurrence
      (GeneralSharedNamedLeaf310.plan side) m := by
  constructor
  · intro out member body found
    cases side_request side out member
    have equal : body = .explicit leafBody := (Option.some.inj found).symm
    subst body
    intro atom seen
    cases List.mem_singleton.mp seen
    exact sharing_scalar m valid
  · intro a ma b mb same
    cases side_request side a ma
    cases side_request side b mb
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem leaf_ready (side : Side) : GeneralNominalCenteredHeadMatEffects.Ready after.core (site side).occurrence
    (GeneralSharedNamedLeaf310.plan side) :=
  GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reachable
    (GeneralSharedNamedLeafFrame310.frame side _ inhabited)

theorem leaf_certificate (side : Side) (m : Assignment) (valid : Models after m) :
    Certificate compiled after.core m (site side).occurrence (decl side).id [] (GeneralSharedNamedLeaf310.plan side) :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics
    (GeneralSharedNamedLeafFrame310.frame side m valid) (no_children side).symm
    (GeneralSharedNamedLeaf310.holds side m valid) (leaf_ready side)
    (classes side m valid)

theorem leaf_evidence (side : Side) (m : Assignment) (valid : Models after m) :
    Evidence compiled after.core m (site side).occurrence (.node (decl side).id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,leaf_certificate side m valid⟩

abbrev payload : Payload := .node 1 [.node 2 [],.node 2 []]

theorem root_evidence (m : Assignment) (valid : Models after m) :
    (boundary roles).Evidence registry after m root payload :=
  GeneralNominalVersionedEvidence231.evidence_node ⟨_,parent_certificate m valid⟩
    (.cons (leaf_evidence .low m valid) (.cons (leaf_evidence .high m valid) .nil))

theorem both_same_model (m : Assignment) (valid : Models after m) :
    GeneralDictionaryDefaultEvidence204.OutputWitness parentPlan m ⟨0,1⟩ ∧
    (boundary roles).Evidence registry after m loSite.occurrence (.node 2 []) ∧
    (boundary roles).Evidence registry after m hiSite.occurrence (.node 2 []) ∧
    (boundary roles).Evidence registry after m root payload :=
  ⟨output m valid,leaf_evidence .low m valid,leaf_evidence .high m valid,root_evidence m valid⟩

end Yulang.GeneralSharedNamedEvidence310
