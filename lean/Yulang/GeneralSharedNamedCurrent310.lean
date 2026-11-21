import Yulang.GeneralSharedNamedMerge310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralSharedNamedCurrent310
open GeneralSharedNamedSource310 (root registry compiled checked impl leafBody)
open GeneralSharedNamedPlan310 (loSite hiSite z kids)
open GeneralSharedNamedInstall310 (after)
open GeneralSharedNamedEvidence310 (parentPlan parent_frame parent_children leaf_certificate siblings_different)
open GeneralSharedNamedLeaf310 (Side site decl named_requests sharing_scalar)
open GeneralSharedNamedMerge310 (merged added reached inhabited supported after_context root_not_alias_child)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence)
open GeneralNominalVersionedTransport231 (extendedPlan)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff EqualOutputs)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_refl)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCenters (Plan)
open GeneralDictionaryReadback (Payload)

abbrev advance (old : Plan roles) := extendedPlan [] added [] old
abbrev parent := advance parentPlan
abbrev receiver (side : Side) := advance (GeneralSharedNamedLeaf310.plan side)

theorem raw_same : merged.core.erased.current.sites = after.core.erased.current.sites := rfl
theorem centers_same : merged.core.sites = after.core.sites := rfl

theorem holds (m : Assignment) (old : Plan roles)
    (past : Holds old m) : Holds (advance old) m :=
  (GeneralNominalVersionedTransport231.holds_iff [] added [] old m).mpr
    ⟨past,GeneralSharedNamedMerge310.added_model m⟩

theorem revalidate {old : Plan roles} (framed : Frame compiled after.core demand key old)
    (witness : Holds old GeneralNominalExamples.model) :
    Frame compiled merged.core demand key (advance old) :=
  GeneralVersionedOrdinaryFrame310.revalidate framed added (framed.context_eq.symm ▸ supported)
    after_context (raw_same ▸ List.Subset.refl _) (centers_same ▸ List.Subset.refl _)
    _ (holds _ old witness)

theorem current_parent : Frame compiled merged.core root impl.id parent :=
  revalidate parent_frame (GeneralNominalVersionedInstalledEvidence233.replay_holds GeneralSharedNamedInstall310.inhabited)

theorem current_leaf (side : Side) : Frame compiled merged.core (site side).occurrence (decl side).id (receiver side) :=
  revalidate (GeneralSharedNamedLeafFrame310.frame side _ GeneralSharedNamedInstall310.inhabited)
    (GeneralSharedNamedLeaf310.holds side _ GeneralSharedNamedInstall310.inhabited)

theorem parent_certificate (m : Assignment) (valid : Models merged m) :
    Certificate compiled merged.core m root impl.id kids parent := by
  have prior := (GeneralSharedNamedMerge310.models m).mp valid
  have recorded := GeneralNominalVersionedInstalledEvidence233.class_effects prior
  have newClass : GeneralNominalVersionedEffects231.ClassEffects merged.core root parentPlan m :=
    (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun out => (GeneralSharedNamedMerge310.request_root_iff out).symm)).mp recorded
  have moved := (GeneralNominalVersionedReplayEffects232.class_effects_iff [] added []
    merged.core root parentPlan m).mpr newClass
  apply GeneralNominalVersionedEvidence231.certificate_of_semantics current_parent ?_
    (holds m parentPlan (GeneralNominalVersionedInstalledEvidence233.replay_holds prior))
    (GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reached current_parent) moved
  change kids = GeneralNominalVersionedFrame231.children (GeneralNominalVersionedTransport231.extendedPacket [] added [] parentPlan.packet)
  rw [GeneralNominalVersionedTransport231.children_eq,parent_children]

theorem receiver_request (side : Side) (out : GeneralSourceState.Output)
    (seen : out ∈ requests merged.core (site side).occurrence) : out = ⟨1,z⟩ := by
  obtain ⟨s,present,alias,member⟩ := mem_requests_iff.mp seen
  rw [raw_same,GeneralSharedNamedInstall310.raw_sites] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · exact False.elim (GeneralSharedNamedLeafFrame310.invocations side (root_not_alias_child (.symm alias)))
  · change out ∈ loSite.occurrence.demand.outputs at member
    exact List.mem_singleton.mp (named_requests .low ▸ member)
  · change out ∈ hiSite.occurrence.demand.outputs at member
    exact List.mem_singleton.mp (named_requests .high ▸ member)

theorem receiver_classes (side : Side) (m : Assignment) (valid : Models merged m) :
    GeneralNominalVersionedEffects231.ClassEffects merged.core (site side).occurrence (receiver side) m := by
  have past := (GeneralSharedNamedMerge310.models m).mp valid
  constructor
  · intro out member body found
    cases receiver_request side out member
    have eq : body = .explicit leafBody := (Option.some.inj found).symm
    subst body
    intro atom seen
    cases List.mem_singleton.mp seen
    exact sharing_scalar m past
  · intro a ma b mb same
    cases receiver_request side a ma
    cases receiver_request side b mb
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem receiver_certificate (side : Side) (m : Assignment) (valid : Models merged m) :
    Certificate compiled merged.core m (site side).occurrence (decl side).id [] (receiver side) := by
  have current := current_leaf side
  have prior := (GeneralSharedNamedMerge310.models m).mp valid
  refine GeneralNominalVersionedEvidence231.certificate_of_semantics current ?_
    (holds m _ (GeneralSharedNamedLeaf310.holds side m prior))
    (GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reached current) (receiver_classes side m valid)
  change [] = GeneralNominalVersionedFrame231.children (GeneralNominalVersionedTransport231.extendedPacket [] added [] (GeneralSharedNamedLeaf310.packet side))
  rw [GeneralNominalVersionedTransport231.children_eq,GeneralSharedNamedLeaf310.no_children]

theorem root_evidence (m : Assignment) (valid : Models merged m) :
    (boundary roles).Evidence registry merged m root GeneralSharedNamedEvidence310.payload :=
  GeneralNominalVersionedEvidence231.evidence_node ⟨_,parent_certificate m valid⟩
    (.cons (GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,receiver_certificate .low m valid⟩)
     (.cons (GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,receiver_certificate .high m valid⟩) .nil))

end Yulang.GeneralSharedNamedCurrent310
