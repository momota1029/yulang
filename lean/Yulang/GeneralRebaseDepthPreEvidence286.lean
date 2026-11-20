import Yulang.GeneralRebaseDepthSimulation286

/-! A prepared but uncommitted leaf can already give conditional raw evidence
for a complete assignment which satisfies its output. This is not a
statement of unconditional coverage of the pre-install model set. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthPreEvidence286
open GeneralDictionaryOutputDepth252 (roles registry root initial plan)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseDepthGroundModels285 (InitialTypeCheck FinalTypeCheck)
open GeneralRebaseDepthPhase286 (Pre Post)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPrePlan286 (unrelated_output packet_holds)
open GeneralRebaseDepthPreInstall286 (unique_located)
open GeneralRebaseDepthPathKeep285 (of_frame)

theorem exact_before {s : State roles} (pre : Pre s) (m : Assignment) (payload : Payload) :
    Evidence registry s.core m root payload ↔ FinalTypeCheck m ∧ payload = .node 0 [] := by
  obtain ⟨p,v⟩ := pre.plan
  constructor
  · intro evidence
    have erased := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr evidence
    cases erased with
    | node details ordered =>
      obtain ⟨q,cert⟩ := details
      have eq := unique_located pre.anchor (of_frame cert.frame) (of_frame v.frame)
      subst q
      have raw := v.frame.context_eq ▸ cert.packet.1
      have out := (v.outputs m).mp cert.packet.2.2
      have final := (unrelated_output m).mp ⟨(pre.anchor.rawModels m).mp raw,out⟩
      rw [cert.children_eq,v.leaf] at ordered
      cases ordered
      exact ⟨final,congrArg (fun i => CommonRoleOutermostResolver.Dictionary.node i [])
        (cert.frame.key_eq.symm.trans v.frame.key_eq)⟩
  · rintro ⟨final,rfl⟩
    obtain ⟨source,output⟩ := (unrelated_output m).mpr final
    exact GeneralNominalVersionedEvidence231.evidence_leaf
      ⟨p,GeneralNominalVersionedEvidence231.certificate_of_semantics v.frame v.leaf.symm
        (packet_holds pre.anchor v m source output) v.ready (v.class_of_output m output)⟩

theorem same_joint_everywhere {s : State roles} {n : Nat} (path : ActualPath initial s n)
    (m : Assignment) (payload : Payload) :
    Models s m ∧ Evidence registry s.core m root payload ↔ FinalTypeCheck m ∧ payload = .node 0 [] := by
  rcases GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) path with pre|post
  · have before := exact_before pre m payload
    exact ⟨fun both => before.mp both.2,
      fun final => ⟨(pre.anchor.models m).mpr final.1.1,before.mpr final⟩⟩
  · exact GeneralRebaseDepthPostQueries286.concrete post m payload

theorem pre_noncoverage {s : State roles} (pre : Pre s) :
    ∃ m, Models s m ∧ ∀ p, ¬ Evidence registry s.core m root p := by
  let m := GeneralDictionaryOutputDepthInstall252.smallModel
  have raw := GeneralDictionaryOutputDepthInstall252.small_source
  refine ⟨m,(pre.anchor.models _).mpr ((GeneralRebaseDepthGroundModels285.source_inputs _).mp raw),?_⟩
  intro p cert
  exact GeneralRebaseDepthMinimal285.scalar_ne_output ((exact_before pre m p).mp cert).1.2

end Yulang.GeneralRebaseDepthPreEvidence286
