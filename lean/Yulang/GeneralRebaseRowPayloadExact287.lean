import Yulang.GeneralRebaseRowParentEvidence287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 15000000
namespace Yulang.GeneralRebaseRowPayloadExact287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child plan sole_child)
open GeneralRebaseRowParentFrame287 (after after_exact)
open GeneralRebaseRowParentEvidence287 (only_root_plan evidence_root)
open GeneralRebaseRowChildRaw287 (OutputCheck)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedInstallation231 (replayPlan replay_children)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload payload_iff_erased)

theorem child_shape (m : Assignment) (p : Payload)
    (held : Evidence (registry true) (after true).core m (child true) p) :
    p = .node 1 [] := by
  have tree := (payload_iff_erased ..).mpr held
  cases tree with
  | node details sub =>
    obtain ⟨plan,f⟩ := details
    have d := f.frame.visible
    simp only [List.mem_cons,List.not_mem_nil,or_false] at d
    rcases d with wrong|correct
    · have impossible := f.frame.role_eq
      rw [wrong] at impossible
      cases impossible
    · have key := f.frame.key_eq
      rw [correct] at key
      have empty : GeneralNominalVersionedFrame231.children plan.packet = [] := by
        unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
        have noReq : plan.packet.declaration.requirements = [] := congrArg GeneralDeclarations.Declaration.requirements correct
        rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ noReq]
        rfl
      rw [f.children_eq,empty] at sub
      cases sub
      exact congrArg (fun k => CommonRoleOutermostResolver.Dictionary.node k []) key.symm

theorem only_payload (m : Assignment) (valid : Models (after true) m) (p : Payload)
    (given : Evidence (registry true) (after true).core m root p) :
    p = .node 0 [.node 1 []] := by
  have tree := (payload_iff_erased ..).mpr given
  cases tree with
  | node details childProofs =>
    obtain ⟨candidate,cert⟩ := details
    have eq := only_root_plan true m valid cert.frame
    subst candidate
    rw [cert.children_eq,replay_children,sole_child] at childProofs
    cases childProofs with
    | cons hd tl =>
      cases tl
      have payload := child_shape m _ ((payload_iff_erased ..).mp hd)
      rw [payload]
      exact congrArg (fun k => CommonRoleOutermostResolver.Dictionary.node k [.node 1 []]) cert.frame.key_eq.symm

theorem blocked_root (m : Assignment) (valid : Models (after false) m) (p : Payload) :
    ¬ Evidence (registry false) (after false).core m root p := by
  intro given
  have tree := (payload_iff_erased ..).mpr given
  cases tree with
  | node details childProofs =>
    obtain ⟨candidate,cert⟩ := details
    have eq := only_root_plan false m valid cert.frame
    subst candidate
    rw [cert.children_eq,replay_children,sole_child] at childProofs
    cases childProofs with
    | cons hd _ =>
      exact GeneralRebaseRowGeneratedChild287.no_child_evidence m _ ((payload_iff_erased ..).mp hd)

theorem exact (m : Assignment) (p : Payload) :
    Models (after true) m ∧ Evidence (registry true) (after true).core m root p ↔
      OutputCheck m ∧ p = .node 0 [.node 1 []] := by
  constructor
  · intro h
    exact ⟨(after_exact true m).mp h.1,only_payload m h.1 p h.2⟩
  · rintro ⟨checks,rfl⟩
    have h := (after_exact true m).mpr checks
    exact ⟨h,evidence_root m h⟩

theorem comparison (m : Assignment) (valid : Models (after true) m) :
    Models (after false) m ∧
      Evidence (registry true) (after true).core m root (.node 0 [.node 1 []]) ∧
      ∀ p, ¬ Evidence (registry false) (after false).core m root p := by
  have there := (after_exact false m).mpr ((after_exact true m).mp valid)
  exact ⟨there,evidence_root m valid,blocked_root m there⟩

end Yulang.GeneralRebaseRowPayloadExact287
