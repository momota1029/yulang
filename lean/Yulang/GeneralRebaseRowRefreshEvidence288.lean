import Yulang.GeneralRebaseRowLeafLifetime288

/-! Ordinary V8 dictionary evidence survives every allowed refresh in the
guarded fixture. Fresh evidence on the entire original source slice does not. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseRowRefreshEvidence288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child plan sole_child)
open GeneralRebaseRowParentFrame287 (after at_role after_exact)
open GeneralRebaseRowLedger288 (supplemented models_eq)
open GeneralRebaseRowRefreshPackets288
open GeneralRebaseRowLeafLifetime288 (topOutput source_survives outside_snapshot no_fresh_leaf)
open GeneralRebaseNonleafCommitted276 (result refinement interpretation)
open GeneralNominalVersionedInstallation231 (replayPlan replay_children)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload payload_iff_erased)

variable {context : GeneralNominalCandidates.Context}

theorem parent_children (cert : Refresh supplemented context) :
    GeneralNominalVersionedFrame231.children (result root_frame cert).packet = [child true] :=
  (GeneralRebaseNonleafRetarget276.children_eq _ (refinement root_frame cert)
    (interpretation root_frame cert) parent_observed).trans ((replay_children _).trans (sole_child true))

theorem child_children (cert : Refresh supplemented context) :
    GeneralNominalVersionedFrame231.children (result child_frame cert).packet = [] :=
  (GeneralRebaseNonleafRetarget276.children_eq _ (refinement child_frame cert)
    (interpretation child_frame cert) child_observed).trans GeneralRebaseRowWholeChild287.no_children

theorem parent_ready (cert : Refresh supplemented context) :
    GeneralNominalCenteredHeadMatEffects.Ready (refresh supplemented context).core root (result root_frame cert) :=
  GeneralRebaseNonleafCommitted276.ready root_frame cert (GeneralRebaseRowParentEvidence287.requests_ready true)

theorem child_ready (cert : Refresh supplemented context) :
    GeneralNominalCenteredHeadMatEffects.Ready (refresh supplemented context).core (child true) (result child_frame cert) :=
  GeneralRebaseNonleafCommitted276.ready child_frame cert GeneralRebaseRowWholeChild287.ready

theorem root_evidence (cert : Refresh supplemented context) (m : Assignment)
    (valid : Models (refresh supplemented context) m) :
    Evidence (registry true) (refresh supplemented context).core m root (.node 0 [.node 1 []]) := by
  have parent := (GeneralRebaseNonleafCommitted276.committed root_frame cert parent_observed root_committed).1 m valid
  have leaf := (GeneralRebaseNonleafCommitted276.committed child_frame cert child_observed child_committed).1 m valid
  have parentPiece := GeneralNominalVersionedEvidence231.certificate_of_semantics (root_transported cert)
    (parent_children cert).symm parent.1 (parent_ready cert) parent.2
  have leafPiece := GeneralNominalVersionedEvidence231.certificate_of_semantics (child_transported cert)
    (child_children cert).symm leaf.1 (child_ready cert) leaf.2
  exact GeneralNominalVersionedEvidence231.evidence_node ⟨_,parentPiece⟩
    (.cons (GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,leafPiece⟩) .nil)

theorem only_child_payload (cert : Refresh supplemented context) (m : Assignment) (p : Payload)
    (held : Evidence (registry true) (refresh supplemented context).core m (child true) p) :
    p = .node 1 [] := by
  have tree := (payload_iff_erased ..).mpr held
  cases tree with
  | node details sub =>
    obtain ⟨packet,evidence⟩ := details
    have eq := same_plan evidence.frame (child_transported cert)
      (GeneralRebaseRowLocal287.child_at_role true _ evidence.frame.visible evidence.frame.role_eq)
    subst packet
    rw [evidence.children_eq,child_children cert] at sub
    cases sub
    exact congrArg (fun k => CommonRoleOutermostResolver.Dictionary.node k []) evidence.frame.key_eq.symm

theorem only_root_payload (cert : Refresh supplemented context) (m : Assignment) (p : Payload)
    (held : Evidence (registry true) (refresh supplemented context).core m root p) :
    p = .node 0 [.node 1 []] := by
  have tree := (payload_iff_erased ..).mpr held
  cases tree with
  | node details sub =>
    obtain ⟨packet,evidence⟩ := details
    have eq := same_plan evidence.frame (root_transported cert) (at_role true _ evidence.frame.visible evidence.frame.role_eq)
    subst packet
    rw [evidence.children_eq,parent_children cert] at sub
    cases sub with
    | cons one rest =>
      cases rest
      rw [only_child_payload cert m _ ((payload_iff_erased ..).mp one)]
      exact congrArg (fun k => CommonRoleOutermostResolver.Dictionary.node k [.node 1 []]) evidence.frame.key_eq.symm

theorem exact_payload (cert : Refresh supplemented context) (m : Assignment) (p : Payload) :
    Models (refresh supplemented context) m ∧ Evidence (registry true) (refresh supplemented context).core m root p ↔
    GeneralRebaseRowChildRaw287.OutputCheck m ∧ p = .node 0 [.node 1 []] := by
  have same : Models (refresh supplemented context) m ↔ GeneralRebaseRowChildRaw287.OutputCheck m :=
    (refresh_models cert).trans ((models_eq m).trans (after_exact true m))
  constructor
  · rintro ⟨valid,ev⟩
    exact ⟨same.mp valid,only_root_payload cert m p ev⟩
  · rintro ⟨checks,rfl⟩
    exact ⟨same.mpr checks,root_evidence cert m (same.mpr checks)⟩

theorem no_source_dictionary_at_mark (cert : Refresh supplemented context)
    (known : GeneralNominalState.Known context.state 2)
    (focus : GeneralSourceDictionaries.Occurrence roles) (p : Payload) :
    ¬ Evidence (registry true) (refresh supplemented context).core topOutput focus p := by
  intro claimed
  have erased := (payload_iff_erased ..).mpr claimed
  cases erased with
  | node instance' _ =>
    exact outside_snapshot cert known (GeneralNominalVersionedEvidence231.instance_models instance')

end Yulang.GeneralRebaseRowRefreshEvidence288
