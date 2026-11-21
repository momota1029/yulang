import Yulang.GeneralPositiveForkCurrentRead309
import Yulang.GeneralSelectedReadEvidence309
import Yulang.GeneralCommittedReadErasure309
import Yulang.GeneralOrderedDictionaryFault309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26800
set_option maxHeartbeats 15000000
namespace Yulang.GeneralPositiveForkVerified309
open GeneralPositiveForkSource309 (registry compiled root checked associated)
open GeneralPositiveForkInstall309 (after reachable inhabited)
open GeneralPositiveForkNodes309 (focus exact_frame)
open GeneralPositiveForkEvidence309 (payload parentPlan)
open GeneralPositiveForkCompiler309 (read decode lookup_row projected_children)
open GeneralPositiveForkBefore309 (initial_tree)
open GeneralPositiveForkCheck309 (accepted read_root short_fuel reversed_error duplicate_error)
open GeneralPositiveForkCurrentRead309 (readAt after_table initial_error)
open GeneralSelectedReadEvidence309 (SelectedRead)
open GeneralCommittedReadTrace309 (Trace)
open GeneralCommittedReadAddress309 (here)
open GeneralCommittedReadErasure309 (erase)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Certificate)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)
open GeneralDictionaryReadback (Payload)
open GeneralOrderedDictionaryCheck309 (validate)
open GeneralOrderedDictionaryFault309 (Explains)
open GeneralNominalCenters (Plan)

theorem certified_reader : SelectedRead registry after read decode := by
  intro i row hit
  have commit := GeneralPositiveForkSettlement309.committed_read i row hit
  obtain ⟨n,rfl,rfl⟩ := lookup_row i row hit
  simp only [GeneralPositiveForkCompiler309.decode_encode,projected_children] at commit ⊢
  exact ⟨commit,GeneralPositiveForkSelection309.safe n,
    GeneralPositiveForkSelection309.unique n,GeneralPositiveForkSelection309.no_merged n⟩

theorem checked_selected (fuel : Nat) (d : Payload) (ok : validate (readAt after) fuel 0 d = .ok ()) :
    B4TargetV8.Classify (boundary roles) registry after root (.selected d) ∧
    ∀ m, Models after m → Trace registry after root m read decode 0 d ∧
      (boundary roles).Evidence registry after m root d := by
  rw [after_table] at ok
  exact GeneralSelectedReadEvidence309.selected_checker ⟨rfl,checked⟩ reachable read decode certified_reader
    ⟨_,inhabited⟩ fuel 0 d .root ok

theorem certificates_for_every_model (m : Assignment) (valid : Models after m) :
    ∃ p : Plan roles, Certificate compiled after.core m root 1 [focus .low,focus .high] p ∧
      GeneralDictionaryDefaultEvidence204.OutputWitness p m ⟨0,1⟩ := by
  have ran : validate (readAt after) 2 0 payload = .ok () := by
    rw [after_table]
    exact (accepted 2 payload).mpr ⟨by decide,rfl⟩
  have proof := ((checked_selected 2 payload ran).2 m valid).1
  obtain ⟨_,e,_,⟨hit,p,cert⟩,_⟩ := here proof
  have matchRow := Option.some.inj (hit.symm.trans read_root)
  subst e
  exact ⟨p,cert,cert.outputs _ (List.mem_singleton_self _)⟩

theorem only_explicit_body (m : Assignment) (valid : Models after m) :
    ∃ p : Plan roles, Certificate compiled after.core m root 1 [focus .low,focus .high] p ∧
      GeneralDictionaryAssociatedProvenance.Supplies roles p.packet.declaration 0 (.explicit associated) ∧
      GeneralNominalCenteredHeadMatEffects.compileBody p (.explicit associated) =
        some (.variable 0) ∧
      GeneralNominalCenteredHeadMatEffects.BodyHolds p 1 m (.explicit associated) := by
  obtain ⟨p,cert,witness⟩ := certificates_for_every_model m valid
  obtain ⟨body,supplied,_,realized⟩ := witness
  have same := exact_frame .parent cert.frame
  subst p
  have eq : body = .explicit associated := by
    cases supplied with
    | explicit q listed _ =>
      change q ∈ [associated] at listed
      cases List.mem_singleton.mp listed
      rfl
    | default _ missing _ =>
      exact False.elim (missing associated (List.mem_singleton_self _) rfl)
  subst body
  exact ⟨parentPlan,cert,supplied,rfl,realized⟩

theorem evidence_at_low (m : Assignment) (valid : Models after m) :
    (boundary roles).Evidence registry after m (focus .low) (.node 2 []) :=
  GeneralCommittedReadErasure309.evidence_at_address (GeneralPositiveForkCertifiedTrace309.exact_trace m valid).1
    GeneralPositiveForkAddresses309.left_path.1 GeneralPositiveForkAddresses309.left_path.2

theorem evidence_at_high (m : Assignment) (valid : Models after m) :
    (boundary roles).Evidence registry after m (focus .high) (.node 3 []) :=
  GeneralCommittedReadErasure309.evidence_at_address (GeneralPositiveForkCertifiedTrace309.exact_trace m valid).1
    GeneralPositiveForkAddresses309.right_path.1 GeneralPositiveForkAddresses309.right_path.2

theorem fuel_not_rejection :
    Explains read 1 0 payload (.child 0 0 (.fuel 1)) ∧
    ∃ m, Models after m ∧ (boundary roles).Evidence registry after m root payload :=
  ⟨GeneralOrderedDictionaryFault309.exact.mp short_fuel,_,inhabited,
    GeneralPositiveForkEvidence309.root_evidence _ inhabited⟩

end Yulang.GeneralPositiveForkVerified309
