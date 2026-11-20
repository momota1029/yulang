import Yulang.GeneralDeferredLadderCompiler302
import Yulang.GeneralGeneratedDictionaryScope299

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeferredLadderAvailability302
open GeneralObservedLadderRoute301
open GeneralDeferredLadderLedger302
open GeneralDeferredLadderAdvance302 (run)
open GeneralDeferredLadderPlan302 (compiled)
open GeneralDeferredLadderStage302 (frame stage_children)
open GeneralDeferredLadderOnlyInstall302 (raw_hit inner_frame not_prepared_at_leaf)
open GeneralDeferredLadderFrames302 (replay replay_frame replay_children)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Instance)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload PayloadEvidence payload_iff_erased)
open GeneralGeneratedDictionaryScope299 (all_left)

theorem not_recorded (p : Phase n k) (i : Nat) (future : k < i) (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry p.state m (focus n i) d := by
  intro got
  have seen : PayloadEvidence (Instance compiled p.state.core m) (focus n i) d :=
    (payload_iff_erased _ _ _).mpr got
  cases seen with
  | node instance' _ =>
    obtain ⟨q,found⟩ := instance'
    obtain ⟨j,earlier,eq⟩ := raw_hit p _ found.frame.raw_recorded
    have same : focus n i = focus n j := found.frame.occurrence_eq.symm.trans eq
    have eq := injective n (congrArg (fun o => o.identity) same)
    omega

theorem unobserved_empty (n k : Nat) (cap : k ≤ n+1) (m : Assignment)
    (i : Nat) (atPhase : i ≤ k) (d : Payload) :
    ¬ (boundary roles).Evidence registry (run n k (by omega)).state m (focus n i) d := by
  let p := run n k (by omega)
  have noneAt (remaining : Nat) (j : Nat) (distance : k-j = remaining) (before : j ≤ k) (d' : Payload) :
      ¬ (boundary roles).Evidence registry p.state m (focus n j) d' := by
    induction remaining generalizing j d' with
    | zero =>
      have same : j = k := by omega
      subst j
      intro got
      have seen : PayloadEvidence (Instance compiled p.state.core m) (focus n k) d' :=
        (payload_iff_erased _ _ _).mpr got
      cases seen with
      | node instance' proofs =>
        obtain ⟨q,cert⟩ := instance'
        by_cases below : k ≤ n
        · have same := inner_frame p k below cert.frame (frame p below) rfl rfl rfl
          cases same
          have branches := cert.children_eq.trans (stage_children p below)
          rw [branches] at proofs
          obtain ⟨d,proof⟩ := all_left proofs (focus n (k+1)) (List.mem_singleton_self _)
          exact not_recorded p (k+1) (by omega) m d ((payload_iff_erased _ _ _).mp proof)
        · have last : k = n+1 := by omega
          subst k
          exact not_prepared_at_leaf p _ cert.frame.visible cert.frame.role_eq cert.frame.prepared
    | succ rem ih =>
      intro got
      have seen : PayloadEvidence (Instance compiled p.state.core m) (focus n j) d' :=
        (payload_iff_erased _ _ _).mpr got
      cases seen with
      | node instance' proofs =>
        obtain ⟨q,cert⟩ := instance'
        have past : j < k := by omega
        have same := inner_frame p j (by omega) cert.frame (replay_frame n k (by omega) j past) rfl rfl rfl
        cases same
        have branches := cert.children_eq.trans (replay_children p j (by omega))
        rw [branches] at proofs
        obtain ⟨d,proof⟩ := all_left proofs (focus n (j+1)) (List.mem_singleton_self _)
        exact ih (j+1) (by omega) (by omega) d ((payload_iff_erased _ _ _).mp proof)
  exact noneAt (k-i) i rfl atPhase d

theorem no_root_evidence (n k : Nat) (cap : k ≤ n+1) (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry (run n k cap).state m displayRoot d :=
  unobserved_empty n k cap m 0 (Nat.zero_le _) d

end Yulang.GeneralDeferredLadderAvailability302
