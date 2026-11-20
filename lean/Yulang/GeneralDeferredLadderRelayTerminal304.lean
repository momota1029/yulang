import Yulang.GeneralDeferredLadderRelayAdvance304

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeferredLadderRelayTerminal304
open GeneralDeferredLadderRelay304 (ctx Relay refState synthetic_closed)
open GeneralDeferredLadderResnapshot304 (HeadView)
open GeneralDeferredLadderOperationalView304 (committed_iff frame_forward)
open GeneralDeferredLadderRawCase304 (closed_forward only_installs)
open GeneralDeferredLadderExact302 (RawStep)
open GeneralDeferredLadderRetargetFrames302 (endUnseen)
open GeneralObservedLadderJournalCompiler301 (table receipt)
open GeneralObservedLadderJournalRows301 (rawRow attached)
open GeneralObservedLadderEvidence301 (dictionary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)
open GeneralObservedLadderPlan301 (compiled)

theorem table_eq {a b : State roles} (ab : HeadView a b) : table a = table b := by
  have rows : rawRow a = rawRow b := by
    funext i
    unfold rawRow
    rw [ab.raw.sites]
  have linked : attached a = attached b := by
    funext i j
    unfold attached
    rw [rows,ab.raw.edges]
  funext i
  simp only [table,receipt,rows,linked]
  rw [ab.context]

theorem evidence_forward {a b : State roles} (ab : HeadView a b) (m : Assignment)
    (given : (boundary roles).Evidence registry a m o payload) :
    (boundary roles).Evidence registry b m o payload := by
  obtain ⟨tree,read,certs⟩ := given
  refine ⟨tree,read,GeneralSourceDictionaries.evidence_mono _ _ ?_ certs⟩
  intro node key children localCert
  obtain ⟨p,c⟩ := localCert
  exact ⟨p,⟨frame_forward ab.raw ab.context ab.centers c.frame,c.children_eq,c.packet,c.outputs⟩⟩

theorem halted {n s} (rel : Relay n (n+1) (Nat.le_refl _) s) (after : State roles) :
    ¬ RawStep s after := by
  intro step
  have raw : GeneralNominalVersionedMixedKernel234.Step compiled displayRoot s after := step
  obtain ⟨e,enabled,novel,_,_⟩ :=
    only_installs (closed_forward rel.view (synthetic_closed n (n+1) (Nat.le_refl _) rel)) raw
  have f := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq] at f
  exact novel ((committed_iff rel.view.raw e.plan).mp
    (GeneralDeferredLadderUniversalLeaf302.committed n (ctx s) rel.cert rel.known _
      (frame_forward rel.view.raw.symm rel.view.context.symm rel.view.centers.symm f)))

theorem exact_dictionary {n s} (rel : Relay n (n+1) (Nat.le_refl _) s) (fuel : Nat) :
    GeneralGeneratedDictionaryRun299.run (table s) fuel 0 =
      if n+1 < fuel then some (dictionary (n+1)) else none := by
  rw [← table_eq rel.view]
  exact GeneralDeferredLadderCompiler302.delayed_compile (endUnseen n) (ctx s) rel.cert rel.known fuel

theorem root_evidence {n s} (rel : Relay n (n+1) (Nat.le_refl _) s) (m : Assignment)
    (valid : Models s m) : (boundary roles).Evidence registry s m displayRoot (dictionary (n+1)) := by
  apply evidence_forward rel.view m
  have ev := GeneralDeferredLadderUniversalLeaf302.evidence n (ctx s) rel.cert rel.known
    (n+1) (Nat.le_refl _) m ((rel.view.raw.models m).mpr valid)
  change (boundary roles).Evidence registry (refresh (endUnseen n).state (ctx s)) m
    (GeneralObservedLadderRoute301.focus n 0) (dictionary (n+1))
  simpa only [Nat.sub_self] using ev

end Yulang.GeneralDeferredLadderRelayTerminal304
