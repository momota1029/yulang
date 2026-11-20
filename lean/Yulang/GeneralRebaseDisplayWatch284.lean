import Yulang.GeneralRebaseWatchValidatorSource284

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseDisplayWatch284
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseDisplayFrame276 (before classes_empty)
open GeneralRebaseCompiledDisplay277 (after effect parent compiled)
open GeneralRebaseCompiledChild277 (plan holds no_children)
open GeneralRebaseCompiledEvidence277 (child_frame ready)
open GeneralRebaseCompiledInstall277 (no_new_request)
open GeneralNominalVersionedInstallation231 (replayPlan replay_children)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (certificate_of_semantics)
open GeneralRebaseSliceEvidence283 (Evidence Local reads)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseHistoryOrder282 (history decode)
open GeneralRebaseWatchValidator284 (Compact Valid)
open GeneralRebaseWatchValidatorSource284 (candidate)
open GeneralRebaseActualWatch284 (Cache interpret)
open GeneralRebaseWatchJoint284 (Complete Query)
open GeneralNominalCommonBridge (Assignment)

noncomputable def family : List (GeneralNominalCenters.Plan roles) := [replayPlan parent,plan]

noncomputable def watch : List Nat := journalReads before ++ journalReads after ++ reads family

noncomputable def stored : Compact := ⟨0,watch,[]⟩

theorem history_empty : history before = [] := by
  unfold history
  change (GeneralPresenceOrderedSort247.sort (GeneralPresenceOrderedDedup247.dedup ([] : List (Nat × Core.PresenceGeneration.TyTerm Nat)))).getD [] = []
  simp [GeneralPresenceOrderedDedup247.dedup,GeneralPresenceOrderedSort247.sort,GeneralPresenceOrderedSort247.sortFuel]
theorem packet_empty : GeneralNominalVersionedAggregateLedger236.packetEntries effect.plan.packet = [] := by
  have binds : effect.plan.packet.bindings = [(0,(1,1))] := GeneralNominalNonleafPlan193.bindings
  unfold GeneralNominalVersionedAggregateLedger236.packetEntries
  rw [binds]
  change GeneralNominalVersionedAggregateRealization236.entries _ _ _ _ [0] = []
  rfl

theorem input_valid : Valid stored (history before) := by
  rw [history_empty]
  exact ⟨fun _ h => False.elim (List.not_mem_nil h),
    ⟨fun _ h => False.elim (List.not_mem_nil h),fun {_} h => h,
      fun _ h => False.elim (List.not_mem_nil h)⟩,List.Pairwise.nil⟩

theorem checker : candidate stored watch effect = some stored := by
  unfold candidate
  rw [packet_empty]
  have same : GeneralRebaseWatchValidator284.admits 0 watch watch = true :=
    (GeneralRebaseWatchValidator284.admissible 0 watch watch).mpr (fun _ seen => Or.inl seen)
  simp only [GeneralRebaseWatchValidator284.update,stored,same,
    GeneralRebaseWatchStep284.next,GeneralRebaseSortedCache283.push,GeneralRebaseFutureWatch284.trim,
    List.filter_nil,GeneralRebaseWatchValidator284.checkRows,List.all_nil,Bool.and_self,ite_true,
    GeneralRebaseWatchValidator284.high,List.foldl_nil]

theorem next_valid : Valid stored (history after) := by
  have record := GeneralNominalVersionedMixedSeedLedger237.reachable GeneralRebaseCachedFixtures283.Display.source_start
  exact (GeneralRebaseWatchValidatorSource284.candidate_valid input_valid record rfl checker).1

theorem parent_certificate (m : Assignment) (valid : Models after m) :
    Local family compiled after.core m displayRoot 1 [displayChild] := by
  let p := replayPlan parent
  refine ⟨p,List.mem_cons_self,certificate_of_semantics
    (GeneralNominalVersionedInstalledEvidence233.frame rfl valid) ?_
    (GeneralNominalVersionedInstalledEvidence233.replay_holds valid) (ready p)
    (classes_empty (no_new_request displayRoot) p m)⟩
  exact ((replay_children _).trans GeneralRebaseCompiledDisplay277.children).symm

theorem child_certificate (m : Assignment) (valid : Models after m) :
    Local family compiled after.core m displayChild 3 [] :=
  ⟨plan,List.mem_cons_of_mem _ (List.mem_singleton_self _),
    certificate_of_semantics (child_frame m valid) no_children.symm (holds m valid) (ready plan)
      (classes_empty (no_new_request displayChild) plan m)⟩

theorem witness (m : Assignment) (valid : Models after m) :
    Evidence family compiled after m displayRoot (.node 1 [.node 3 []]) := by
  apply GeneralDictionaryReadback.erased_evidence_node _ _ _ [displayChild] _
    (parent_certificate m valid)
  exact .cons (GeneralDictionaryReadback.erased_evidence_node _ _ _ [] [] (child_certificate m valid) .nil) .nil

theorem complete : Complete watch after compiled displayRoot (.node 1 [.node 3 []]) := by
  intro m hv
  exact ⟨family,fun {_} m => List.mem_append_right _ m,witness _ hv.1⟩

theorem exact_nonleaf (m : Assignment) :
    Query watch after compiled (interpret stored.kept m) displayRoot (.node 1 [.node 3 []]) ↔
    GeneralRebaseWholeJournal282.View after compiled displayRoot (.node 1 [.node 3 []]) m := by
  have cache : Cache after watch stored.kept := ⟨next_valid.covers,next_valid.sorted⟩
  exact GeneralRebaseWatchJoint284.certified cache GeneralRebaseCompiledFixtures282.Display.reached
    (fun {_} req => List.mem_append_left _ (List.mem_append_right _ req))
    compiled m displayRoot (.node 1 [.node 3 []]) complete

end Yulang.GeneralRebaseDisplayWatch284
