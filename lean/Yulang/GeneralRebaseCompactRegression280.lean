import Yulang.GeneralRebaseCompactSource280
import Yulang.GeneralRebaseFixedDisplayGraph280
import Yulang.GeneralDictionaryVersionLoopNontermination239
import Yulang.GeneralDictionaryLooseIterationNontermination240

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseCompactRegression280
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseCompactMachine280 (compact compact_related compactEffect CompactStep acc_exact)
open GeneralRebaseCompactSource280 (SourceCompact compact_initial)
open GeneralNominalCommonBridge (Assignment)

namespace Display
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (compiled after effect)
open GeneralRebaseDisplayStep276 (initial_source)
open GeneralRebaseFixedDisplayGraph280 (actual_edge_list)

theorem one_step (next : State roles) :
    SourceCompact registry displayRoot before next ↔ next = compact after := by
  constructor
  · rintro ⟨raw,go,rfl⟩
    rw [(GeneralRebaseCompiledAcc277.step_exact raw).mp go]
  · rintro rfl
    exact ⟨after,GeneralRebaseCompiledInstall277.adapter_step,rfl⟩

theorem no_next : ¬ ∃ out, SourceCompact registry displayRoot (compact after) out :=
  (GeneralRebaseCompactMachine280.terminal_iff (compact_related after)).mp
    GeneralRebaseCompiledStable277.stable_parent

theorem initial_acc : Acc (fun next prior => SourceCompact registry displayRoot prior next) before :=
  (GeneralRebaseCompactSource280.source_accessible initial_source).mp GeneralRebaseCompiledAcc277.adapter_acc

theorem evidenceAt : B4SkeletonV8.EvidenceAt (boundary roles) registry (compact after) displayRoot :=
  (GeneralRebaseCompactSource280.compact_EvidenceAt after).mp GeneralRebaseCompiledEvidenceAt277.evidenceAt

theorem payload (m : Assignment) (valid : Models (compact after) m) :
    (boundary roles).Evidence registry (compact after) m displayRoot (.node 1 [.node 3 []]) := by
  have old := (GeneralRebaseGraphBisim280.models (compact_related after) m).mpr valid
  exact (GeneralRebaseGraphBisim280.evidence (compact_related after) compiled displayRoot m _).mp
    (GeneralRebaseCompiledEvidence277.real_nonleaf m old)

theorem current_edge : (compact after).core.erased.current.edges = [(displayRoot,displayChild)] := by
  change GeneralRebaseEdgeLedger279.normalize after.core.erased.current.edges = _
  rw [actual_edge_list]
  exact GeneralRebaseEdgeLedger279.normalize_eq _ (by simp)

/-- Representation-only stress fixture, not a source trace. It tests that
the stored snapshot, not only the outer graph, really loses duplicates. -/
noncomputable def duplicateArchives : State roles :=
  GeneralRebaseArchiveTrust280.changeEffects after
    [GeneralRebaseEffectSnapshot280.retag effect [(displayRoot,displayChild),(displayRoot,displayChild)]]

theorem compact_archived_once :
    ((compact duplicateArchives).effects.map fun eff => eff.snapshot.erased.current.edges) =
    [[(displayRoot,displayChild)]] := by
  change [GeneralRebaseEdgeLedger279.normalize [(displayRoot,displayChild),(displayRoot,displayChild)]] = _
  congr 1

end Display

theorem old239_remains_nonaccessible :
    ¬ Acc (fun after before => CompactStep GeneralDictionaryVersionLoopSource237.registry
      GeneralDictionaryVersionLoopSource237.root before after)
      (compact GeneralDictionaryVersionLoopSource237.initial) := by
  intro h
  exact GeneralDictionaryVersionLoopNontermination239.initial_no_acc ((acc_exact _ _ _).mpr h)

theorem old240_remains_nonaccessible :
    ¬ Acc (fun after before => CompactStep GeneralDictionaryLooseLoopSource240.registry
      GeneralDictionaryLooseLoopSource240.root before after)
      (compact GeneralDictionaryLooseLoopSource240.initial) := by
  intro h
  exact GeneralDictionaryLooseIterationNontermination240.initial_no_acc
    (GeneralNominalPointErasure240.old_acc ((acc_exact _ _ _).mpr h))

end Yulang.GeneralRebaseCompactRegression280
